import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0241
import IrregularNine14P06C0242

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32100 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(0,5),(1,2),(3,5)], upper := (rows 11 50 164 268 21 99 67 195 323), lower := (rows 11 50 164 268 21 32 64 128 256), losses := [{ target := 5, region := (rows 3 2 4 24 16 0 67 131 259), good := (rows 459 475 132 268 477 0 64 128 256) }] }

theorem u32100 : Upper (D 6) (R 6) [10,48,160,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32101 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 164 268 22 97 65 193 321), lower := (rows 11 50 164 268 22 32 64 128 256), losses := [] }

theorem u32101 : Upper (D 6) (R 6) [10,48,160,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32102 : Route 9 := (fun mask => (mask,id))

def c32102 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32102 : Upper (D 6) (R 6) [10,48,160,260,65] 13 := by
  apply FastRouting.sound _ _ [10,48,160,260,65] 13 (by decide) (choices 1) [1,2,4,64] r32102 c32102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14461
  · exact u14462
  · exact u14463
  · exact u14464

def r32103 : Route 9 := (fun mask => (mask,id))

def c32103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32103 : Upper (D 6) (R 6) [10,48,160,260,66] 13 := by
  apply FastRouting.sound _ _ [10,48,160,260,66] 13 (by decide) (choices 1) [1,4,64] r32103 c32103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14465
  · exact u14466
  · exact u14467

def r32104 : Route 9 := (fun mask => (mask,id))

def c32104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32104 : Upper (D 6) (R 6) [10,48,160,260,68] 13 := by
  apply FastRouting.sound _ _ [10,48,160,260,68] 13 (by decide) (choices 1) [1,2,64] r32104 c32104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14468
  · exact u14469
  · exact u14470

def b32105 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 164 328 19 101 69 197 325), lower := (rows 11 50 164 328 19 32 64 128 256), losses := [] }

theorem u32105 : Upper (D 6) (R 6) [10,48,160,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32106 : Route 9 := (fun mask => (mask,id))

def c32106 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32106 : Upper (D 6) (R 6) [10,48,160,320,5] 13 := by
  apply FastRouting.sound _ _ [10,48,160,320,5] 13 (by decide) (choices 1) [1,2,4,64] r32106 c32106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14471
  · exact u14472
  · exact u14473
  · exact u14474

def b32107 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 164 328 22 101 69 197 325), lower := (rows 11 50 164 328 22 32 64 128 256), losses := [] }

theorem u32107 : Upper (D 6) (R 6) [10,48,160,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32108 : Route 9 := (fun mask => (mask,id))

def c32108 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32108 : Upper (D 6) (R 6) [10,48,160,320,65] 13 := by
  apply FastRouting.sound _ _ [10,48,160,320,65] 13 (by decide) (choices 1) [1,2,4] r32108 c32108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14475
  · exact u14476
  · exact u14477

def b32109 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 164, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 50 164 328 82 37 69 133 261), lower := (rows 11 50 164 328 82 32 64 128 256), losses := [] }

theorem u32109 : Upper (D 6) (R 6) [10,48,160,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32110 : Route 9 := (fun mask => (mask,id))

def c32110 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32110 : Upper (D 6) (R 6) [10,48,160,320,68] 13 := by
  apply FastRouting.sound _ _ [10,48,160,320,68] 13 (by decide) (choices 1) [1,2,4] r32110 c32110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14478
  · exact u14479
  · exact u14480

def b32111 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 196 13 19 356 356 484 356), lower := (rows 11 50 196 13 19 32 64 128 256), losses := [] }

theorem u32111 : Upper (D 6) (R 6) [10,48,192,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32112 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 196 13 21 354 354 482 354), lower := (rows 11 50 196 13 21 32 64 128 256), losses := [] }

theorem u32112 : Upper (D 6) (R 6) [10,48,192,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32113 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 50 196 13 22 353 353 481 353), lower := (rows 11 50 196 13 22 32 64 128 256), losses := [] }

theorem u32113 : Upper (D 6) (R 6) [10,48,192,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32114 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 13 49 358 326 454 326), lower := (rows 11 50 196 13 49 32 64 128 256), losses := [] }

theorem u32114 : Upper (D 6) (R 6) [10,48,192,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32115 : PairBound 9 := { available := 325, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 196 13 50 357 325 453 325), lower := (rows 11 50 196 13 50 32 64 128 256), losses := [] }

theorem u32115 : Upper (D 6) (R 6) [10,48,192,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32116 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 13 52 355 323 451 323), lower := (rows 11 50 196 13 52 32 64 128 256), losses := [] }

theorem u32116 : Upper (D 6) (R 6) [10,48,192,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32117 : Route 9 := (fun mask => (mask,id))

def c32117 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32117 : Upper (D 6) (R 6) [10,48,192,5,65] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,65] 13 (by decide) (choices 1) [2,4,256] r32117 c32117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14481
  · exact u14482
  · exact u14483

def r32118 : Route 9 := (fun mask => (mask,id))

def c32118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32118 : Upper (D 6) (R 6) [10,48,192,5,66] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,66] 13 (by decide) (choices 1) [1,4,256] r32118 c32118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14484
  · exact u14485
  · exact u14486

def b32119 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 196 13 84 291 355 419 291), lower := (rows 11 50 196 13 84 32 64 128 256), losses := [] }

theorem u32119 : Upper (D 6) (R 6) [10,48,192,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32120 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 13 112 295 327 391 263), lower := (rows 11 50 196 13 112 32 64 128 256), losses := [] }

theorem u32120 : Upper (D 6) (R 6) [10,48,192,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32121 : Route 9 := (fun mask => (mask,id))

def c32121 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32121 : Upper (D 6) (R 6) [10,48,192,5,257] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,257] 13 (by decide) (choices 1) [2,4,64] r32121 c32121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14487
  · exact u14488
  · exact u14489

def r32122 : Route 9 := (fun mask => (mask,id))

def c32122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32122 : Upper (D 6) (R 6) [10,48,192,5,258] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,258] 13 (by decide) (choices 1) [1,4,64] r32122 c32122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14490
  · exact u14491
  · exact u14492

def r32123 : Route 9 := (fun mask => (mask,id))

def c32123 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32123 : Upper (D 6) (R 6) [10,48,192,5,260] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,260] 13 (by decide) (choices 1) [1,2,64] r32123 c32123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14493
  · exact u14494
  · exact u14495

def b32124 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 13 304 103 71 199 327), lower := (rows 11 50 196 13 304 32 64 128 256), losses := [] }

theorem u32124 : Upper (D 6) (R 6) [10,48,192,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32125 : Route 9 := (fun mask => (mask,id))

def c32125 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32125 : Upper (D 6) (R 6) [10,48,192,5,320] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,320] 13 (by decide) (choices 1) [1,2,4] r32125 c32125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14496
  · exact u14497
  · exact u14498

def b32126 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 196 44 19 357 325 453 325), lower := (rows 11 50 196 44 19 32 64 128 256), losses := [] }

theorem u32126 : Upper (D 6) (R 6) [10,48,192,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32127 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 196 44 21 355 323 451 323), lower := (rows 11 50 196 44 21 32 64 128 256), losses := [] }

theorem u32127 : Upper (D 6) (R 6) [10,48,192,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32128 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 196 44 22 353 321 449 321), lower := (rows 11 50 196 44 22 32 64 128 256), losses := [] }

theorem u32128 : Upper (D 6) (R 6) [10,48,192,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32129 : Route 9 := (fun mask => (mask,id))

def c32129 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32129 : Upper (D 6) (R 6) [10,48,192,36,65] 13 := by
  apply FastRouting.sound _ _ [10,48,192,36,65] 13 (by decide) (choices 1) [1,2,4,256] r32129 c32129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14499
  · exact u14500
  · exact u14501
  · exact u14502

def b32130 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 196 44 82 293 325 389 261), lower := (rows 11 50 196 44 82 32 64 128 256), losses := [] }

theorem u32130 : Upper (D 6) (R 6) [10,48,192,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32131 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 196 44 84 291 323 387 259), lower := (rows 11 50 196 44 84 32 64 128 256), losses := [] }

theorem u32131 : Upper (D 6) (R 6) [10,48,192,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32132 : Route 9 := (fun mask => (mask,id))

def c32132 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32132 : Upper (D 6) (R 6) [10,48,192,36,257] 13 := by
  apply FastRouting.sound _ _ [10,48,192,36,257] 13 (by decide) (choices 1) [1,2,4,64] r32132 c32132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14503
  · exact u14504
  · exact u14505
  · exact u14506

def b32133 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 196 44 274 101 69 197 325), lower := (rows 11 50 196 44 274 32 64 128 256), losses := [] }

theorem u32133 : Upper (D 6) (R 6) [10,48,192,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32134 : Route 9 := (fun mask => (mask,id))

def c32134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32134 : Upper (D 6) (R 6) [10,48,192,36,260] 13 := by
  apply FastRouting.sound _ _ [10,48,192,36,260] 13 (by decide) (choices 1) [1,2,64] r32134 c32134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14507
  · exact u14508
  · exact u14509

def r32135 : Route 9 := (fun mask => (mask,id))

def c32135 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32135 : Upper (D 6) (R 6) [10,48,192,36,320] 13 := by
  apply FastRouting.sound _ _ [10,48,192,36,320] 13 (by decide) (choices 1) [1,2,4] r32135 c32135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14510
  · exact u14511
  · exact u14512

def b32136 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 196 73 19 292 356 420 292), lower := (rows 11 50 196 73 19 32 64 128 256), losses := [] }

theorem u32136 : Upper (D 6) (R 6) [10,48,192,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32137 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 50 196 73 21 294 358 422 294), lower := (rows 11 50 196 73 21 32 64 128 256), losses := [] }

theorem u32137 : Upper (D 6) (R 6) [10,48,192,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32138 : Route 9 := (fun mask => (mask,id))

def c32138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32138 : Upper (D 6) (R 6) [10,48,192,65,6] 13 := by
  apply FastRouting.sound _ _ [10,48,192,65,6] 13 (by decide) (choices 1) [1,4,256] r32138 c32138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14513
  · exact u14514
  · exact u14515

def b32139 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 73 49 294 326 390 262), lower := (rows 11 50 196 73 49 32 64 128 256), losses := [] }

theorem u32139 : Upper (D 6) (R 6) [10,48,192,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32140 : PairBound 9 := { available := 261, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 196 73 50 293 325 389 261), lower := (rows 11 50 196 73 50 32 64 128 256), losses := [] }

theorem u32140 : Upper (D 6) (R 6) [10,48,192,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32141 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 73 52 295 327 391 263), lower := (rows 11 50 196 73 52 32 64 128 256), losses := [] }

theorem u32141 : Upper (D 6) (R 6) [10,48,192,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32142 : Route 9 := (fun mask => (mask,id))

def c32142 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32142 : Upper (D 6) (R 6) [10,48,192,65,257] 13 := by
  apply FastRouting.sound _ _ [10,48,192,65,257] 13 (by decide) (choices 1) [2,4] r32142 c32142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14516
  · exact u14517

def r32143 : Route 9 := (fun mask => (mask,id))

def c32143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32143 : Upper (D 6) (R 6) [10,48,192,65,258] 13 := by
  apply FastRouting.sound _ _ [10,48,192,65,258] 13 (by decide) (choices 1) [1,4] r32143 c32143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14518
  · exact u14519

def r32144 : Route 9 := (fun mask => (mask,id))

def c32144 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32144 : Upper (D 6) (R 6) [10,48,192,65,260] 13 := by
  apply FastRouting.sound _ _ [10,48,192,65,260] 13 (by decide) (choices 1) [1,2,4] r32144 c32144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14520
  · exact u14521
  · exact u14522

def b32145 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 73 304 39 71 135 263), lower := (rows 11 50 196 73 304 32 64 128 256), losses := [] }

theorem u32145 : Upper (D 6) (R 6) [10,48,192,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32146 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 196 104 19 293 325 389 261), lower := (rows 11 50 196 104 19 32 64 128 256), losses := [] }

theorem u32146 : Upper (D 6) (R 6) [10,48,192,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32147 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 50 196 104 21 295 327 391 263), lower := (rows 11 50 196 104 21 32 64 128 256), losses := [] }

theorem u32147 : Upper (D 6) (R 6) [10,48,192,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32148 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 196 104 22 293 325 389 261), lower := (rows 11 50 196 104 22 32 64 128 256), losses := [] }

theorem u32148 : Upper (D 6) (R 6) [10,48,192,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32149 : Route 9 := (fun mask => (mask,id))

def c32149 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32149 : Upper (D 6) (R 6) [10,48,192,96,257] 13 := by
  apply FastRouting.sound _ _ [10,48,192,96,257] 13 (by decide) (choices 1) [1,2,4] r32149 c32149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14523
  · exact u14524
  · exact u14525

def b32150 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 196 104 274 37 69 133 261), lower := (rows 11 50 196 104 274 32 64 128 256), losses := [] }

theorem u32150 : Upper (D 6) (R 6) [10,48,192,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32151 : Route 9 := (fun mask => (mask,id))

def c32151 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32151 : Upper (D 6) (R 6) [10,48,192,96,260] 13 := by
  apply FastRouting.sound _ _ [10,48,192,96,260] 13 (by decide) (choices 1) [1,2,4] r32151 c32151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14526
  · exact u14527
  · exact u14528

def b32152 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 196 265 19 100 100 228 356), lower := (rows 11 50 196 265 19 32 64 128 256), losses := [] }

theorem u32152 : Upper (D 6) (R 6) [10,48,192,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32153 : Route 9 := (fun mask => (mask,id))

def c32153 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32153 : Upper (D 6) (R 6) [10,48,192,257,5] 13 := by
  apply FastRouting.sound _ _ [10,48,192,257,5] 13 (by decide) (choices 1) [2,4,64] r32153 c32153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14529
  · exact u14530
  · exact u14531

def r32154 : Route 9 := (fun mask => (mask,id))

def c32154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32154 : Upper (D 6) (R 6) [10,48,192,257,6] 13 := by
  apply FastRouting.sound _ _ [10,48,192,257,6] 13 (by decide) (choices 1) [1,4,64] r32154 c32154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14532
  · exact u14533
  · exact u14534

def b32155 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 265 49 102 70 198 326), lower := (rows 11 50 196 265 49 32 64 128 256), losses := [] }

theorem u32155 : Upper (D 6) (R 6) [10,48,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32156 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 196 265 50 101 69 197 325), lower := (rows 11 50 196 265 50 32 64 128 256), losses := [] }

theorem u32156 : Upper (D 6) (R 6) [10,48,192,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32157 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 265 52 103 71 199 327), lower := (rows 11 50 196 265 52 32 64 128 256), losses := [] }

theorem u32157 : Upper (D 6) (R 6) [10,48,192,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32158 : Route 9 := (fun mask => (mask,id))

def c32158 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32158 : Upper (D 6) (R 6) [10,48,192,257,65] 13 := by
  apply FastRouting.sound _ _ [10,48,192,257,65] 13 (by decide) (choices 1) [2,4] r32158 c32158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14535
  · exact u14536

def r32159 : Route 9 := (fun mask => (mask,id))

def c32159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32159 : Upper (D 6) (R 6) [10,48,192,257,66] 13 := by
  apply FastRouting.sound _ _ [10,48,192,257,66] 13 (by decide) (choices 1) [1,4] r32159 c32159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14537
  · exact u14538

#print axioms u32159
end Delivery.IrregularNine14.P06
