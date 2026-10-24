import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0223
import IrregularNine14P07C0224
import IrregularNine14P07C0225

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31080 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 42 196 265 19 240 240 240 496), lower := (rows 7 42 196 265 19 32 64 128 256), losses := [] }

theorem u31080 : Upper (D 7) (R 7) [6,40,192,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31081 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31081 : Upper (D 7) (R 7) [6,40,192,257,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,33] 13 (by decide) (choices 1) [2,16,64] r31081 c31081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13417
  · exact u13418
  · exact u13419

def b31082 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 196 265 50 241 209 209 465), lower := (rows 7 42 196 265 50 32 64 128 256), losses := [] }

theorem u31082 : Upper (D 7) (R 7) [6,40,192,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31083 : Route 9 := (fun mask => (mask,id))

def c31083 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31083 : Upper (D 7) (R 7) [6,40,192,257,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,65] 13 (by decide) (choices 1) [2,16,128] r31083 c31083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13420
  · exact u13421
  · exact u13422

def r31084 : Route 9 := (fun mask => (mask,id))

def c31084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31084 : Upper (D 7) (R 7) [6,40,192,257,66] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,66] 13 (by decide) (choices 1) [1,16,128] r31084 c31084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13423
  · exact u13424
  · exact u13425

def r31085 : Route 9 := (fun mask => (mask,id))

def c31085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31085 : Upper (D 7) (R 7) [6,40,192,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,96] 13 (by decide) (choices 1) [1,2,16,128] r31085 c31085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13426
  · exact u13427
  · exact u13428
  · exact u13429

def b31086 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 196 265 208 51 115 179 307), lower := (rows 7 42 196 265 208 32 64 128 256), losses := [] }

theorem u31086 : Upper (D 7) (R 7) [6,40,192,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31087 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31087 : Upper (D 7) (R 7) [6,40,192,258,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,33] 13 (by decide) (choices 1) [1,16,64] r31087 c31087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13430
  · exact u13431
  · exact u13432

def b31088 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 196 266 81 177 241 177 433), lower := (rows 7 42 196 266 81 32 64 128 256), losses := [] }

theorem u31088 : Upper (D 7) (R 7) [6,40,192,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31089 : Route 9 := (fun mask => (mask,id))

def c31089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31089 : Upper (D 7) (R 7) [6,40,192,258,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,96] 13 (by decide) (choices 1) [1,16,128] r31089 c31089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13433
  · exact u13434
  · exact u13435

def b31090 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 196 266 208 49 113 177 305), lower := (rows 7 42 196 266 208 32 64 128 256), losses := [] }

theorem u31090 : Upper (D 7) (R 7) [6,40,192,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31091 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 42 196 280 19 225 225 225 481), lower := (rows 7 42 196 280 19 32 64 128 256), losses := [] }

theorem u31091 : Upper (D 7) (R 7) [6,40,192,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31092 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31092 : Upper (D 7) (R 7) [6,40,192,272,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,33] 13 (by decide) (choices 1) [1,2,64] r31092 c31092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13436
  · exact u13437
  · exact u13438

def b31093 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 196 280 50 225 193 193 449), lower := (rows 7 42 196 280 50 32 64 128 256), losses := [] }

theorem u31093 : Upper (D 7) (R 7) [6,40,192,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31094 : Route 9 := (fun mask => (mask,id))

def c31094 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31094 : Upper (D 7) (R 7) [6,40,192,272,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,65] 13 (by decide) (choices 1) [1,2,128] r31094 c31094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13439
  · exact u13440
  · exact u13441

def r31095 : Route 9 := (fun mask => (mask,id))

def c31095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31095 : Upper (D 7) (R 7) [6,40,192,272,66] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,66] 13 (by decide) (choices 1) [1,128] r31095 c31095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13442
  · exact u13443

def r31096 : Route 9 := (fun mask => (mask,id))

def c31096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31096 : Upper (D 7) (R 7) [6,40,192,272,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,96] 13 (by decide) (choices 1) [1,2,128] r31096 c31096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13444
  · exact u13445
  · exact u13446

def b31097 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 196 280 208 35 99 163 291), lower := (rows 7 42 196 280 208 32 64 128 256), losses := [] }

theorem u31097 : Upper (D 7) (R 7) [6,40,192,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31098 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 42 196 328 19 177 241 177 433), lower := (rows 7 42 196 328 19 32 64 128 256), losses := [] }

theorem u31098 : Upper (D 7) (R 7) [6,40,192,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31099 : Route 9 := (fun mask => (mask,id))

def c31099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31099 : Upper (D 7) (R 7) [6,40,192,320,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,33] 13 (by decide) (choices 1) [1,2,16,128] r31099 c31099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13447
  · exact u13448
  · exact u13449
  · exact u13450

def b31100 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 196 328 50 177 209 145 401), lower := (rows 7 42 196 328 50 32 64 128 256), losses := [] }

theorem u31100 : Upper (D 7) (R 7) [6,40,192,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31101 : Route 9 := (fun mask => (mask,id))

def c31101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31101 : Upper (D 7) (R 7) [6,40,192,320,129] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,129] 13 (by decide) (choices 1) [1,2,16] r31101 c31101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13451
  · exact u13452
  · exact u13453

def r31102 : Route 9 := (fun mask => (mask,id))

def c31102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31102 : Upper (D 7) (R 7) [6,40,192,320,130] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,130] 13 (by decide) (choices 1) [1,16] r31102 c31102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13454
  · exact u13455

def r31103 : Route 9 := (fun mask => (mask,id))

def c31103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31103 : Upper (D 7) (R 7) [6,40,192,320,160] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,160] 13 (by decide) (choices 1) [1,2,16] r31103 c31103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13456
  · exact u13457
  · exact u13458

def b31104 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 16, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 42 261 25 50 224 192 192 448), lower := (rows 7 42 261 25 50 32 64 128 256), losses := [] }

theorem u31104 : Upper (D 7) (R 7) [6,40,257,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31105 : Route 9 := (fun mask => (mask,id))

def c31105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31105 : Upper (D 7) (R 7) [6,40,257,17,66] 13 := by
  apply FastRouting.sound _ _ [6,40,257,17,66] 13 (by decide) (choices 1) [64,128] r31105 c31105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13459
  · exact u13460

def b31106 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,0)], upper := (rows 7 42 261 25 112 226 194 194 450), lower := (rows 7 42 261 25 112 32 64 128 256), losses := [] }

theorem u31106 : Upper (D 7) (R 7) [6,40,257,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31107 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31107 : Upper (D 7) (R 7) [6,40,257,17,192] 13 := by
  apply FastRouting.sound _ _ [6,40,257,17,192] 13 (by decide) (choices 1) [2,64] r31107 c31107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13461
  · exact u13462

def b31108 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 10, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 42 261 26 49 224 192 192 448), lower := (rows 7 42 261 26 49 32 64 128 256), losses := [] }

theorem u31108 : Upper (D 7) (R 7) [6,40,257,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31109 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 261 26 81 224 224 224 480), lower := (rows 7 42 261 26 81 32 64 128 256), losses := [] }

theorem u31109 : Upper (D 7) (R 7) [6,40,257,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31110 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 261 26 112 225 193 193 449), lower := (rows 7 42 261 26 112 32 64 128 256), losses := [] }

theorem u31110 : Upper (D 7) (R 7) [6,40,257,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31111 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31111 : Upper (D 7) (R 7) [6,40,257,18,192] 13 := by
  apply FastRouting.sound _ _ [6,40,257,18,192] 13 (by decide) (choices 1) [1,64] r31111 c31111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13463
  · exact u13464

def b31112 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 16, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 42 261 73 50 240 208 208 464), lower := (rows 7 42 261 73 50 32 64 128 256), losses := [] }

theorem u31112 : Upper (D 7) (R 7) [6,40,257,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31113 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 7 42 261 73 82 176 240 176 432), lower := (rows 7 42 261 73 82 32 64 128 256), losses := [] }

theorem u31113 : Upper (D 7) (R 7) [6,40,257,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31114 : Route 9 := (fun mask => (mask,id))

def c31114 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31114 : Upper (D 7) (R 7) [6,40,257,65,96] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,96] 13 (by decide) (choices 1) [2,16,128] r31114 c31114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13465
  · exact u13466
  · exact u13467

def r31115 : Route 9 := (fun mask => (mask,id))

def c31115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31115 : Upper (D 7) (R 7) [6,40,257,65,130] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,130] 13 (by decide) (choices 1) [16,64,128] r31115 c31115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13468
  · exact u13469
  · exact u13470

def r31116 : Route 9 := (fun mask => (mask,id))

def c31116 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31116 : Upper (D 7) (R 7) [6,40,257,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,160] 13 (by decide) (choices 1) [2,16,64,128] r31116 c31116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13471
  · exact u13472
  · exact u13473
  · exact u13474

def r31117 : Route 9 := (fun mask => (mask,id))

def c31117 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31117 : Upper (D 7) (R 7) [6,40,257,65,192] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,192] 13 (by decide) (choices 1) [2,16,128] r31117 c31117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13475
  · exact u13476
  · exact u13477

def b31118 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 261 74 49 240 208 208 464), lower := (rows 7 42 261 74 49 32 64 128 256), losses := [] }

theorem u31118 : Upper (D 7) (R 7) [6,40,257,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31119 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 261 74 81 176 240 176 432), lower := (rows 7 42 261 74 81 32 64 128 256), losses := [] }

theorem u31119 : Upper (D 7) (R 7) [6,40,257,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31120 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 261 74 112 177 209 145 401), lower := (rows 7 42 261 74 112 32 64 128 256), losses := [] }

theorem u31120 : Upper (D 7) (R 7) [6,40,257,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31121 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 261 74 145 240 240 240 496), lower := (rows 7 42 261 74 145 32 64 128 256), losses := [] }

theorem u31121 : Upper (D 7) (R 7) [6,40,257,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31122 : Route 9 := (fun mask => (mask,id))

def c31122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31122 : Upper (D 7) (R 7) [6,40,257,66,160] 13 := by
  apply FastRouting.sound _ _ [6,40,257,66,160] 13 (by decide) (choices 1) [1,16,64,128] r31122 c31122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13478
  · exact u13479
  · exact u13480
  · exact u13481

def r31123 : Route 9 := (fun mask => (mask,id))

def c31123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31123 : Upper (D 7) (R 7) [6,40,257,66,192] 13 := by
  apply FastRouting.sound _ _ [6,40,257,66,192] 13 (by decide) (choices 1) [1,16,128] r31123 c31123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13482
  · exact u13483
  · exact u13484

def b31124 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 42 261 88 19 224 224 224 480), lower := (rows 7 42 261 88 19 32 64 128 256), losses := [] }

theorem u31124 : Upper (D 7) (R 7) [6,40,257,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31125 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 4, region := 202, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,0)], upper := (rows 7 42 261 88 49 226 194 194 450), lower := (rows 7 42 261 88 49 32 64 128 256), losses := [] }

theorem u31125 : Upper (D 7) (R 7) [6,40,257,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31126 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 261 88 50 225 193 193 449), lower := (rows 7 42 261 88 50 32 64 128 256), losses := [] }

theorem u31126 : Upper (D 7) (R 7) [6,40,257,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31127 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,6),(1,6),(2,6),(3,1)], upper := (rows 7 42 261 88 81 162 226 162 418), lower := (rows 7 42 261 88 81 32 64 128 256), losses := [] }

theorem u31127 : Upper (D 7) (R 7) [6,40,257,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31128 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 261 88 82 161 225 161 417), lower := (rows 7 42 261 88 82 32 64 128 256), losses := [] }

theorem u31128 : Upper (D 7) (R 7) [6,40,257,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31129 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 261 88 112 163 195 131 387), lower := (rows 7 42 261 88 112 32 64 128 256), losses := [] }

theorem u31129 : Upper (D 7) (R 7) [6,40,257,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31130 : Route 9 := (fun mask => (mask,id))

def c31130 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31130 : Upper (D 7) (R 7) [6,40,257,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,257,80,129] 13 (by decide) (choices 1) [2,64,128] r31130 c31130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13485
  · exact u13486
  · exact u13487

def r31131 : Route 9 := (fun mask => (mask,id))

def c31131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31131 : Upper (D 7) (R 7) [6,40,257,80,130] 13 := by
  apply FastRouting.sound _ _ [6,40,257,80,130] 13 (by decide) (choices 1) [1,64,128] r31131 c31131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13488
  · exact u13489
  · exact u13490

def r31132 : Route 9 := (fun mask => (mask,id))

def c31132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31132 : Upper (D 7) (R 7) [6,40,257,80,160] 13 := by
  apply FastRouting.sound _ _ [6,40,257,80,160] 13 (by decide) (choices 1) [1,2,64,128] r31132 c31132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13491
  · exact u13492
  · exact u13493
  · exact u13494

def b31133 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 261 88 208 163 227 163 419), lower := (rows 7 42 261 88 208 32 64 128 256), losses := [] }

theorem u31133 : Upper (D 7) (R 7) [6,40,257,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31134 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 42 261 200 19 240 240 240 496), lower := (rows 7 42 261 200 19 32 64 128 256), losses := [] }

theorem u31134 : Upper (D 7) (R 7) [6,40,257,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31135 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31135 : Upper (D 7) (R 7) [6,40,257,192,33] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192,33] 13 (by decide) (choices 1) [2,16,64] r31135 c31135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13495
  · exact u13496
  · exact u13497

def b31136 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 261 200 50 241 209 209 465), lower := (rows 7 42 261 200 50 32 64 128 256), losses := [] }

theorem u31136 : Upper (D 7) (R 7) [6,40,257,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31137 : Route 9 := (fun mask => (mask,id))

def c31137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31137 : Upper (D 7) (R 7) [6,40,257,192,65] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192,65] 13 (by decide) (choices 1) [2,16,128] r31137 c31137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13498
  · exact u13499
  · exact u13500

def r31138 : Route 9 := (fun mask => (mask,id))

def c31138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31138 : Upper (D 7) (R 7) [6,40,257,192,66] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192,66] 13 (by decide) (choices 1) [1,16,128] r31138 c31138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13501
  · exact u13502
  · exact u13503

def r31139 : Route 9 := (fun mask => (mask,id))

def c31139 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31139 : Upper (D 7) (R 7) [6,40,257,192,96] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192,96] 13 (by decide) (choices 1) [1,2,16,128] r31139 c31139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13504
  · exact u13505
  · exact u13506
  · exact u13507

#print axioms u31139
end Delivery.IrregularNine14.P07
