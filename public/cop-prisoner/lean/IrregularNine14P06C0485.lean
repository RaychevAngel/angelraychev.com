import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0174
import IrregularNine14P06C0175

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29100 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 164 25 274 101 69 197 325), lower := (rows 7 42 164 25 274 32 64 128 256), losses := [] }

theorem u29100 : Upper (D 6) (R 6) [6,40,160,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29100
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29101 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 42 164 25 276 99 67 195 323), lower := (rows 7 42 164 25 276 32 64 128 256), losses := [] }

theorem u29101 : Upper (D 6) (R 6) [6,40,160,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29101
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29102 : Route 9 := (fun mask => (mask,id))

def c29102 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29102 : Upper (D 6) (R 6) [6,40,160,17,320] 13 := by
  apply FastRouting.sound _ _ [6,40,160,17,320] 13 (by decide) (choices 1) [1,2,4,64] r29102 c29102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10456
  · exact u10457
  · exact u10458
  · exact u10459

def b29103 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,2),(4,6)], upper := (rows 7 42 164 73 19 372 340 468 340), lower := (rows 7 42 164 73 19 32 64 128 256), losses := [] }

theorem u29103 : Upper (D 6) (R 6) [6,40,160,65,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29103
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29104 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 164 73 21 370 338 466 338), lower := (rows 7 42 164 73 21 32 64 128 256), losses := [] }

theorem u29104 : Upper (D 6) (R 6) [6,40,160,65,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29104
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29105 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 16, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 164 73 22 369 337 465 337), lower := (rows 7 42 164 73 22 32 64 128 256), losses := [] }

theorem u29105 : Upper (D 6) (R 6) [6,40,160,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29105
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29106 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 7 42 164 73 81 310 342 406 278), lower := (rows 7 42 164 73 81 32 64 128 256), losses := [] }

theorem u29106 : Upper (D 6) (R 6) [6,40,160,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29106
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29107 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 42 164 73 82 309 341 405 277), lower := (rows 7 42 164 73 82 32 64 128 256), losses := [] }

theorem u29107 : Upper (D 6) (R 6) [6,40,160,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29107
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29108 : Route 9 := (fun mask => (mask,id))

def c29108 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29108 : Upper (D 6) (R 6) [6,40,160,65,68] 13 := by
  apply FastRouting.sound _ _ [6,40,160,65,68] 13 (by decide) (choices 1) [1,2,16,256] r29108 c29108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10460
  · exact u10461
  · exact u10462
  · exact u10463

def r29109 : Route 9 := (fun mask => (mask,id))

def c29109 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29109 : Upper (D 6) (R 6) [6,40,160,65,257] 13 := by
  apply FastRouting.sound _ _ [6,40,160,65,257] 13 (by decide) (choices 1) [2,4,16,64] r29109 c29109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10464
  · exact u10465
  · exact u10466
  · exact u10467

def r29110 : Route 9 := (fun mask => (mask,id))

def c29110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29110 : Upper (D 6) (R 6) [6,40,160,65,258] 13 := by
  apply FastRouting.sound _ _ [6,40,160,65,258] 13 (by decide) (choices 1) [1,4,16,64] r29110 c29110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10468
  · exact u10469
  · exact u10470
  · exact u10471

def r29111 : Route 9 := (fun mask => (mask,id))

def c29111 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29111 : Upper (D 6) (R 6) [6,40,160,65,260] 13 := by
  apply FastRouting.sound _ _ [6,40,160,65,260] 13 (by decide) (choices 1) [1,2,16,64] r29111 c29111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10472
  · exact u10473
  · exact u10474
  · exact u10475

def r29112 : Route 9 := (fun mask => (mask,id))

def c29112 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29112 : Upper (D 6) (R 6) [6,40,160,65,320] 13 := by
  apply FastRouting.sound _ _ [6,40,160,65,320] 13 (by decide) (choices 1) [1,2,4,16] r29112 c29112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10476
  · exact u10477
  · exact u10478
  · exact u10479

def b29113 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,2),(4,6)], upper := (rows 7 42 164 88 19 357 325 453 325), lower := (rows 7 42 164 88 19 32 64 128 256), losses := [] }

theorem u29113 : Upper (D 6) (R 6) [6,40,160,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29113
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29114 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 164 88 21 355 323 451 323), lower := (rows 7 42 164 88 21 32 64 128 256), losses := [] }

theorem u29114 : Upper (D 6) (R 6) [6,40,160,80,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29114
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29115 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 16, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 164 88 22 353 321 449 321), lower := (rows 7 42 164 88 22 32 64 128 256), losses := [] }

theorem u29115 : Upper (D 6) (R 6) [6,40,160,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29115
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29116 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 164 88 81 295 327 391 263), lower := (rows 7 42 164 88 81 32 64 128 256), losses := [] }

theorem u29116 : Upper (D 6) (R 6) [6,40,160,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29116
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29117 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 164 88 82 293 325 389 261), lower := (rows 7 42 164 88 82 32 64 128 256), losses := [] }

theorem u29117 : Upper (D 6) (R 6) [6,40,160,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29117
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29118 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 164 88 84 291 323 387 259), lower := (rows 7 42 164 88 84 32 64 128 256), losses := [] }

theorem u29118 : Upper (D 6) (R 6) [6,40,160,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29118
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29119 : Route 9 := (fun mask => (mask,id))

def c29119 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29119 : Upper (D 6) (R 6) [6,40,160,80,257] 13 := by
  apply FastRouting.sound _ _ [6,40,160,80,257] 13 (by decide) (choices 1) [1,2,4,64] r29119 c29119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10480
  · exact u10481
  · exact u10482
  · exact u10483

def b29120 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 164 88 274 101 69 197 325), lower := (rows 7 42 164 88 274 32 64 128 256), losses := [] }

theorem u29120 : Upper (D 6) (R 6) [6,40,160,80,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29120
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29121 : Route 9 := (fun mask => (mask,id))

def c29121 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29121 : Upper (D 6) (R 6) [6,40,160,80,260] 13 := by
  apply FastRouting.sound _ _ [6,40,160,80,260] 13 (by decide) (choices 1) [1,2,64] r29121 c29121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10484
  · exact u10485
  · exact u10486

def b29122 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 164 88 336 39 71 135 263), lower := (rows 7 42 164 88 336 32 64 128 256), losses := [] }

theorem u29122 : Upper (D 6) (R 6) [6,40,160,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29122
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29123 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,2),(4,6)], upper := (rows 7 42 164 265 19 116 84 212 340), lower := (rows 7 42 164 265 19 32 64 128 256), losses := [] }

theorem u29123 : Upper (D 6) (R 6) [6,40,160,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29123
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29124 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 164 265 21 114 82 210 338), lower := (rows 7 42 164 265 21 32 64 128 256), losses := [] }

theorem u29124 : Upper (D 6) (R 6) [6,40,160,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29124
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29125 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 16, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 164 265 22 113 81 209 337), lower := (rows 7 42 164 265 22 32 64 128 256), losses := [] }

theorem u29125 : Upper (D 6) (R 6) [6,40,160,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29125
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29126 : Route 9 := (fun mask => (mask,id))

def c29126 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29126 : Upper (D 6) (R 6) [6,40,160,257,65] 13 := by
  apply FastRouting.sound _ _ [6,40,160,257,65] 13 (by decide) (choices 1) [2,4,16,64] r29126 c29126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10487
  · exact u10488
  · exact u10489
  · exact u10490

def r29127 : Route 9 := (fun mask => (mask,id))

def c29127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29127 : Upper (D 6) (R 6) [6,40,160,257,66] 13 := by
  apply FastRouting.sound _ _ [6,40,160,257,66] 13 (by decide) (choices 1) [1,4,16,64] r29127 c29127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10491
  · exact u10492
  · exact u10493
  · exact u10494

def r29128 : Route 9 := (fun mask => (mask,id))

def c29128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29128 : Upper (D 6) (R 6) [6,40,160,257,68] 13 := by
  apply FastRouting.sound _ _ [6,40,160,257,68] 13 (by decide) (choices 1) [1,2,16,64] r29128 c29128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10495
  · exact u10496
  · exact u10497
  · exact u10498

def b29129 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,2),(4,6)], upper := (rows 7 42 164 280 19 101 69 197 325), lower := (rows 7 42 164 280 19 32 64 128 256), losses := [] }

theorem u29129 : Upper (D 6) (R 6) [6,40,160,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29129
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29130 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 164 280 21 99 67 195 323), lower := (rows 7 42 164 280 21 32 64 128 256), losses := [] }

theorem u29130 : Upper (D 6) (R 6) [6,40,160,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29130
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29131 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 16, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 164 280 22 97 65 193 321), lower := (rows 7 42 164 280 22 32 64 128 256), losses := [] }

theorem u29131 : Upper (D 6) (R 6) [6,40,160,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29131
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29132 : Route 9 := (fun mask => (mask,id))

def c29132 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29132 : Upper (D 6) (R 6) [6,40,160,272,65] 13 := by
  apply FastRouting.sound _ _ [6,40,160,272,65] 13 (by decide) (choices 1) [1,2,4,64] r29132 c29132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10499
  · exact u10500
  · exact u10501
  · exact u10502

def b29133 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 164 280 82 101 69 197 325), lower := (rows 7 42 164 280 82 32 64 128 256), losses := [] }

theorem u29133 : Upper (D 6) (R 6) [6,40,160,272,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29133
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29134 : Route 9 := (fun mask => (mask,id))

def c29134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29134 : Upper (D 6) (R 6) [6,40,160,272,68] 13 := by
  apply FastRouting.sound _ _ [6,40,160,272,68] 13 (by decide) (choices 1) [1,2,64] r29134 c29134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10503
  · exact u10504
  · exact u10505

def b29135 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,2),(4,6)], upper := (rows 7 42 164 328 19 117 85 213 341), lower := (rows 7 42 164 328 19 32 64 128 256), losses := [] }

theorem u29135 : Upper (D 6) (R 6) [6,40,160,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29135
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29136 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 164 328 21 115 83 211 339), lower := (rows 7 42 164 328 21 32 64 128 256), losses := [] }

theorem u29136 : Upper (D 6) (R 6) [6,40,160,320,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29136
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29137 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 16, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 164 328 22 113 81 209 337), lower := (rows 7 42 164 328 22 32 64 128 256), losses := [] }

theorem u29137 : Upper (D 6) (R 6) [6,40,160,320,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29137
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29138 : Route 9 := (fun mask => (mask,id))

def c29138 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29138 : Upper (D 6) (R 6) [6,40,160,320,65] 13 := by
  apply FastRouting.sound _ _ [6,40,160,320,65] 13 (by decide) (choices 1) [1,2,4,16] r29138 c29138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10506
  · exact u10507
  · exact u10508
  · exact u10509

def b29139 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 42 164 328 82 53 85 149 277), lower := (rows 7 42 164 328 82 32 64 128 256), losses := [] }

theorem u29139 : Upper (D 6) (R 6) [6,40,160,320,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29139
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29140 : Route 9 := (fun mask => (mask,id))

def c29140 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29140 : Upper (D 6) (R 6) [6,40,160,320,68] 13 := by
  apply FastRouting.sound _ _ [6,40,160,320,68] 13 (by decide) (choices 1) [1,2,16] r29140 c29140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10510
  · exact u10511
  · exact u10512

def b29141 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 42 196 25 19 356 356 484 356), lower := (rows 7 42 196 25 19 32 64 128 256), losses := [] }

theorem u29141 : Upper (D 6) (R 6) [6,40,192,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29141
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29142 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 42 196 25 21 354 354 482 354), lower := (rows 7 42 196 25 21 32 64 128 256), losses := [] }

theorem u29142 : Upper (D 6) (R 6) [6,40,192,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29142
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29143 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 196 25 22 353 353 481 353), lower := (rows 7 42 196 25 22 32 64 128 256), losses := [] }

theorem u29143 : Upper (D 6) (R 6) [6,40,192,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29143
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29144 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 10, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 42 196 25 49 358 326 454 326), lower := (rows 7 42 196 25 49 32 64 128 256), losses := [] }

theorem u29144 : Upper (D 6) (R 6) [6,40,192,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29144
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29145 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 196 25 50 357 325 453 325), lower := (rows 7 42 196 25 50 32 64 128 256), losses := [] }

theorem u29145 : Upper (D 6) (R 6) [6,40,192,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29145
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29146 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 196 25 52 355 323 451 323), lower := (rows 7 42 196 25 52 32 64 128 256), losses := [] }

theorem u29146 : Upper (D 6) (R 6) [6,40,192,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29146
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29147 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 42 196 25 81 294 358 422 294), lower := (rows 7 42 196 25 81 32 64 128 256), losses := [] }

theorem u29147 : Upper (D 6) (R 6) [6,40,192,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29147
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29148 : Route 9 := (fun mask => (mask,id))

def c29148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29148 : Upper (D 6) (R 6) [6,40,192,17,66] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,66] 13 (by decide) (choices 1) [1,4,256] r29148 c29148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10513
  · exact u10514
  · exact u10515

def b29149 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 196 25 84 291 355 419 291), lower := (rows 7 42 196 25 84 32 64 128 256), losses := [] }

theorem u29149 : Upper (D 6) (R 6) [6,40,192,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29149
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29150 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(1,6),(2,5)], upper := (rows 7 42 196 25 112 295 327 391 263), lower := (rows 7 42 196 25 112 32 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 33 0 129 257), good := (rows 423 42 132 443 48 32 0 128 256) }] }

theorem u29150 : Upper (D 6) (R 6) [6,40,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29150
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29151 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 42 196 25 273 102 102 230 358), lower := (rows 7 42 196 25 273 32 64 128 256), losses := [] }

theorem u29151 : Upper (D 6) (R 6) [6,40,192,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29151
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29152 : Route 9 := (fun mask => (mask,id))

def c29152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29152 : Upper (D 6) (R 6) [6,40,192,17,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,258] 13 (by decide) (choices 1) [1,4,64] r29152 c29152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10516
  · exact u10517
  · exact u10518

def r29153 : Route 9 := (fun mask => (mask,id))

def c29153 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29153 : Upper (D 6) (R 6) [6,40,192,17,260] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,260] 13 (by decide) (choices 1) [1,2,64] r29153 c29153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10519
  · exact u10520
  · exact u10521

def r29154 : Route 9 := (fun mask => (mask,id))

def c29154 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29154 : Upper (D 6) (R 6) [6,40,192,17,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,288] 13 (by decide) (choices 1) [1,2,4,64] r29154 c29154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10522
  · exact u10523
  · exact u10524
  · exact u10525

def r29155 : Route 9 := (fun mask => (mask,id))

def c29155 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29155 : Upper (D 6) (R 6) [6,40,192,17,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,320] 13 (by decide) (choices 1) [1,2,4] r29155 c29155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10526
  · exact u10527
  · exact u10528

def b29156 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 196 26 21 353 353 481 353), lower := (rows 7 42 196 26 21 32 64 128 256), losses := [] }

theorem u29156 : Upper (D 6) (R 6) [6,40,192,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29156
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29157 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 26 49 357 325 453 325), lower := (rows 7 42 196 26 49 32 64 128 256), losses := [] }

theorem u29157 : Upper (D 6) (R 6) [6,40,192,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29157
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29158 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 196 26 52 353 321 449 321), lower := (rows 7 42 196 26 52 32 64 128 256), losses := [] }

theorem u29158 : Upper (D 6) (R 6) [6,40,192,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29158
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29159 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 7 42 196 26 81 293 357 421 293), lower := (rows 7 42 196 26 81 32 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 33 0 129 257), good := (rows 423 42 132 26 443 32 0 128 256) }] }

theorem u29159 : Upper (D 6) (R 6) [6,40,192,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29159
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29159
end Delivery.IrregularNine14.P06
