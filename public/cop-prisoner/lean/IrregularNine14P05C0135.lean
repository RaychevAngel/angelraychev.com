import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0075
import IrregularNine14P05C0076

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8100 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 140 296 28 55 87 151 279), lower := (rows 35 67 140 296 28 32 64 128 256), losses := [] }

theorem u8100 : Upper (D 5) (R 5) [34,65,136,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8100
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8101 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 148 296 19 44 76 140 268), lower := (rows 35 67 148 296 19 32 64 128 256), losses := [] }

theorem u8101 : Upper (D 5) (R 5) [34,65,144,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8101
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8102 : Route 9 := (fun mask => (mask,id))

def c8102 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8102 : Upper (D 5) (R 5) [34,65,144,288,5] 13 := by
  apply FastRouting.sound _ _ [34,65,144,288,5] 13 (by decide) (choices 1) [2,4,8] r8102 c8102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4518
  · exact u4519
  · exact u4520

def r8103 : Route 9 := (fun mask => (mask,id))

def c8103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8103 : Upper (D 5) (R 5) [34,65,144,288,6] 13 := by
  apply FastRouting.sound _ _ [34,65,144,288,6] 13 (by decide) (choices 1) [1,4,8] r8103 c8103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4521
  · exact u4522
  · exact u4523

def b8104 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 148 296 25 46 78 142 270), lower := (rows 35 67 148 296 25 32 64 128 256), losses := [] }

theorem u8104 : Upper (D 5) (R 5) [34,65,144,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8104
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8105 : Route 9 := (fun mask => (mask,id))

def c8105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8105 : Upper (D 5) (R 5) [34,65,144,288,10] 13 := by
  apply FastRouting.sound _ _ [34,65,144,288,10] 13 (by decide) (choices 1) [1,4,8] r8105 c8105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4524
  · exact u4525
  · exact u4526

def r8106 : Route 9 := (fun mask => (mask,id))

def c8106 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8106 : Upper (D 5) (R 5) [34,65,144,288,12] 13 := by
  apply FastRouting.sound _ _ [34,65,144,288,12] 13 (by decide) (choices 1) [1,2,4,8] r8106 c8106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4527
  · exact u4528
  · exact u4529
  · exact u4530

def b8107 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 44 137 19 316 348 412 284), lower := (rows 35 70 44 137 19 32 64 128 256), losses := [] }

theorem u8107 : Upper (D 5) (R 5) [34,68,40,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8107
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8108 : PairBound 9 := { available := 282, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 44 137 21 314 346 410 282), lower := (rows 35 70 44 137 21 32 64 128 256), losses := [] }

theorem u8108 : Upper (D 5) (R 5) [34,68,40,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8108
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8109 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 44 137 22 313 345 409 281), lower := (rows 35 70 44 137 22 32 64 128 256), losses := [] }

theorem u8109 : Upper (D 5) (R 5) [34,68,40,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8109
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m8110_4 : Upper (D 5) (R 5) [34,68,40,129,10,4] 13 :=
  permutation_upper _ _ _ [34,68,40,129,10,1] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4531

def r8110 : Route 9 := (fun mask => (mask,id))

def c8110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8110 : Upper (D 5) (R 5) [34,68,40,129,10] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,10] 13 (by decide) (choices 1) [1,4,16,256] r8110 c8110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4531
  · exact m8110_4
  · exact u4532
  · exact u4533

def r8111 : Route 9 := (fun mask => (mask,id))

def c8111 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8111 : Upper (D 5) (R 5) [34,68,40,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,257] 13 (by decide) (choices 1) [2,4,8,16] r8111 c8111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4534
  · exact u4535
  · exact u4536
  · exact u4537

def r8112 : Route 9 := (fun mask => (mask,id))

def c8112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8112 : Upper (D 5) (R 5) [34,68,40,129,258] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,258] 13 (by decide) (choices 1) [1,4,8,16] r8112 c8112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4538
  · exact u4539
  · exact u4540
  · exact u4541

def b8113 : PairBound 9 := { available := 281, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 44 138 21 313 345 409 281), lower := (rows 35 70 44 138 21 32 64 128 256), losses := [] }

theorem u8113 : Upper (D 5) (R 5) [34,68,40,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8113
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8114 : Route 9 := (fun mask => (mask,id))

def c8114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8114 : Upper (D 5) (R 5) [34,68,40,130,9] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,9] 13 (by decide) (choices 1) [1,4,16,256] r8114 c8114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4542
  · exact u4543
  · exact u4544
  · exact u4545

def b8115 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 44 138 28 305 337 401 273), lower := (rows 35 70 44 138 28 32 64 128 256), losses := [] }

theorem u8115 : Upper (D 5) (R 5) [34,68,40,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8115
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8116 : Route 9 := (fun mask => (mask,id))

def c8116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8116 : Upper (D 5) (R 5) [34,68,40,130,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,257] 13 (by decide) (choices 1) [1,4,8,16] r8116 c8116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4546
  · exact u4547
  · exact u4548
  · exact u4549

def r8117 : Route 9 := (fun mask => (mask,id))

def c8117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8117 : Upper (D 5) (R 5) [34,68,40,130,260] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,260] 13 (by decide) (choices 1) [1,8,16] r8117 c8117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4550
  · exact u4551
  · exact u4552

def r8118 : Route 9 := (fun mask => (mask,id))

def c8118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8118 : Upper (D 5) (R 5) [34,68,40,130,264] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,264] 13 (by decide) (choices 1) [1,4,16] r8118 c8118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4553
  · exact u4554
  · exact u4555

def b8119 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 44 152 19 301 333 397 269), lower := (rows 35 70 44 152 19 32 64 128 256), losses := [] }

theorem u8119 : Upper (D 5) (R 5) [34,68,40,144,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8119
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8120 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 44 152 21 299 331 395 267), lower := (rows 35 70 44 152 21 32 64 128 256), losses := [] }

theorem u8120 : Upper (D 5) (R 5) [34,68,40,144,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8120
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8121 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 44 152 22 297 329 393 265), lower := (rows 35 70 44 152 22 32 64 128 256), losses := [] }

theorem u8121 : Upper (D 5) (R 5) [34,68,40,144,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8122 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 152 25 295 327 391 263), lower := (rows 35 70 44 152 25 32 64 128 256), losses := [] }

theorem u8122 : Upper (D 5) (R 5) [34,68,40,144,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8123 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 152 26 293 325 389 261), lower := (rows 35 70 44 152 26 32 64 128 256), losses := [] }

theorem u8123 : Upper (D 5) (R 5) [34,68,40,144,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8123
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8124 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 44 152 28 291 323 387 259), lower := (rows 35 70 44 152 28 32 64 128 256), losses := [] }

theorem u8124 : Upper (D 5) (R 5) [34,68,40,144,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8124
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8125 : Route 9 := (fun mask => (mask,id))

def c8125 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8125 : Upper (D 5) (R 5) [34,68,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,257] 13 (by decide) (choices 1) [1,2,4,8] r8125 c8125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4556
  · exact u4557
  · exact u4558
  · exact u4559

def r8126 : Route 9 := (fun mask => (mask,id))

def c8126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8126 : Upper (D 5) (R 5) [34,68,40,144,258] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,258] 13 (by decide) (choices 1) [1,4,8] r8126 c8126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4560
  · exact u4561
  · exact u4562

def r8127 : Route 9 := (fun mask => (mask,id))

def c8127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8127 : Upper (D 5) (R 5) [34,68,40,144,260] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,260] 13 (by decide) (choices 1) [1,2,8] r8127 c8127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4563
  · exact u4564
  · exact u4565

def b8128 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 152 280 39 71 135 263), lower := (rows 35 70 44 152 280 32 64 128 256), losses := [] }

theorem u8128 : Upper (D 5) (R 5) [34,68,40,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8129 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 70 44 392 19 61 93 157 285), lower := (rows 35 70 44 392 19 32 64 128 256), losses := [] }

theorem u8129 : Upper (D 5) (R 5) [34,68,40,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8130 : PairBound 9 := { available := 27, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 44 392 21 59 91 155 283), lower := (rows 35 70 44 392 21 32 64 128 256), losses := [] }

theorem u8130 : Upper (D 5) (R 5) [34,68,40,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8130
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8131 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 44 392 22 57 89 153 281), lower := (rows 35 70 44 392 22 32 64 128 256), losses := [] }

theorem u8131 : Upper (D 5) (R 5) [34,68,40,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8131
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8132 : Route 9 := (fun mask => (mask,id))

def c8132 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8132 : Upper (D 5) (R 5) [34,68,40,384,9] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,9] 13 (by decide) (choices 1) [1,2,4,16] r8132 c8132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4566
  · exact u4567
  · exact u4568
  · exact u4569

def r8133 : Route 9 := (fun mask => (mask,id))

def c8133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8133 : Upper (D 5) (R 5) [34,68,40,384,10] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,10] 13 (by decide) (choices 1) [1,4,16] r8133 c8133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4570
  · exact u4571
  · exact u4572

def b8134 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 44 392 28 51 83 147 275), lower := (rows 35 70 44 392 28 32 64 128 256), losses := [] }

theorem u8134 : Upper (D 5) (R 5) [34,68,40,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8134
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8135 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 52 137 19 300 332 396 268), lower := (rows 35 70 52 137 19 32 64 128 256), losses := [] }

theorem u8135 : Upper (D 5) (R 5) [34,68,48,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8135
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8136 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 20, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 70 52 137 21 298 330 394 266), lower := (rows 35 70 52 137 21 32 64 128 256), losses := [] }

theorem u8136 : Upper (D 5) (R 5) [34,68,48,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8136
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8137 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 52 137 22 297 329 393 265), lower := (rows 35 70 52 137 22 32 64 128 256), losses := [] }

theorem u8137 : Upper (D 5) (R 5) [34,68,48,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8137
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8138 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 52 137 25 302 334 398 270), lower := (rows 35 70 52 137 25 32 64 128 256), losses := [] }

theorem u8138 : Upper (D 5) (R 5) [34,68,48,129,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8138
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8139 : Route 9 := (fun mask => (mask,id))

def c8139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8139 : Upper (D 5) (R 5) [34,68,48,129,10] 13 := by
  apply FastRouting.sound _ _ [34,68,48,129,10] 13 (by decide) (choices 1) [1,4,8,256] r8139 c8139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4573
  · exact u4574
  · exact u4575
  · exact u4576

def b8140 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 425, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 52 137 28 299 331 395 267), lower := (rows 35 70 52 137 28 32 64 128 256), losses := [] }

theorem u8140 : Upper (D 5) (R 5) [34,68,48,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8140
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8141 : Route 9 := (fun mask => (mask,id))

def c8141 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8141 : Upper (D 5) (R 5) [34,68,48,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,48,129,257] 13 (by decide) (choices 1) [2,4,8] r8141 c8141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4577
  · exact u4578
  · exact u4579

def r8142 : Route 9 := (fun mask => (mask,id))

def c8142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8142 : Upper (D 5) (R 5) [34,68,48,129,258] 13 := by
  apply FastRouting.sound _ _ [34,68,48,129,258] 13 (by decide) (choices 1) [1,4,8] r8142 c8142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4580
  · exact u4581
  · exact u4582

def b8143 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 169, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 52 137 276 43 75 139 267), lower := (rows 35 70 52 137 276 32 64 128 256), losses := [] }

theorem u8143 : Upper (D 5) (R 5) [34,68,48,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8143
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8144 : Route 9 := (fun mask => (mask,id))

def c8144 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8144 : Upper (D 5) (R 5) [34,68,48,129,264] 13 := by
  apply FastRouting.sound _ _ [34,68,48,129,264] 13 (by decide) (choices 1) [1,2,4,8] r8144 c8144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4583
  · exact u4584
  · exact u4585
  · exact u4586

def b8145 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 20, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 70 52 138 21 297 329 393 265), lower := (rows 35 70 52 138 21 32 64 128 256), losses := [] }

theorem u8145 : Upper (D 5) (R 5) [34,68,48,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8145
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8146 : Route 9 := (fun mask => (mask,id))

def c8146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8146 : Upper (D 5) (R 5) [34,68,48,130,9] 13 := by
  apply FastRouting.sound _ _ [34,68,48,130,9] 13 (by decide) (choices 1) [1,4,8,256] r8146 c8146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4587
  · exact u4588
  · exact u4589
  · exact u4590

def b8147 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 425, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 52 138 28 297 329 393 265), lower := (rows 35 70 52 138 28 32 64 128 256), losses := [] }

theorem u8147 : Upper (D 5) (R 5) [34,68,48,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8147
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8148 : Route 9 := (fun mask => (mask,id))

def c8148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8148 : Upper (D 5) (R 5) [34,68,48,130,257] 13 := by
  apply FastRouting.sound _ _ [34,68,48,130,257] 13 (by decide) (choices 1) [1,4,8] r8148 c8148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4591
  · exact u4592
  · exact u4593

def b8149 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 169, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 52 138 276 41 73 137 265), lower := (rows 35 70 52 138 276 32 64 128 256), losses := [] }

theorem u8149 : Upper (D 5) (R 5) [34,68,48,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8149
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8150 : Route 9 := (fun mask => (mask,id))

def c8150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8150 : Upper (D 5) (R 5) [34,68,48,130,264] 13 := by
  apply FastRouting.sound _ _ [34,68,48,130,264] 13 (by decide) (choices 1) [1,4,8] r8150 c8150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4594
  · exact u4595
  · exact u4596

def b8151 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 52 140 19 297 329 393 265), lower := (rows 35 70 52 140 19 32 64 128 256), losses := [] }

theorem u8151 : Upper (D 5) (R 5) [34,68,48,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8152 : Route 9 := (fun mask => (mask,id))

def c8152 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8152 : Upper (D 5) (R 5) [34,68,48,132,9] 13 := by
  apply FastRouting.sound _ _ [34,68,48,132,9] 13 (by decide) (choices 1) [1,2,8,256] r8152 c8152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4597
  · exact u4598
  · exact u4599
  · exact u4600

def r8153 : Route 9 := (fun mask => (mask,id))

def c8153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8153 : Upper (D 5) (R 5) [34,68,48,132,10] 13 := by
  apply FastRouting.sound _ _ [34,68,48,132,10] 13 (by decide) (choices 1) [1,8,256] r8153 c8153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4601
  · exact u4602
  · exact u4603

def r8154 : Route 9 := (fun mask => (mask,id))

def c8154 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8154 : Upper (D 5) (R 5) [34,68,48,132,257] 13 := by
  apply FastRouting.sound _ _ [34,68,48,132,257] 13 (by decide) (choices 1) [1,2,8] r8154 c8154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4604
  · exact u4605
  · exact u4606

def r8155 : Route 9 := (fun mask => (mask,id))

def c8155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8155 : Upper (D 5) (R 5) [34,68,48,132,258] 13 := by
  apply FastRouting.sound _ _ [34,68,48,132,258] 13 (by decide) (choices 1) [1,8] r8155 c8155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4607
  · exact u4608

def r8156 : Route 9 := (fun mask => (mask,id))

def c8156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8156 : Upper (D 5) (R 5) [34,68,48,132,264] 13 := by
  apply FastRouting.sound _ _ [34,68,48,132,264] 13 (by decide) (choices 1) [1,2,8] r8156 c8156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4609
  · exact u4610
  · exact u4611

def b8157 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 52 392 19 45 77 141 269), lower := (rows 35 70 52 392 19 32 64 128 256), losses := [] }

theorem u8157 : Upper (D 5) (R 5) [34,68,48,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8157
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8158 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 20, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 70 52 392 21 43 75 139 267), lower := (rows 35 70 52 392 21 32 64 128 256), losses := [] }

theorem u8158 : Upper (D 5) (R 5) [34,68,48,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8158
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8159 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 35 70 52 392 22 41 73 137 265), lower := (rows 35 70 52 392 22 32 64 128 256), losses := [] }

theorem u8159 : Upper (D 5) (R 5) [34,68,48,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8159
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8159
end Delivery.IrregularNine14.P05
