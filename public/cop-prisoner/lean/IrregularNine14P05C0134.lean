import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0073
import IrregularNine14P05C0074
import IrregularNine14P05C0075

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8040 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 20, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 67 52 392 21 46 78 142 270), lower := (rows 35 67 52 392 21 32 64 128 256), losses := [] }

theorem u8040 : Upper (D 5) (R 5) [34,65,48,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8040
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8041 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 52 392 22 45 77 141 269), lower := (rows 35 67 52 392 22 32 64 128 256), losses := [] }

theorem u8041 : Upper (D 5) (R 5) [34,65,48,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8041
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8042 : Route 9 := (fun mask => (mask,id))

def c8042 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8042 : Upper (D 5) (R 5) [34,65,48,384,9] 13 := by
  apply FastRouting.sound _ _ [34,65,48,384,9] 13 (by decide) (choices 1) [2,4,8] r8042 c8042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4415
  · exact u4416
  · exact u4417

def r8043 : Route 9 := (fun mask => (mask,id))

def c8043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8043 : Upper (D 5) (R 5) [34,65,48,384,10] 13 := by
  apply FastRouting.sound _ _ [34,65,48,384,10] 13 (by decide) (choices 1) [1,4,8] r8043 c8043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4418
  · exact u4419
  · exact u4420

def r8044 : Route 9 := (fun mask => (mask,id))

def c8044 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8044 : Upper (D 5) (R 5) [34,65,48,384,12] 13 := by
  apply FastRouting.sound _ _ [34,65,48,384,12] 13 (by decide) (choices 1) [1,2,4,8] r8044 c8044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4421
  · exact u4422
  · exact u4423
  · exact u4424

def r8045 : Route 9 := (fun mask => (mask,id))

def c8045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8045 : Upper (D 5) (R 5) [34,65,129,258,12] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258,12] 13 (by decide) (choices 1) [4,8,16] r8045 c8045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4425
  · exact u4426
  · exact u4427

def r8046 : Route 9 := (fun mask => (mask,id))

def c8046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8046 : Upper (D 5) (R 5) [34,65,129,258,36] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258,36] 13 (by decide) (choices 1) [4,8,16] r8046 c8046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4428
  · exact u4429
  · exact u4430

def r8047 : Route 9 := (fun mask => (mask,id))

def c8047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8047 : Upper (D 5) (R 5) [34,65,129,258,40] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258,40] 13 (by decide) (choices 1) [4,8,16] r8047 c8047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4431
  · exact u4432
  · exact u4433

def b8048 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 268 22 56 120 184 312), lower := (rows 35 67 133 268 22 32 64 128 256), losses := [] }

theorem u8048 : Upper (D 5) (R 5) [34,65,129,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8048
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8049 : Route 9 := (fun mask => (mask,id))

def c8049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8049 : Upper (D 5) (R 5) [34,65,129,260,10] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,10] 13 (by decide) (choices 1) [4,8,16] r8049 c8049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4434
  · exact u4435
  · exact u4436

def b8050 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 268 28 58 122 186 314), lower := (rows 35 67 133 268 28 32 64 128 256), losses := [] }

theorem u8050 : Upper (D 5) (R 5) [34,65,129,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8050
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8051 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 67 133 268 50 60 92 156 284), lower := (rows 35 67 133 268 50 32 64 128 256), losses := [] }

theorem u8051 : Upper (D 5) (R 5) [34,65,129,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8051
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8052 : Route 9 := (fun mask => (mask,id))

def c8052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8052 : Upper (D 5) (R 5) [34,65,129,260,36] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,36] 13 (by decide) (choices 1) [2,8,16] r8052 c8052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4437
  · exact u4438
  · exact u4439

def r8053 : Route 9 := (fun mask => (mask,id))

def c8053 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8053 : Upper (D 5) (R 5) [34,65,129,260,40] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,40] 13 (by decide) (choices 1) [2,4,8,16] r8053 c8053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4440
  · exact u4441
  · exact u4442
  · exact u4443

def b8054 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 280 22 44 108 172 300), lower := (rows 35 67 133 280 22 32 64 128 256), losses := [] }

theorem u8054 : Upper (D 5) (R 5) [34,65,129,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8054
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8055 : Route 9 := (fun mask => (mask,id))

def c8055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8055 : Upper (D 5) (R 5) [34,65,129,272,10] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272,10] 13 (by decide) (choices 1) [4,8] r8055 c8055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4444
  · exact u4445

def r8056 : Route 9 := (fun mask => (mask,id))

def c8056 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8056 : Upper (D 5) (R 5) [34,65,129,272,12] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272,12] 13 (by decide) (choices 1) [2,4,8] r8056 c8056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4446
  · exact u4447
  · exact u4448

def b8057 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 67 133 280 50 44 76 140 268), lower := (rows 35 67 133 280 50 32 64 128 256), losses := [] }

theorem u8057 : Upper (D 5) (R 5) [34,65,129,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8057
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8058 : Route 9 := (fun mask => (mask,id))

def c8058 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8058 : Upper (D 5) (R 5) [34,65,129,272,36] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272,36] 13 (by decide) (choices 1) [2,4,8] r8058 c8058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4449
  · exact u4450
  · exact u4451

def r8059 : Route 9 := (fun mask => (mask,id))

def c8059 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8059 : Upper (D 5) (R 5) [34,65,129,272,40] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272,40] 13 (by decide) (choices 1) [2,4,8] r8059 c8059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4452
  · exact u4453
  · exact u4454

def b8060 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 296 22 60 92 156 284), lower := (rows 35 67 133 296 22 32 64 128 256), losses := [] }

theorem u8060 : Upper (D 5) (R 5) [34,65,129,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8060
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8061 : Route 9 := (fun mask => (mask,id))

def c8061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8061 : Upper (D 5) (R 5) [34,65,129,288,10] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288,10] 13 (by decide) (choices 1) [4,8,16] r8061 c8061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4455
  · exact u4456
  · exact u4457

def r8062 : Route 9 := (fun mask => (mask,id))

def c8062 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8062 : Upper (D 5) (R 5) [34,65,129,288,12] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288,12] 13 (by decide) (choices 1) [2,4,8,16] r8062 c8062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4458
  · exact u4459
  · exact u4460
  · exact u4461

def b8063 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 134 268 21 56 120 184 312), lower := (rows 35 67 134 268 21 32 64 128 256), losses := [] }

theorem u8063 : Upper (D 5) (R 5) [34,65,130,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8063
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8064 : Route 9 := (fun mask => (mask,id))

def c8064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8064 : Upper (D 5) (R 5) [34,65,130,260,9] 13 := by
  apply FastRouting.sound _ _ [34,65,130,260,9] 13 (by decide) (choices 1) [4,8,16] r8064 c8064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4462
  · exact u4463
  · exact u4464

def b8065 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 134 268 28 57 121 185 313), lower := (rows 35 67 134 268 28 32 64 128 256), losses := [] }

theorem u8065 : Upper (D 5) (R 5) [34,65,130,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8065
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8066 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 67 134 268 49 60 92 156 284), lower := (rows 35 67 134 268 49 32 64 128 256), losses := [] }

theorem u8066 : Upper (D 5) (R 5) [34,65,130,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8066
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8067 : Route 9 := (fun mask => (mask,id))

def c8067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8067 : Upper (D 5) (R 5) [34,65,130,260,36] 13 := by
  apply FastRouting.sound _ _ [34,65,130,260,36] 13 (by decide) (choices 1) [1,8,16] r8067 c8067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4465
  · exact u4466
  · exact u4467

def r8068 : Route 9 := (fun mask => (mask,id))

def c8068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8068 : Upper (D 5) (R 5) [34,65,130,260,40] 13 := by
  apply FastRouting.sound _ _ [34,65,130,260,40] 13 (by decide) (choices 1) [1,4,8,16] r8068 c8068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4468
  · exact u4469
  · exact u4470
  · exact u4471

def b8069 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 134 280 21 44 108 172 300), lower := (rows 35 67 134 280 21 32 64 128 256), losses := [] }

theorem u8069 : Upper (D 5) (R 5) [34,65,130,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8069
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8070 : Route 9 := (fun mask => (mask,id))

def c8070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8070 : Upper (D 5) (R 5) [34,65,130,272,9] 13 := by
  apply FastRouting.sound _ _ [34,65,130,272,9] 13 (by decide) (choices 1) [4,8] r8070 c8070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4472
  · exact u4473

def r8071 : Route 9 := (fun mask => (mask,id))

def c8071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8071 : Upper (D 5) (R 5) [34,65,130,272,12] 13 := by
  apply FastRouting.sound _ _ [34,65,130,272,12] 13 (by decide) (choices 1) [1,4,8] r8071 c8071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4474
  · exact u4475
  · exact u4476

def b8072 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 67 134 280 49 44 76 140 268), lower := (rows 35 67 134 280 49 32 64 128 256), losses := [] }

theorem u8072 : Upper (D 5) (R 5) [34,65,130,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8072
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8073 : Route 9 := (fun mask => (mask,id))

def c8073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8073 : Upper (D 5) (R 5) [34,65,130,272,36] 13 := by
  apply FastRouting.sound _ _ [34,65,130,272,36] 13 (by decide) (choices 1) [1,4,8] r8073 c8073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4477
  · exact u4478
  · exact u4479

def r8074 : Route 9 := (fun mask => (mask,id))

def c8074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8074 : Upper (D 5) (R 5) [34,65,130,272,40] 13 := by
  apply FastRouting.sound _ _ [34,65,130,272,40] 13 (by decide) (choices 1) [1,4,8] r8074 c8074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4480
  · exact u4481
  · exact u4482

def b8075 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 134 296 21 60 92 156 284), lower := (rows 35 67 134 296 21 32 64 128 256), losses := [] }

theorem u8075 : Upper (D 5) (R 5) [34,65,130,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8075
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8076 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 134 296 25 60 92 156 284), lower := (rows 35 67 134 296 25 32 64 128 256), losses := [] }

theorem u8076 : Upper (D 5) (R 5) [34,65,130,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8076
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8077 : Route 9 := (fun mask => (mask,id))

def c8077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8077 : Upper (D 5) (R 5) [34,65,130,288,12] 13 := by
  apply FastRouting.sound _ _ [34,65,130,288,12] 13 (by decide) (choices 1) [1,4,8,16] r8077 c8077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4483
  · exact u4484
  · exact u4485
  · exact u4486

def b8078 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 268 19 60 124 188 316), lower := (rows 35 67 140 268 19 32 64 128 256), losses := [] }

theorem u8078 : Upper (D 5) (R 5) [34,65,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8078
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8079 : Route 9 := (fun mask => (mask,id))

def c8079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8079 : Upper (D 5) (R 5) [34,65,136,260,5] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260,5] 13 (by decide) (choices 1) [2,8,16] r8079 c8079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4487
  · exact u4488
  · exact u4489

def r8080 : Route 9 := (fun mask => (mask,id))

def c8080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8080 : Upper (D 5) (R 5) [34,65,136,260,6] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260,6] 13 (by decide) (choices 1) [1,8,16] r8080 c8080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4490
  · exact u4491
  · exact u4492

def b8081 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 140 268 28 51 115 179 307), lower := (rows 35 67 140 268 28 32 64 128 256), losses := [] }

theorem u8081 : Upper (D 5) (R 5) [34,65,136,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8081
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8082 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 67 140 268 49 62 94 158 286), lower := (rows 35 67 140 268 49 32 64 128 256), losses := [] }

theorem u8082 : Upper (D 5) (R 5) [34,65,136,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8082
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8083 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 67 140 268 50 61 93 157 285), lower := (rows 35 67 140 268 50 32 64 128 256), losses := [] }

theorem u8083 : Upper (D 5) (R 5) [34,65,136,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8083
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8084 : Route 9 := (fun mask => (mask,id))

def c8084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8084 : Upper (D 5) (R 5) [34,65,136,260,36] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260,36] 13 (by decide) (choices 1) [1,2,8,16] r8084 c8084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4493
  · exact u4494
  · exact u4495
  · exact u4496

def b8085 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 280 19 44 108 172 300), lower := (rows 35 67 140 280 19 32 64 128 256), losses := [] }

theorem u8085 : Upper (D 5) (R 5) [34,65,136,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8085
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8086 : Route 9 := (fun mask => (mask,id))

def c8086 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8086 : Upper (D 5) (R 5) [34,65,136,272,5] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,5] 13 (by decide) (choices 1) [2,4,8] r8086 c8086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4497
  · exact u4498
  · exact u4499

def r8087 : Route 9 := (fun mask => (mask,id))

def c8087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8087 : Upper (D 5) (R 5) [34,65,136,272,6] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,6] 13 (by decide) (choices 1) [1,4,8] r8087 c8087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4500
  · exact u4501
  · exact u4502

def b8088 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 140 280 25 38 102 166 294), lower := (rows 35 67 140 280 25 32 64 128 256), losses := [] }

theorem u8088 : Upper (D 5) (R 5) [34,65,136,272,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8088
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8089 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 140 280 26 37 101 165 293), lower := (rows 35 67 140 280 26 32 64 128 256), losses := [] }

theorem u8089 : Upper (D 5) (R 5) [34,65,136,272,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8089
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8090 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 140 280 28 39 103 167 295), lower := (rows 35 67 140 280 28 32 64 128 256), losses := [] }

theorem u8090 : Upper (D 5) (R 5) [34,65,136,272,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8090
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8091 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 67 140 280 49 46 78 142 270), lower := (rows 35 67 140 280 49 32 64 128 256), losses := [] }

theorem u8091 : Upper (D 5) (R 5) [34,65,136,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8091
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8092 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 67 140 280 50 45 77 141 269), lower := (rows 35 67 140 280 50 32 64 128 256), losses := [] }

theorem u8092 : Upper (D 5) (R 5) [34,65,136,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8092
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8093 : Route 9 := (fun mask => (mask,id))

def c8093 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8093 : Upper (D 5) (R 5) [34,65,136,272,36] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,36] 13 (by decide) (choices 1) [1,2,4,8] r8093 c8093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4503
  · exact u4504
  · exact u4505
  · exact u4506

def b8094 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 140 280 56 39 71 135 263), lower := (rows 35 67 140 280 56 32 64 128 256), losses := [] }

theorem u8094 : Upper (D 5) (R 5) [34,65,136,272,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8094
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8095 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 296 19 60 92 156 284), lower := (rows 35 67 140 296 19 32 64 128 256), losses := [] }

theorem u8095 : Upper (D 5) (R 5) [34,65,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8095
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8096 : Route 9 := (fun mask => (mask,id))

def c8096 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8096 : Upper (D 5) (R 5) [34,65,136,288,5] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,5] 13 (by decide) (choices 1) [2,4,8,16] r8096 c8096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4507
  · exact u4508
  · exact u4509
  · exact u4510

def r8097 : Route 9 := (fun mask => (mask,id))

def c8097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8097 : Upper (D 5) (R 5) [34,65,136,288,6] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,6] 13 (by decide) (choices 1) [1,4,8,16] r8097 c8097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4511
  · exact u4512
  · exact u4513
  · exact u4514

def b8098 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 140 296 25 54 86 150 278), lower := (rows 35 67 140 296 25 32 64 128 256), losses := [] }

theorem u8098 : Upper (D 5) (R 5) [34,65,136,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8098
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8099 : Route 9 := (fun mask => (mask,id))

def c8099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8099 : Upper (D 5) (R 5) [34,65,136,288,10] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,10] 13 (by decide) (choices 1) [1,4,16] r8099 c8099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4515
  · exact u4516
  · exact u4517

#print axioms u8099
end Delivery.IrregularNine14.P05
