import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0090
import IrregularNine14P09C0091
import IrregularNine14P09C0092

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8040 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 200 400 313 345 409 281), lower := (rows 97 7 38 200 400 32 64 128 256), losses := [] }

theorem u8040 : Upper (D 9) (R 9) [96,5,34,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8040 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8041 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 30, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 44 25 82 416 448 384 384), lower := (rows 97 7 44 25 82 32 64 128 256), losses := [] }

theorem u8041 : Upper (D 9) (R 9) [96,5,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8041 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8042 : Route 9 := (fun mask => (mask,id))

def c8042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8042 : Upper (D 9) (R 9) [96,5,40,17,130] 13 := by
  apply FastRouting.sound _ _ [96,5,40,17,130] 13 (by decide) (choices 1) [64,128,256] r8042 c8042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5439
  · exact u5440
  · exact u5441

def b8043 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 3, region := 422, targets := 64 },{ cop := 1, region := 464, targets := 1 }], pairs := [(1,6),(2,6),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 25 208 418 450 386 386), lower := (rows 97 7 44 25 208 32 64 128 256), losses := [] }

theorem u8043 : Upper (D 9) (R 9) [96,5,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8043 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8044 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8044 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8044 : Upper (D 9) (R 9) [96,5,40,17,384] 13 := by
  apply FastRouting.sound _ _ [96,5,40,17,384] 13 (by decide) (choices 1) [2,64,128] r8044 c8044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5442
  · exact u5443
  · exact u5444

def b8045 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 30, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 44 26 81 416 448 384 384), lower := (rows 97 7 44 26 81 32 64 128 256), losses := [] }

theorem u8045 : Upper (D 9) (R 9) [96,5,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8045 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8046 : Route 9 := (fun mask => (mask,id))

def c8046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8046 : Upper (D 9) (R 9) [96,5,40,18,129] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18,129] 13 (by decide) (choices 1) [64,128,256] r8046 c8046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5445
  · exact u5446
  · exact u5447

def r8047 : Route 9 := (fun mask => (mask,id))

def c8047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8047 : Upper (D 9) (R 9) [96,5,40,18,192] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18,192] 13 (by decide) (choices 1) [1,128,256] r8047 c8047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5448
  · exact u5449
  · exact u5450

def r8048 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8048 : Upper (D 9) (R 9) [96,5,40,18,384] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18,384] 13 (by decide) (choices 1) [1,64,128] r8048 c8048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5451
  · exact u5452
  · exact u5453

def b8049 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 44 73 146 432 464 400 400), lower := (rows 97 7 44 73 146 32 64 128 256), losses := [] }

theorem u8049 : Upper (D 9) (R 9) [96,5,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8049 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8050 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 44 73 400 434 466 402 402), lower := (rows 97 7 44 73 400 32 64 128 256), losses := [] }

theorem u8050 : Upper (D 9) (R 9) [96,5,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8050 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8051 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 44 74 145 432 464 400 400), lower := (rows 97 7 44 74 145 32 64 128 256), losses := [] }

theorem u8051 : Upper (D 9) (R 9) [96,5,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8051 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8052 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 44 74 400 433 465 401 401), lower := (rows 97 7 44 74 400 32 64 128 256), losses := [] }

theorem u8052 : Upper (D 9) (R 9) [96,5,40,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8052 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8053 : Route 9 := (fun mask => (mask,id))

def c8053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8053 : Upper (D 9) (R 9) [96,5,40,80,129] 13 := by
  apply FastRouting.sound _ _ [96,5,40,80,129] 13 (by decide) (choices 1) [2,128,256] r8053 c8053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5454
  · exact u5455
  · exact u5456

def r8054 : Route 9 := (fun mask => (mask,id))

def c8054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8054 : Upper (D 9) (R 9) [96,5,40,80,130] 13 := by
  apply FastRouting.sound _ _ [96,5,40,80,130] 13 (by decide) (choices 1) [1,128,256] r8054 c8054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5457
  · exact u5458
  · exact u5459

def r8055 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8055 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8055 : Upper (D 9) (R 9) [96,5,40,80,384] 13 := by
  apply FastRouting.sound _ _ [96,5,40,80,384] 13 (by decide) (choices 1) [1,2,128] r8055 c8055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5460
  · exact u5461
  · exact u5462

def r8056 : Route 9 := (fun mask => (mask,id))

def c8056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8056 : Upper (D 9) (R 9) [96,5,40,129,66] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,66] 13 (by decide) (choices 1) [16,128,256] r8056 c8056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5463
  · exact u5464
  · exact u5465

def r8057 : Route 9 := (fun mask => (mask,id))

def c8057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8057 : Upper (D 9) (R 9) [96,5,40,129,130] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,130] 13 (by decide) (choices 1) [16,64,256] r8057 c8057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5466
  · exact u5467
  · exact u5468

def r8058 : Route 9 := (fun mask => (mask,id))

def c8058 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8058 : Upper (D 9) (R 9) [96,5,40,129,192] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,192] 13 (by decide) (choices 1) [2,16,256] r8058 c8058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5469
  · exact u5470
  · exact u5471

def r8059 : Route 9 := (fun mask => (mask,id))

def c8059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u8059 : Upper (D 9) (R 9) [96,5,40,129,258] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,258] 13 (by decide) (choices 1) [16,64,128,256] r8059 c8059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5472
  · exact u5473
  · exact u5474
  · exact u5475

def r8060 : Route 9 := (fun mask => (mask,id))

def c8060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8060 : Upper (D 9) (R 9) [96,5,40,129,320] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,320] 13 (by decide) (choices 1) [2,16,128,256] r8060 c8060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5476
  · exact u5477
  · exact u5478
  · exact u5479

def r8061 : Route 9 := (fun mask => (mask,id))

def c8061 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8061 : Upper (D 9) (R 9) [96,5,40,129,384] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129,384] 13 (by decide) (choices 1) [2,16,64,256] r8061 c8061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5480
  · exact u5481
  · exact u5482
  · exact u5483

def b8062 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 430, targets := 64 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,6),(2,6),(3,6),(4,7),(4,8)], upper := (rows 97 7 44 138 81 432 464 400 400), lower := (rows 97 7 44 138 81 32 64 128 256), losses := [] }

theorem u8062 : Upper (D 9) (R 9) [96,5,40,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8062 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8063 : Route 9 := (fun mask => (mask,id))

def c8063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8063 : Upper (D 9) (R 9) [96,5,40,130,129] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,129] 13 (by decide) (choices 1) [16,64,256] r8063 c8063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5484
  · exact u5485
  · exact u5486

def r8064 : Route 9 := (fun mask => (mask,id))

def c8064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8064 : Upper (D 9) (R 9) [96,5,40,130,192] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,192] 13 (by decide) (choices 1) [1,16,256] r8064 c8064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5487
  · exact u5488
  · exact u5489

def r8065 : Route 9 := (fun mask => (mask,id))

def c8065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u8065 : Upper (D 9) (R 9) [96,5,40,130,257] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,257] 13 (by decide) (choices 1) [16,64,128,256] r8065 c8065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5490
  · exact u5491
  · exact u5492
  · exact u5493

def r8066 : Route 9 := (fun mask => (mask,id))

def c8066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8066 : Upper (D 9) (R 9) [96,5,40,130,320] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,320] 13 (by decide) (choices 1) [1,16,128,256] r8066 c8066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5494
  · exact u5495
  · exact u5496
  · exact u5497

def r8067 : Route 9 := (fun mask => (mask,id))

def c8067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8067 : Upper (D 9) (R 9) [96,5,40,130,384] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,384] 13 (by decide) (choices 1) [1,16,64,256] r8067 c8067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5498
  · exact u5499
  · exact u5500
  · exact u5501

def b8068 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 16, targets := 416 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,6),(4,5),(4,7),(4,8)], upper := (rows 97 7 44 152 81 418 450 386 386), lower := (rows 97 7 44 152 81 32 64 128 256), losses := [] }

theorem u8068 : Upper (D 9) (R 9) [96,5,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8068 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8069 : Route 9 := (fun mask => (mask,id))

def c8069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8069 : Upper (D 9) (R 9) [96,5,40,144,66] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,66] 13 (by decide) (choices 1) [1,128,256] r8069 c8069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5502
  · exact u5503
  · exact u5504

def b8070 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 7 44 152 145 354 322 450 322), lower := (rows 97 7 44 152 145 32 64 128 256), losses := [] }

theorem u8070 : Upper (D 9) (R 9) [96,5,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8070 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8071 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 7 44 152 146 353 321 449 321), lower := (rows 97 7 44 152 146 32 64 128 256), losses := [] }

theorem u8071 : Upper (D 9) (R 9) [96,5,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8071 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8072 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 7 44 152 208 291 323 387 259), lower := (rows 97 7 44 152 208 32 64 128 256), losses := [] }

theorem u8072 : Upper (D 9) (R 9) [96,5,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8072 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8073 : Route 9 := (fun mask => (mask,id))

def c8073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8073 : Upper (D 9) (R 9) [96,5,40,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,257] 13 (by decide) (choices 1) [2,64,128,256] r8073 c8073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5505
  · exact u5506
  · exact u5507
  · exact u5508

def r8074 : Route 9 := (fun mask => (mask,id))

def c8074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8074 : Upper (D 9) (R 9) [96,5,40,144,258] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,258] 13 (by decide) (choices 1) [1,64,128,256] r8074 c8074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5509
  · exact u5510
  · exact u5511
  · exact u5512

def r8075 : Route 9 := (fun mask => (mask,id))

def c8075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8075 : Upper (D 9) (R 9) [96,5,40,144,320] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,320] 13 (by decide) (choices 1) [1,2,128,256] r8075 c8075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5513
  · exact u5514
  · exact u5515
  · exact u5516

def b8076 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 7 44 152 400 355 323 451 323), lower := (rows 97 7 44 152 400 32 64 128 256), losses := [] }

theorem u8076 : Upper (D 9) (R 9) [96,5,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8076 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8077 : Route 9 := (fun mask => (mask,id))

def c8077 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8077 : Upper (D 9) (R 9) [96,5,40,192,129] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,129] 13 (by decide) (choices 1) [2,16,256] r8077 c8077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5517
  · exact u5518
  · exact u5519

def r8078 : Route 9 := (fun mask => (mask,id))

def c8078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8078 : Upper (D 9) (R 9) [96,5,40,192,130] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,130] 13 (by decide) (choices 1) [1,16,256] r8078 c8078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5520
  · exact u5521
  · exact u5522

def r8079 : Route 9 := (fun mask => (mask,id))

def c8079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8079 : Upper (D 9) (R 9) [96,5,40,192,257] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,257] 13 (by decide) (choices 1) [2,16,128,256] r8079 c8079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5523
  · exact u5524
  · exact u5525
  · exact u5526

def r8080 : Route 9 := (fun mask => (mask,id))

def c8080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8080 : Upper (D 9) (R 9) [96,5,40,192,258] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,258] 13 (by decide) (choices 1) [1,16,128,256] r8080 c8080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5527
  · exact u5528
  · exact u5529
  · exact u5530

def r8081 : Route 9 := (fun mask => (mask,id))

def c8081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8081 : Upper (D 9) (R 9) [96,5,40,192,384] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192,384] 13 (by decide) (choices 1) [1,2,16,256] r8081 c8081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5531
  · exact u5532
  · exact u5533
  · exact u5534

def b8082 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 16, targets := 416 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,6),(4,5),(4,7),(4,8)], upper := (rows 97 7 44 392 81 434 466 402 402), lower := (rows 97 7 44 392 81 32 64 128 256), losses := [] }

theorem u8082 : Upper (D 9) (R 9) [96,5,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8082 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8083 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8083 : Upper (D 9) (R 9) [96,5,40,384,66] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,66] 13 (by decide) (choices 1) [1,16,128] r8083 c8083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5535
  · exact u5536
  · exact u5537

def r8084 : Route 9 := (fun mask => (mask,id))

def c8084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8084 : Upper (D 9) (R 9) [96,5,40,384,129] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,129] 13 (by decide) (choices 1) [2,16,64,256] r8084 c8084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5538
  · exact u5539
  · exact u5540
  · exact u5541

def r8085 : Route 9 := (fun mask => (mask,id))

def c8085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8085 : Upper (D 9) (R 9) [96,5,40,384,130] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,130] 13 (by decide) (choices 1) [1,16,64,256] r8085 c8085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5542
  · exact u5543
  · exact u5544
  · exact u5545

def r8086 : Route 9 := (fun mask => (mask,id))

def c8086 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8086 : Upper (D 9) (R 9) [96,5,40,384,192] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,192] 13 (by decide) (choices 1) [1,2,16,256] r8086 c8086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5546
  · exact u5547
  · exact u5548
  · exact u5549

def b8087 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 97 7 44 392 400 115 83 211 339), lower := (rows 97 7 44 392 400 32 64 128 256), losses := [] }

theorem u8087 : Upper (D 9) (R 9) [96,5,40,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8087 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8088 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 25 146 424 456 392 392), lower := (rows 97 7 100 25 146 32 64 128 256), losses := [] }

theorem u8088 : Upper (D 9) (R 9) [96,5,96,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8088 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8089 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 25 152 418 450 386 386), lower := (rows 97 7 100 25 152 32 64 128 256), losses := [] }

theorem u8089 : Upper (D 9) (R 9) [96,5,96,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8089 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8090 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 25 400 426 458 394 394), lower := (rows 97 7 100 25 400 32 64 128 256), losses := [] }

theorem u8090 : Upper (D 9) (R 9) [96,5,96,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8090 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8091 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 26 145 424 456 392 392), lower := (rows 97 7 100 26 145 32 64 128 256), losses := [] }

theorem u8091 : Upper (D 9) (R 9) [96,5,96,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8091 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8092 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 26 152 417 449 385 385), lower := (rows 97 7 100 26 152 32 64 128 256), losses := [] }

theorem u8092 : Upper (D 9) (R 9) [96,5,96,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8092 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8093 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 26 400 425 457 393 393), lower := (rows 97 7 100 26 400 32 64 128 256), losses := [] }

theorem u8093 : Upper (D 9) (R 9) [96,5,96,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8093 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8094 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 137 146 312 344 408 280), lower := (rows 97 7 100 137 146 32 64 128 256), losses := [] }

theorem u8094 : Upper (D 9) (R 9) [96,5,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8094 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8095 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 137 274 440 472 408 408), lower := (rows 97 7 100 137 274 32 64 128 256), losses := [] }

theorem u8095 : Upper (D 9) (R 9) [96,5,96,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8095 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8096 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 137 280 434 466 402 402), lower := (rows 97 7 100 137 280 32 64 128 256), losses := [] }

theorem u8096 : Upper (D 9) (R 9) [96,5,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8096 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8097 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 137 400 314 346 410 282), lower := (rows 97 7 100 137 400 32 64 128 256), losses := [] }

theorem u8097 : Upper (D 9) (R 9) [96,5,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8097 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8098 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 138 280 433 465 401 401), lower := (rows 97 7 100 138 280 32 64 128 256), losses := [] }

theorem u8098 : Upper (D 9) (R 9) [96,5,96,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8098 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8099 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 138 400 313 345 409 281), lower := (rows 97 7 100 138 400 32 64 128 256), losses := [] }

theorem u8099 : Upper (D 9) (R 9) [96,5,96,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8099 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u8099
end Delivery.IrregularNine14.P09
