import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0274
import IrregularNine14P07C0275
import IrregularNine14P07C0276

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32940 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 196 328 176 35 67 131 259), lower := (rows 13 50 196 328 176 32 64 128 256), losses := [] }

theorem u32940 : Upper (D 7) (R 7) [12,48,192,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32941 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 7 25 50 480 448 448 448), lower := (rows 13 98 7 25 50 32 64 128 256), losses := [] }

theorem u32941 : Upper (D 7) (R 7) [12,96,3,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32942 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 7 25 112 418 450 386 386), lower := (rows 13 98 7 25 112 32 64 128 256), losses := [] }

theorem u32942 : Upper (D 7) (R 7) [12,96,3,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32943 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 13, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 98 7 25 146 480 480 480 480), lower := (rows 13 98 7 25 146 32 64 128 256), losses := [] }

theorem u32943 : Upper (D 7) (R 7) [12,96,3,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32944 : Route 9 := (fun mask => (mask,id))

def c32944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32944 : Upper (D 7) (R 7) [12,96,3,17,160] 13 := by
  apply FastRouting.sound _ _ [12,96,3,17,160] 13 (by decide) (choices 1) [2,64,128,256] r32944 c32944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16480
  · exact u16481
  · exact u16482
  · exact u16483

def b32945 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 13, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 98 7 25 274 224 224 224 480), lower := (rows 13 98 7 25 274 32 64 128 256), losses := [] }

theorem u32945 : Upper (D 7) (R 7) [12,96,3,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32946 : Route 9 := (fun mask => (mask,id))

def c32946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32946 : Upper (D 7) (R 7) [12,96,3,17,288] 13 := by
  apply FastRouting.sound _ _ [12,96,3,17,288] 13 (by decide) (choices 1) [2,64,128] r32946 c32946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16484
  · exact u16485
  · exact u16486

def r32947 : Route 9 := (fun mask => (mask,id))

def c32947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32947 : Upper (D 7) (R 7) [12,96,3,17,384] 13 := by
  apply FastRouting.sound _ _ [12,96,3,17,384] 13 (by decide) (choices 1) [2,64,128] r32947 c32947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16487
  · exact u16488
  · exact u16489

def b32948 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 7 56 19 480 448 448 448), lower := (rows 13 98 7 56 19 32 64 128 256), losses := [] }

theorem u32948 : Upper (D 7) (R 7) [12,96,3,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32949 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 7 56 81 418 450 386 386), lower := (rows 13 98 7 56 81 32 64 128 256), losses := [] }

theorem u32949 : Upper (D 7) (R 7) [12,96,3,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32950 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 7 56 82 417 449 385 385), lower := (rows 13 98 7 56 82 32 64 128 256), losses := [] }

theorem u32950 : Upper (D 7) (R 7) [12,96,3,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32951 : Route 9 := (fun mask => (mask,id))

def c32951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32951 : Upper (D 7) (R 7) [12,96,3,48,129] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,129] 13 (by decide) (choices 1) [2,64,128,256] r32951 c32951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16490
  · exact u16491
  · exact u16492
  · exact u16493

def r32952 : Route 9 := (fun mask => (mask,id))

def c32952 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32952 : Upper (D 7) (R 7) [12,96,3,48,130] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,130] 13 (by decide) (choices 1) [1,64,128,256] r32952 c32952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16494
  · exact u16495
  · exact u16496
  · exact u16497

def r32953 : Route 9 := (fun mask => (mask,id))

def c32953 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32953 : Upper (D 7) (R 7) [12,96,3,48,192] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,192] 13 (by decide) (choices 1) [1,2,128,256] r32953 c32953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16498
  · exact u16499
  · exact u16500
  · exact u16501

def r32954 : Route 9 := (fun mask => (mask,id))

def c32954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32954 : Upper (D 7) (R 7) [12,96,3,48,257] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,257] 13 (by decide) (choices 1) [2,64,128] r32954 c32954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16502
  · exact u16503
  · exact u16504

def r32955 : Route 9 := (fun mask => (mask,id))

def c32955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32955 : Upper (D 7) (R 7) [12,96,3,48,258] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,258] 13 (by decide) (choices 1) [1,64,128] r32955 c32955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16505
  · exact u16506
  · exact u16507

def r32956 : Route 9 := (fun mask => (mask,id))

def c32956 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32956 : Upper (D 7) (R 7) [12,96,3,48,320] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,320] 13 (by decide) (choices 1) [1,2,128] r32956 c32956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16508
  · exact u16509
  · exact u16510

def r32957 : Route 9 := (fun mask => (mask,id))

def c32957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32957 : Upper (D 7) (R 7) [12,96,3,48,384] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,384] 13 (by decide) (choices 1) [1,2,64,128] r32957 c32957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16511
  · exact u16512
  · exact u16513
  · exact u16514

def b32958 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 98 7 137 50 496 464 464 464), lower := (rows 13 98 7 137 50 32 64 128 256), losses := [] }

theorem u32958 : Upper (D 7) (R 7) [12,96,3,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32959 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 16, targets := 2 },{ cop := 1, region := 16, targets := 128 }], pairs := [(1,0),(4,0),(4,1),(4,7)], upper := (rows 13 98 7 137 112 434 466 402 402), lower := (rows 13 98 7 137 112 32 64 128 256), losses := [] }

theorem u32959 : Upper (D 7) (R 7) [12,96,3,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32960 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 13, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 13 98 7 137 146 368 368 496 368), lower := (rows 13 98 7 137 146 32 64 128 256), losses := [] }

theorem u32960 : Upper (D 7) (R 7) [12,96,3,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32961 : Route 9 := (fun mask => (mask,id))

def c32961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u32961 : Upper (D 7) (R 7) [12,96,3,129,160] 13 := by
  apply FastRouting.sound _ _ [12,96,3,129,160] 13 (by decide) (choices 1) [2,16,64,256] r32961 c32961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16515
  · exact u16516
  · exact u16517
  · exact u16518

def r32962 : Route 9 := (fun mask => (mask,id))

def c32962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32962 : Upper (D 7) (R 7) [12,96,3,129,258] 13 := by
  apply FastRouting.sound _ _ [12,96,3,129,258] 13 (by decide) (choices 1) [16,64,128] r32962 c32962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16519
  · exact u16520
  · exact u16521

def r32963 : Route 9 := (fun mask => (mask,id))

def c32963 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32963 : Upper (D 7) (R 7) [12,96,3,129,288] 13 := by
  apply FastRouting.sound _ _ [12,96,3,129,288] 13 (by decide) (choices 1) [2,16,64,128] r32963 c32963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16522
  · exact u16523
  · exact u16524
  · exact u16525

def r32964 : Route 9 := (fun mask => (mask,id))

def c32964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32964 : Upper (D 7) (R 7) [12,96,3,129,384] 13 := by
  apply FastRouting.sound _ _ [12,96,3,129,384] 13 (by decide) (choices 1) [2,16,64] r32964 c32964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16526
  · exact u16527
  · exact u16528

def b32965 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 98 7 152 19 480 480 480 480), lower := (rows 13 98 7 152 19 32 64 128 256), losses := [] }

theorem u32965 : Upper (D 7) (R 7) [12,96,3,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32966 : Route 9 := (fun mask => (mask,id))

def c32966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32966 : Upper (D 7) (R 7) [12,96,3,144,33] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,33] 13 (by decide) (choices 1) [2,64,128,256] r32966 c32966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16529
  · exact u16530
  · exact u16531
  · exact u16532

def b32967 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 7 152 50 481 449 449 449), lower := (rows 13 98 7 152 50 32 64 128 256), losses := [] }

theorem u32967 : Upper (D 7) (R 7) [12,96,3,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32968 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 7 152 112 419 451 387 387), lower := (rows 13 98 7 152 112 32 64 128 256), losses := [] }

theorem u32968 : Upper (D 7) (R 7) [12,96,3,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32969 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 13 98 7 152 145 354 354 482 354), lower := (rows 13 98 7 152 145 32 64 128 256), losses := [] }

theorem u32969 : Upper (D 7) (R 7) [12,96,3,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32970 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 13, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 13 98 7 152 146 353 353 481 353), lower := (rows 13 98 7 152 146 32 64 128 256), losses := [] }

theorem u32970 : Upper (D 7) (R 7) [12,96,3,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32971 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 98 7 152 176 355 323 451 323), lower := (rows 13 98 7 152 176 32 64 128 256), losses := [] }

theorem u32971 : Upper (D 7) (R 7) [12,96,3,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32972 : Route 9 := (fun mask => (mask,id))

def c32972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32972 : Upper (D 7) (R 7) [12,96,3,144,257] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,257] 13 (by decide) (choices 1) [2,64,128] r32972 c32972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16533
  · exact u16534
  · exact u16535

def r32973 : Route 9 := (fun mask => (mask,id))

def c32973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32973 : Upper (D 7) (R 7) [12,96,3,144,258] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,258] 13 (by decide) (choices 1) [1,64,128] r32973 c32973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16536
  · exact u16537
  · exact u16538

def r32974 : Route 9 := (fun mask => (mask,id))

def c32974 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32974 : Upper (D 7) (R 7) [12,96,3,144,288] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,288] 13 (by decide) (choices 1) [1,2,64,128] r32974 c32974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16539
  · exact u16540
  · exact u16541
  · exact u16542

def b32975 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 98 7 152 400 99 99 227 355), lower := (rows 13 98 7 152 400 32 64 128 256), losses := [] }

theorem u32975 : Upper (D 7) (R 7) [12,96,3,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32976 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 13 98 7 168 19 496 464 464 464), lower := (rows 13 98 7 168 19 32 64 128 256), losses := [] }

theorem u32976 : Upper (D 7) (R 7) [12,96,3,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32977 : Route 9 := (fun mask => (mask,id))

def c32977 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u32977 : Upper (D 7) (R 7) [12,96,3,160,65] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,65] 13 (by decide) (choices 1) [2,16,128,256] r32977 c32977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16543
  · exact u16544
  · exact u16545
  · exact u16546

def b32978 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 7 168 82 433 465 401 401), lower := (rows 13 98 7 168 82 32 64 128 256), losses := [] }

theorem u32978 : Upper (D 7) (R 7) [12,96,3,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32979 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 7 168 145 370 338 466 338), lower := (rows 13 98 7 168 145 32 64 128 256), losses := [] }

theorem u32979 : Upper (D 7) (R 7) [12,96,3,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32980 : Route 9 := (fun mask => (mask,id))

def c32980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u32980 : Upper (D 7) (R 7) [12,96,3,160,130] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,130] 13 (by decide) (choices 1) [1,16,64,256] r32980 c32980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16547
  · exact u16548
  · exact u16549
  · exact u16550

def r32981 : Route 9 := (fun mask => (mask,id))

def c32981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32981 : Upper (D 7) (R 7) [12,96,3,160,192] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,192] 13 (by decide) (choices 1) [1,2,16,256] r32981 c32981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16551
  · exact u16552
  · exact u16553
  · exact u16554

def r32982 : Route 9 := (fun mask => (mask,id))

def c32982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32982 : Upper (D 7) (R 7) [12,96,3,160,257] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,257] 13 (by decide) (choices 1) [2,16,64,128] r32982 c32982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16555
  · exact u16556
  · exact u16557
  · exact u16558

def r32983 : Route 9 := (fun mask => (mask,id))

def c32983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32983 : Upper (D 7) (R 7) [12,96,3,160,258] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,258] 13 (by decide) (choices 1) [1,16,64,128] r32983 c32983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16559
  · exact u16560
  · exact u16561
  · exact u16562

def r32984 : Route 9 := (fun mask => (mask,id))

def c32984 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32984 : Upper (D 7) (R 7) [12,96,3,160,320] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,320] 13 (by decide) (choices 1) [1,2,16,128] r32984 c32984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16563
  · exact u16564
  · exact u16565
  · exact u16566

def r32985 : Route 9 := (fun mask => (mask,id))

def c32985 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32985 : Upper (D 7) (R 7) [12,96,3,160,384] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,384] 13 (by decide) (choices 1) [1,2,16,64] r32985 c32985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16567
  · exact u16568
  · exact u16569
  · exact u16570

def b32986 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 98 7 265 50 240 208 208 464), lower := (rows 13 98 7 265 50 32 64 128 256), losses := [] }

theorem u32986 : Upper (D 7) (R 7) [12,96,3,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32987 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 16, targets := 2 },{ cop := 1, region := 16, targets := 128 }], pairs := [(1,0),(4,0),(4,1),(4,7)], upper := (rows 13 98 7 265 112 178 210 146 402), lower := (rows 13 98 7 265 112 32 64 128 256), losses := [] }

theorem u32987 : Upper (D 7) (R 7) [12,96,3,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32988 : Route 9 := (fun mask => (mask,id))

def c32988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32988 : Upper (D 7) (R 7) [12,96,3,257,130] 13 := by
  apply FastRouting.sound _ _ [12,96,3,257,130] 13 (by decide) (choices 1) [16,64,128] r32988 c32988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16571
  · exact u16572
  · exact u16573

def r32989 : Route 9 := (fun mask => (mask,id))

def c32989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32989 : Upper (D 7) (R 7) [12,96,3,257,160] 13 := by
  apply FastRouting.sound _ _ [12,96,3,257,160] 13 (by decide) (choices 1) [2,16,64,128] r32989 c32989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16574
  · exact u16575
  · exact u16576
  · exact u16577

def b32990 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 98 7 280 19 224 224 224 480), lower := (rows 13 98 7 280 19 32 64 128 256), losses := [] }

theorem u32990 : Upper (D 7) (R 7) [12,96,3,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32991 : Route 9 := (fun mask => (mask,id))

def c32991 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32991 : Upper (D 7) (R 7) [12,96,3,272,33] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,33] 13 (by decide) (choices 1) [2,64,128] r32991 c32991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16578
  · exact u16579
  · exact u16580

def b32992 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 7 280 50 225 193 193 449), lower := (rows 13 98 7 280 50 32 64 128 256), losses := [] }

theorem u32992 : Upper (D 7) (R 7) [12,96,3,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32993 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 7 280 112 163 195 131 387), lower := (rows 13 98 7 280 112 32 64 128 256), losses := [] }

theorem u32993 : Upper (D 7) (R 7) [12,96,3,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32994 : Route 9 := (fun mask => (mask,id))

def c32994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32994 : Upper (D 7) (R 7) [12,96,3,272,129] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,129] 13 (by decide) (choices 1) [2,64,128] r32994 c32994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16581
  · exact u16582
  · exact u16583

def r32995 : Route 9 := (fun mask => (mask,id))

def c32995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32995 : Upper (D 7) (R 7) [12,96,3,272,130] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,130] 13 (by decide) (choices 1) [1,64,128] r32995 c32995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16584
  · exact u16585
  · exact u16586

def r32996 : Route 9 := (fun mask => (mask,id))

def c32996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32996 : Upper (D 7) (R 7) [12,96,3,272,160] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,160] 13 (by decide) (choices 1) [1,2,64,128] r32996 c32996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16587
  · exact u16588
  · exact u16589
  · exact u16590

def b32997 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 13 98 7 296 19 240 208 208 464), lower := (rows 13 98 7 296 19 32 64 128 256), losses := [] }

theorem u32997 : Upper (D 7) (R 7) [12,96,3,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32998 : Route 9 := (fun mask => (mask,id))

def c32998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32998 : Upper (D 7) (R 7) [12,96,3,288,65] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288,65] 13 (by decide) (choices 1) [2,16,128] r32998 c32998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16591
  · exact u16592
  · exact u16593

def b32999 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 7 296 82 177 209 145 401), lower := (rows 13 98 7 296 82 32 64 128 256), losses := [] }

theorem u32999 : Upper (D 7) (R 7) [12,96,3,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u32999
end Delivery.IrregularNine14.P07
