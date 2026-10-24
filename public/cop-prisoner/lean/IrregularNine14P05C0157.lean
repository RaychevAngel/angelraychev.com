import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0133
import IrregularNine14P05C0134
import IrregularNine14P05C0135
import IrregularNine14P05C0136
import IrregularNine14P05C0137
import IrregularNine14P05C0138

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9420 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 8 }], pairs := [(2,0),(2,3)], upper := (rows 35 67 38 137 284 316 348 412 284), lower := (rows 35 67 38 137 16 32 64 128 256), losses := [] }

theorem u9420 : Upper (D 5) (R 5) [34,65,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9420
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9421 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 8 }], pairs := [(2,0),(2,3)], upper := (rows 35 67 38 140 285 317 349 413 285), lower := (rows 35 67 38 140 16 32 64 128 256), losses := [] }

theorem u9421 : Upper (D 5) (R 5) [34,65,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9421
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9422 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 8 }], pairs := [(2,0),(2,3)], upper := (rows 35 67 38 152 285 301 333 397 269), lower := (rows 35 67 38 152 16 32 64 128 256), losses := [] }

theorem u9422 : Upper (D 5) (R 5) [34,65,34,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9422
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9423 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 8 }], pairs := [(2,0),(2,3)], upper := (rows 35 67 38 392 29 61 93 157 285), lower := (rows 35 67 38 392 16 32 64 128 256), losses := [] }

theorem u9423 : Upper (D 5) (R 5) [34,65,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9423
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9424 : Route 9 := (fun mask => (mask,id))

def c9424 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9424 : Upper (D 5) (R 5) [34,65,40,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129] 13 (by decide) (choices 2) [6,10,12,258,260,264] r9424 c9424
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7983
  · exact u7984
  · exact u7985
  · exact u7986
  · exact u7987
  · exact u7988

def r9425 : Route 9 := (fun mask => (mask,id))

def c9425 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9425 : Upper (D 5) (R 5) [34,65,40,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9425 c9425
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7989
  · exact u7990
  · exact u7991
  · exact u7992
  · exact u7993
  · exact u7994

theorem m9426_9 : Upper (D 5) (R 5) [34,65,40,132,9] 13 :=
  permutation_upper _ _ _ [34,65,40,132,6] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7997

theorem m9426_12 : Upper (D 5) (R 5) [34,65,40,132,12] 13 :=
  permutation_upper _ _ _ [34,65,40,132,3] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7995

theorem m9426_260 : Upper (D 5) (R 5) [34,65,40,132,260] 13 :=
  permutation_upper _ _ _ [34,65,40,132,257] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7999

theorem m9426_264 : Upper (D 5) (R 5) [34,65,40,132,264] 13 :=
  permutation_upper _ _ _ [34,65,40,132,258] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8000

def r9426 : Route 9 := (fun mask => (mask,id))

def c9426 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9426 : Upper (D 5) (R 5) [34,65,40,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9426 c9426
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7995
  · exact u7996
  · exact u7997
  · exact m9426_9
  · exact u7998
  · exact m9426_12
  · exact u7999
  · exact u8000
  · exact m9426_260
  · exact m9426_264

def r9427 : Route 9 := (fun mask => (mask,id))

def c9427 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9427 : Upper (D 5) (R 5) [34,65,40,144] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9427 c9427
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8001
  · exact u8002
  · exact u8003
  · exact u8004
  · exact u8005
  · exact u8006
  · exact u8007
  · exact u8008
  · exact u8009
  · exact u8010

def r9428 : Route 9 := (fun mask => (mask,id))

def c9428 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9428 : Upper (D 5) (R 5) [34,65,40,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9428 c9428
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8011
  · exact u8012
  · exact u8013
  · exact u8014
  · exact u8015
  · exact u8016

def r9429 : Route 9 := (fun mask => (mask,id))

def c9429 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9429 : Upper (D 5) (R 5) [34,65,48,129] 13 := by
  apply FastRouting.sound _ _ [34,65,48,129] 13 (by decide) (choices 2) [6,10,12,258,260,264] r9429 c9429
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8017
  · exact u8018
  · exact u8019
  · exact u8020
  · exact u8021
  · exact u8022

def r9430 : Route 9 := (fun mask => (mask,id))

def c9430 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9430 : Upper (D 5) (R 5) [34,65,48,130] 13 := by
  apply FastRouting.sound _ _ [34,65,48,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9430 c9430
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8023
  · exact u8024
  · exact u8025
  · exact u8026
  · exact u8027
  · exact u8028

def r9431 : Route 9 := (fun mask => (mask,id))

def c9431 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9431 : Upper (D 5) (R 5) [34,65,48,132] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9431 c9431
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8029
  · exact u8030
  · exact u8031
  · exact u8032
  · exact u8033
  · exact u8034
  · exact u8035
  · exact u8036
  · exact u8037
  · exact u8038

def r9432 : Route 9 := (fun mask => (mask,id))

def c9432 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9432 : Upper (D 5) (R 5) [34,65,48,384] 13 := by
  apply FastRouting.sound _ _ [34,65,48,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9432 c9432
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8039
  · exact u8040
  · exact u8041
  · exact u8042
  · exact u8043
  · exact u8044

def r9433 : Route 9 := (fun mask => (mask,id))

def c9433 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9433 : Upper (D 5) (R 5) [34,65,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258] 13 (by decide) (choices 2) [12,36,40] r9433 c9433
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8045
  · exact u8046
  · exact u8047

def r9434 : Route 9 := (fun mask => (mask,id))

def c9434 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9434 : Upper (D 5) (R 5) [34,65,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9434 c9434
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8048
  · exact u8049
  · exact u8050
  · exact u8051
  · exact u8052
  · exact u8053

def r9435 : Route 9 := (fun mask => (mask,id))

def c9435 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9435 : Upper (D 5) (R 5) [34,65,129,272] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9435 c9435
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8054
  · exact u8055
  · exact u8056
  · exact u8057
  · exact u8058
  · exact u8059

def r9436 : Route 9 := (fun mask => (mask,id))

def c9436 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9436 : Upper (D 5) (R 5) [34,65,129,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288] 13 (by decide) (choices 2) [6,10,12] r9436 c9436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8060
  · exact u8061
  · exact u8062

def r9437 : Route 9 := (fun mask => (mask,id))

def c9437 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9437 : Upper (D 5) (R 5) [34,65,130,260] 13 := by
  apply FastRouting.sound _ _ [34,65,130,260] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9437 c9437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8063
  · exact u8064
  · exact u8065
  · exact u8066
  · exact u8067
  · exact u8068

def r9438 : Route 9 := (fun mask => (mask,id))

def c9438 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9438 : Upper (D 5) (R 5) [34,65,130,272] 13 := by
  apply FastRouting.sound _ _ [34,65,130,272] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9438 c9438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8069
  · exact u8070
  · exact u8071
  · exact u8072
  · exact u8073
  · exact u8074

def r9439 : Route 9 := (fun mask => (mask,id))

def c9439 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9439 : Upper (D 5) (R 5) [34,65,130,288] 13 := by
  apply FastRouting.sound _ _ [34,65,130,288] 13 (by decide) (choices 2) [5,9,12] r9439 c9439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8075
  · exact u8076
  · exact u8077

theorem m9440_9 : Upper (D 5) (R 5) [34,65,136,260,9] 13 :=
  permutation_upper _ _ _ [34,65,136,260,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8079

theorem m9440_10 : Upper (D 5) (R 5) [34,65,136,260,10] 13 :=
  permutation_upper _ _ _ [34,65,136,260,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8080

theorem m9440_40 : Upper (D 5) (R 5) [34,65,136,260,40] 13 :=
  permutation_upper _ _ _ [34,65,136,260,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8084

def r9440 : Route 9 := (fun mask => (mask,id))

def c9440 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9440 : Upper (D 5) (R 5) [34,65,136,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9440 c9440
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8078
  · exact u8079
  · exact u8080
  · exact m9440_9
  · exact m9440_10
  · exact u8081
  · exact u8082
  · exact u8083
  · exact u8084
  · exact m9440_40

def r9441 : Route 9 := (fun mask => (mask,id))

def c9441 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9441 : Upper (D 5) (R 5) [34,65,136,272] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9441 c9441
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8085
  · exact u8086
  · exact u8087
  · exact u8088
  · exact u8089
  · exact u8090
  · exact u8091
  · exact u8092
  · exact u8093
  · exact u8094

def r9442 : Route 9 := (fun mask => (mask,id))

def c9442 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9442 : Upper (D 5) (R 5) [34,65,136,288] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9442 c9442
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8095
  · exact u8096
  · exact u8097
  · exact u8098
  · exact u8099
  · exact u8100

def r9443 : Route 9 := (fun mask => (mask,id))

def c9443 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9443 : Upper (D 5) (R 5) [34,65,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,144,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9443 c9443
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8101
  · exact u8102
  · exact u8103
  · exact u8104
  · exact u8105
  · exact u8106

theorem m9444_9 : Upper (D 5) (R 5) [34,68,40,129,9] 13 :=
  permutation_upper _ _ _ [34,68,40,129,6] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8109

theorem m9444_12 : Upper (D 5) (R 5) [34,68,40,129,12] 13 :=
  permutation_upper _ _ _ [34,68,40,129,3] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8107

theorem m9444_260 : Upper (D 5) (R 5) [34,68,40,129,260] 13 :=
  permutation_upper _ _ _ [34,68,40,129,257] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8111

theorem m9444_264 : Upper (D 5) (R 5) [34,68,40,129,264] 13 :=
  permutation_upper _ _ _ [34,68,40,129,258] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8112

def r9444 : Route 9 := (fun mask => (mask,id))

def c9444 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9444 : Upper (D 5) (R 5) [34,68,40,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9444 c9444
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8107
  · exact u8108
  · exact u8109
  · exact m9444_9
  · exact u8110
  · exact m9444_12
  · exact u8111
  · exact u8112
  · exact m9444_260
  · exact m9444_264

def r9445 : Route 9 := (fun mask => (mask,id))

def c9445 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9445 : Upper (D 5) (R 5) [34,68,40,130] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9445 c9445
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8113
  · exact u8114
  · exact u8115
  · exact u8116
  · exact u8117
  · exact u8118

def r9446 : Route 9 := (fun mask => (mask,id))

def c9446 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9446 : Upper (D 5) (R 5) [34,68,40,144] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9446 c9446
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8119
  · exact u8120
  · exact u8121
  · exact u8122
  · exact u8123
  · exact u8124
  · exact u8125
  · exact u8126
  · exact u8127
  · exact u8128

def r9447 : Route 9 := (fun mask => (mask,id))

def c9447 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9447 : Upper (D 5) (R 5) [34,68,40,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9447 c9447
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8129
  · exact u8130
  · exact u8131
  · exact u8132
  · exact u8133
  · exact u8134

def r9448 : Route 9 := (fun mask => (mask,id))

def c9448 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9448 : Upper (D 5) (R 5) [34,68,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,48,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9448 c9448
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8135
  · exact u8136
  · exact u8137
  · exact u8138
  · exact u8139
  · exact u8140
  · exact u8141
  · exact u8142
  · exact u8143
  · exact u8144

def r9449 : Route 9 := (fun mask => (mask,id))

def c9449 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9449 : Upper (D 5) (R 5) [34,68,48,130] 13 := by
  apply FastRouting.sound _ _ [34,68,48,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9449 c9449
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8145
  · exact u8146
  · exact u8147
  · exact u8148
  · exact u8149
  · exact u8150

def r9450 : Route 9 := (fun mask => (mask,id))

def c9450 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9450 : Upper (D 5) (R 5) [34,68,48,132] 13 := by
  apply FastRouting.sound _ _ [34,68,48,132] 13 (by decide) (choices 2) [3,9,10,257,258,264] r9450 c9450
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8151
  · exact u8152
  · exact u8153
  · exact u8154
  · exact u8155
  · exact u8156

def r9451 : Route 9 := (fun mask => (mask,id))

def c9451 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9451 : Upper (D 5) (R 5) [34,68,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,48,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9451 c9451
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8157
  · exact u8158
  · exact u8159
  · exact u8160
  · exact u8161
  · exact u8162

def b9452 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 4 }], pairs := [(3,0),(3,2)], upper := (rows 35 70 133 42 285 317 349 413 285), lower := (rows 35 70 133 42 16 32 64 128 256), losses := [] }

theorem u9452 : Upper (D 5) (R 5) [34,68,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9452
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9453 : Route 9 := (fun mask => (mask,id))

def c9453 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9453 : Upper (D 5) (R 5) [34,68,129,48] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9453 c9453
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8163
  · exact u8164
  · exact u8165
  · exact u8166
  · exact u8167
  · exact u8168
  · exact u8169
  · exact u8170
  · exact u8171
  · exact u8172

def r9454 : Route 9 := (fun mask => (mask,id))

def c9454 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9454 : Upper (D 5) (R 5) [34,68,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9454 c9454
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8173
  · exact u8174
  · exact u8175
  · exact u8176
  · exact u8177
  · exact u8178

def r9455 : Route 9 := (fun mask => (mask,id))

def c9455 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9455 : Upper (D 5) (R 5) [34,68,129,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9455 c9455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8179
  · exact u8180
  · exact u8181
  · exact u8182
  · exact u8183
  · exact u8184

def r9456 : Route 9 := (fun mask => (mask,id))

def c9456 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9456 : Upper (D 5) (R 5) [34,68,129,260] 13 := by
  apply FastRouting.sound _ _ [34,68,129,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9456 c9456
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8185
  · exact u8186
  · exact u8187
  · exact u8188
  · exact u8189
  · exact u8190

def r9457 : Route 9 := (fun mask => (mask,id))

def c9457 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9457 : Upper (D 5) (R 5) [34,68,129,272] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9457 c9457
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8191
  · exact u8192
  · exact u8193
  · exact u8194
  · exact u8195
  · exact u8196
  · exact u8197
  · exact u8198
  · exact u8199
  · exact u8200

def r9458 : Route 9 := (fun mask => (mask,id))

def c9458 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9458 : Upper (D 5) (R 5) [34,68,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9458 c9458
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8201
  · exact u8202
  · exact u8203
  · exact u8204
  · exact u8205
  · exact u8206

theorem m9459_264 : Upper (D 5) (R 5) [34,68,130,36,264] 13 :=
  permutation_upper _ _ _ [34,68,130,36,257] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8208

def r9459 : Route 9 := (fun mask => (mask,id))

def c9459 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9459 : Upper (D 5) (R 5) [34,68,130,36] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36] 13 (by decide) (choices 2) [9,257,264] r9459 c9459
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8207
  · exact u8208
  · exact m9459_264

def r9460 : Route 9 := (fun mask => (mask,id))

def c9460 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9460 : Upper (D 5) (R 5) [34,68,130,48] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9460 c9460
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8209
  · exact u8210
  · exact u8211
  · exact u8212
  · exact u8213
  · exact u8214

def r9461 : Route 9 := (fun mask => (mask,id))

def c9461 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9461 : Upper (D 5) (R 5) [34,68,130,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,257] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9461 c9461
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8215
  · exact u8216
  · exact u8217
  · exact u8218
  · exact u8219
  · exact u8220

def r9462 : Route 9 := (fun mask => (mask,id))

def c9462 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9462 : Upper (D 5) (R 5) [34,68,130,260] 13 := by
  apply FastRouting.sound _ _ [34,68,130,260] 13 (by decide) (choices 2) [9,33,40] r9462 c9462
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8221
  · exact u8222
  · exact u8223

def r9463 : Route 9 := (fun mask => (mask,id))

def c9463 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9463 : Upper (D 5) (R 5) [34,68,130,272] 13 := by
  apply FastRouting.sound _ _ [34,68,130,272] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9463 c9463
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8224
  · exact u8225
  · exact u8226
  · exact u8227
  · exact u8228
  · exact u8229

def r9464 : Route 9 := (fun mask => (mask,id))

def c9464 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9464 : Upper (D 5) (R 5) [34,68,130,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,288] 13 (by decide) (choices 2) [5,9,12] r9464 c9464
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8230
  · exact u8231
  · exact u8232

def r9465 : Route 9 := (fun mask => (mask,id))

def c9465 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9465 : Upper (D 5) (R 5) [34,68,136,48] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9465 c9465
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8233
  · exact u8234
  · exact u8235
  · exact u8236
  · exact u8237
  · exact u8238
  · exact u8239
  · exact u8240
  · exact u8241
  · exact u8242

def r9466 : Route 9 := (fun mask => (mask,id))

def c9466 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9466 : Upper (D 5) (R 5) [34,68,136,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9466 c9466
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8243
  · exact u8244
  · exact u8245
  · exact u8246
  · exact u8247
  · exact u8248
  · exact u8249
  · exact u8250
  · exact u8251
  · exact u8252

def r9467 : Route 9 := (fun mask => (mask,id))

def c9467 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9467 : Upper (D 5) (R 5) [34,68,136,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9467 c9467
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8253
  · exact u8254
  · exact u8255
  · exact u8256
  · exact u8257
  · exact u8258

def r9468 : Route 9 := (fun mask => (mask,id))

def c9468 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9468 : Upper (D 5) (R 5) [34,68,136,260] 13 := by
  apply FastRouting.sound _ _ [34,68,136,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9468 c9468
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8259
  · exact u8260
  · exact u8261
  · exact u8262
  · exact u8263
  · exact u8264

def r9469 : Route 9 := (fun mask => (mask,id))

def c9469 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9469 : Upper (D 5) (R 5) [34,68,136,272] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9469 c9469
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8265
  · exact u8266
  · exact u8267
  · exact u8268
  · exact u8269
  · exact u8270
  · exact u8271
  · exact u8272
  · exact u8273
  · exact u8274

def r9470 : Route 9 := (fun mask => (mask,id))

def c9470 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9470 : Upper (D 5) (R 5) [34,68,136,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9470 c9470
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8275
  · exact u8276
  · exact u8277
  · exact u8278
  · exact u8279
  · exact u8280

def b9471 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 4 }], pairs := [(3,0),(3,2)], upper := (rows 35 70 148 42 285 301 333 397 269), lower := (rows 35 70 148 42 16 32 64 128 256), losses := [] }

theorem u9471 : Upper (D 5) (R 5) [34,68,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9471
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9472 : Route 9 := (fun mask => (mask,id))

def c9472 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9472 : Upper (D 5) (R 5) [34,68,144,36] 13 := by
  apply FastRouting.sound _ _ [34,68,144,36] 13 (by decide) (choices 2) [3,9,10,257,258,264] r9472 c9472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8281
  · exact u8282
  · exact u8283
  · exact u8284
  · exact u8285
  · exact u8286

def r9473 : Route 9 := (fun mask => (mask,id))

def c9473 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9473 : Upper (D 5) (R 5) [34,68,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,144,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9473 c9473
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8287
  · exact u8288
  · exact u8289
  · exact u8290
  · exact u8291
  · exact u8292
  · exact u8293
  · exact u8294
  · exact u8295
  · exact u8296

def r9474 : Route 9 := (fun mask => (mask,id))

def c9474 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9474 : Upper (D 5) (R 5) [34,68,144,258] 13 := by
  apply FastRouting.sound _ _ [34,68,144,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9474 c9474
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8297
  · exact u8298
  · exact u8299
  · exact u8300
  · exact u8301
  · exact u8302

def r9475 : Route 9 := (fun mask => (mask,id))

def c9475 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9475 : Upper (D 5) (R 5) [34,68,144,260] 13 := by
  apply FastRouting.sound _ _ [34,68,144,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9475 c9475
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8303
  · exact u8304
  · exact u8305
  · exact u8306
  · exact u8307
  · exact u8308

def r9476 : Route 9 := (fun mask => (mask,id))

def c9476 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9476 : Upper (D 5) (R 5) [34,68,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,144,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9476 c9476
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8309
  · exact u8310
  · exact u8311
  · exact u8312
  · exact u8313
  · exact u8314

def r9477 : Route 9 := (fun mask => (mask,id))

def c9477 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9477 : Upper (D 5) (R 5) [34,68,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9477 c9477
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8315
  · exact u8316
  · exact u8317
  · exact u8318
  · exact u8319
  · exact u8320

def r9478 : Route 9 := (fun mask => (mask,id))

def c9478 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9478 : Upper (D 5) (R 5) [34,68,160,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,258] 13 (by decide) (choices 2) [5,9,12] r9478 c9478
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8321
  · exact u8322
  · exact u8323

def r9479 : Route 9 := (fun mask => (mask,id))

def c9479 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9479 : Upper (D 5) (R 5) [34,68,160,260] 13 := by
  apply FastRouting.sound _ _ [34,68,160,260] 13 (by decide) (choices 2) [3,9,10] r9479 c9479
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8324
  · exact u8325
  · exact u8326

#print axioms u9479
end Delivery.IrregularNine14.P05
