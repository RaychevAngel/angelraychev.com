import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0059
import IrregularNine14P01C0060

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7080 : PairBound 9 := { available := 434, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 53 194 14 73 434 434 498 434 434), lower := (rows 53 194 14 73 16 32 64 128 256), losses := [] }

theorem u7080 : Upper (D 1) (R 1) [52,192,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7080
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7081 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 53 194 14 74 433 433 497 433 433), lower := (rows 53 194 14 74 16 32 64 128 256), losses := [] }

theorem u7081 : Upper (D 1) (R 1) [52,192,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7081
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7082 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 14 88 435 419 483 419 419), lower := (rows 53 194 14 88 16 32 64 128 256), losses := [] }

theorem u7082 : Upper (D 1) (R 1) [52,192,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7082
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7083 : PairBound 9 := { available := 307, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 53 194 14 200 307 307 371 435 307), lower := (rows 53 194 14 200 16 32 64 128 256), losses := [] }

theorem u7083 : Upper (D 1) (R 1) [52,192,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7083
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7084 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7084 : Upper (D 1) (R 1) [52,192,10,257] 13 := by
  apply FastRouting.sound _ _ [52,192,10,257] 13 (by decide) (choices 1) [2,32,64] r7084 c7084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3540
  · exact u3541
  · exact u3542

def b7085 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 194 14 266 241 241 241 241 497), lower := (rows 53 194 14 266 16 32 64 128 256), losses := [] }

theorem u7085 : Upper (D 1) (R 1) [52,192,10,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7085
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7086 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 14 280 243 227 227 227 483), lower := (rows 53 194 14 280 16 32 64 128 256), losses := [] }

theorem u7086 : Upper (D 1) (R 1) [52,192,10,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7086
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7087 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 194 14 328 179 179 243 179 435), lower := (rows 53 194 14 328 16 32 64 128 256), losses := [] }

theorem u7087 : Upper (D 1) (R 1) [52,192,10,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7087
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7088 : PairBound 9 := { available := 434, camps := [], pairs := [(0,6)], upper := (rows 53 194 76 11 434 434 498 434 434), lower := (rows 53 194 76 11 16 32 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 26 42 0 138 266), good := (rows 53 434 445 443 16 32 0 128 256) }] }

theorem u7088 : Upper (D 1) (R 1) [52,192,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7088
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7089 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 76 25 434 418 482 418 418), lower := (rows 53 194 76 25 16 32 64 128 256), losses := [] }

theorem u7089 : Upper (D 1) (R 1) [52,192,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7089
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7090 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 76 26 435 419 483 419 419), lower := (rows 53 194 76 26 16 32 64 128 256), losses := [] }

theorem u7090 : Upper (D 1) (R 1) [52,192,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7090
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7091 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 76 56 403 419 451 387 387), lower := (rows 53 194 76 56 16 32 64 128 256), losses := [] }

theorem u7091 : Upper (D 1) (R 1) [52,192,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7091
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7092 : Route 9 := (fun mask => (mask,id))

def c7092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7092 : Upper (D 1) (R 1) [52,192,72,129] 13 := by
  apply FastRouting.sound _ _ [52,192,72,129] 13 (by decide) (choices 1) [2,32,256] r7092 c7092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3543
  · exact u3544
  · exact u3545

def b7093 : PairBound 9 := { available := 307, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 53 194 76 138 307 307 371 435 307), lower := (rows 53 194 76 138 16 32 64 128 256), losses := [] }

theorem u7093 : Upper (D 1) (R 1) [52,192,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7093
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7094 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 76 152 307 291 355 419 291), lower := (rows 53 194 76 152 16 32 64 128 256), losses := [] }

theorem u7094 : Upper (D 1) (R 1) [52,192,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7094
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7095 : Route 9 := (fun mask => (mask,id))

def c7095 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7095 : Upper (D 1) (R 1) [52,192,72,257] 13 := by
  apply FastRouting.sound _ _ [52,192,72,257] 13 (by decide) (choices 1) [2,32,128] r7095 c7095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3546
  · exact u3547
  · exact u3548

def r7096 : Route 9 := (fun mask => (mask,id))

def c7096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7096 : Upper (D 1) (R 1) [52,192,72,258] 13 := by
  apply FastRouting.sound _ _ [52,192,72,258] 13 (by decide) (choices 1) [1,2,32,128] r7096 c7096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3549
  · exact u3550
  · exact u3551
  · exact u3552

def b7097 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 76 280 179 163 227 163 419), lower := (rows 53 194 76 280 16 32 64 128 256), losses := [] }

theorem u7097 : Upper (D 1) (R 1) [52,192,72,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7097
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7098 : Route 9 := (fun mask => (mask,id))

def c7098 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7098 : Upper (D 1) (R 1) [52,192,72,384] 13 := by
  apply FastRouting.sound _ _ [52,192,72,384] 13 (by decide) (choices 1) [1,2,32] r7098 c7098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3553
  · exact u3554
  · exact u3555

def b7099 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 261 26 250 234 234 234 490), lower := (rows 53 194 261 26 16 32 64 128 256), losses := [] }

theorem u7099 : Upper (D 1) (R 1) [52,192,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7099
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7100 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 261 56 218 234 202 202 458), lower := (rows 53 194 261 56 16 32 64 128 256), losses := [] }

theorem u7100 : Upper (D 1) (R 1) [52,192,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7100
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7101 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 261 74 186 186 250 186 442), lower := (rows 53 194 261 74 16 32 64 128 256), losses := [] }

theorem u7101 : Upper (D 1) (R 1) [52,192,257,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7101
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7102 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 162, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 261 88 186 170 234 170 426), lower := (rows 53 194 261 88 16 32 64 128 256), losses := [] }

theorem u7102 : Upper (D 1) (R 1) [52,192,257,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7102
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7103 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 261 200 58 58 122 186 314), lower := (rows 53 194 261 200 16 32 64 128 256), losses := [] }

theorem u7103 : Upper (D 1) (R 1) [52,192,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7103
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7104 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7104 : Upper (D 1) (R 1) [52,192,258,3] 13 := by
  apply FastRouting.sound _ _ [52,192,258,3] 13 (by decide) (choices 1) [8,32,64] r7104 c7104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3556
  · exact u3557
  · exact u3558

def b7105 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 262 25 250 234 234 234 490), lower := (rows 53 194 262 25 16 32 64 128 256), losses := [] }

theorem u7105 : Upper (D 1) (R 1) [52,192,258,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7105
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7106 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7106 : Upper (D 1) (R 1) [52,192,258,18] 13 := by
  apply FastRouting.sound _ _ [52,192,258,18] 13 (by decide) (choices 1) [1,8,32,64] r7106 c7106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3559
  · exact u3560
  · exact u3561
  · exact u3562

def b7107 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 262 56 219 235 203 203 459), lower := (rows 53 194 262 56 16 32 64 128 256), losses := [] }

theorem u7107 : Upper (D 1) (R 1) [52,192,258,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7107
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7108 : Route 9 := (fun mask => (mask,id))

def c7108 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7108 : Upper (D 1) (R 1) [52,192,258,65] 13 := by
  apply FastRouting.sound _ _ [52,192,258,65] 13 (by decide) (choices 1) [2,8,32,128] r7108 c7108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3563
  · exact u3564
  · exact u3565
  · exact u3566

def b7109 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 262 74 185 185 249 185 441), lower := (rows 53 194 262 74 16 32 64 128 256), losses := [] }

theorem u7109 : Upper (D 1) (R 1) [52,192,258,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7109
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7110 : Route 9 := (fun mask => (mask,id))

def c7110 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7110 : Upper (D 1) (R 1) [52,192,258,80] 13 := by
  apply FastRouting.sound _ _ [52,192,258,80] 13 (by decide) (choices 1) [1,2,8,32,128] r7110 c7110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3567
  · exact u3568
  · exact u3569
  · exact u3570
  · exact u3571

def b7111 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 262 200 59 59 123 187 315), lower := (rows 53 194 262 200 16 32 64 128 256), losses := [] }

theorem u7111 : Upper (D 1) (R 1) [52,192,258,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7112 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7112 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7112 : Upper (D 1) (R 1) [52,192,264,3] 13 := by
  apply FastRouting.sound _ _ [52,192,264,3] 13 (by decide) (choices 1) [2,32,64] r7112 c7112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3572
  · exact u3573
  · exact u3574

def b7113 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 268 25 242 226 226 226 482), lower := (rows 53 194 268 25 16 32 64 128 256), losses := [] }

theorem u7113 : Upper (D 1) (R 1) [52,192,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7114 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 268 26 243 227 227 227 483), lower := (rows 53 194 268 26 16 32 64 128 256), losses := [] }

theorem u7114 : Upper (D 1) (R 1) [52,192,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7114
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7115 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 268 56 211 227 195 195 451), lower := (rows 53 194 268 56 16 32 64 128 256), losses := [] }

theorem u7115 : Upper (D 1) (R 1) [52,192,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7115
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7116 : Route 9 := (fun mask => (mask,id))

def c7116 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7116 : Upper (D 1) (R 1) [52,192,264,65] 13 := by
  apply FastRouting.sound _ _ [52,192,264,65] 13 (by decide) (choices 1) [2,32,128] r7116 c7116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3575
  · exact u3576
  · exact u3577

def b7117 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 268 74 179 179 243 179 435), lower := (rows 53 194 268 74 16 32 64 128 256), losses := [] }

theorem u7117 : Upper (D 1) (R 1) [52,192,264,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7117
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7118 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 268 88 179 163 227 163 419), lower := (rows 53 194 268 88 16 32 64 128 256), losses := [] }

theorem u7118 : Upper (D 1) (R 1) [52,192,264,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7118
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7119 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 268 200 51 51 115 179 307), lower := (rows 53 194 268 200 16 32 64 128 256), losses := [] }

theorem u7119 : Upper (D 1) (R 1) [52,192,264,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7119
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7120 : Route 9 := (fun mask => (mask,id))

def c7120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7120 : Upper (D 1) (R 1) [52,192,320,3] 13 := by
  apply FastRouting.sound _ _ [52,192,320,3] 13 (by decide) (choices 1) [2,8,32,128] r7120 c7120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3578
  · exact u3579
  · exact u3580
  · exact u3581

def b7121 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 324 25 186 170 234 170 426), lower := (rows 53 194 324 25 16 32 64 128 256), losses := [] }

theorem u7121 : Upper (D 1) (R 1) [52,192,320,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7121
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7122 : Route 9 := (fun mask => (mask,id))

def c7122 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7122 : Upper (D 1) (R 1) [52,192,320,18] 13 := by
  apply FastRouting.sound _ _ [52,192,320,18] 13 (by decide) (choices 1) [1,2,8,32,128] r7122 c7122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3582
  · exact u3583
  · exact u3584
  · exact u3585
  · exact u3586

def b7123 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 324 56 155 171 203 139 395), lower := (rows 53 194 324 56 16 32 64 128 256), losses := [] }

theorem u7123 : Upper (D 1) (R 1) [52,192,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7123
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7124 : Route 9 := (fun mask => (mask,id))

def c7124 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7124 : Upper (D 1) (R 1) [52,192,320,129] 13 := by
  apply FastRouting.sound _ _ [52,192,320,129] 13 (by decide) (choices 1) [2,8,32] r7124 c7124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3587
  · exact u3588
  · exact u3589

def b7125 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 324 138 59 59 123 187 315), lower := (rows 53 194 324 138 16 32 64 128 256), losses := [] }

theorem u7125 : Upper (D 1) (R 1) [52,192,320,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7125
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7126 : Route 9 := (fun mask => (mask,id))

def c7126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7126 : Upper (D 1) (R 1) [52,192,320,144] 13 := by
  apply FastRouting.sound _ _ [52,192,320,144] 13 (by decide) (choices 1) [1,2,8,32] r7126 c7126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3590
  · exact u3591
  · exact u3592
  · exact u3593

def b7127 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 53 259 14 26 240 224 224 224 480), lower := (rows 53 259 14 26 16 32 64 128 256), losses := [] }

theorem u7127 : Upper (D 1) (R 1) [52,257,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7127
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7128 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 14 56 210 226 194 194 450), lower := (rows 53 259 14 56 16 32 64 128 256), losses := [] }

theorem u7128 : Upper (D 1) (R 1) [52,257,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7128
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7129 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 259 14 74 240 240 240 240 496), lower := (rows 53 259 14 74 16 32 64 128 256), losses := [] }

theorem u7129 : Upper (D 1) (R 1) [52,257,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7129
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7130 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 259 14 88 242 226 226 226 482), lower := (rows 53 259 14 88 16 32 64 128 256), losses := [] }

theorem u7130 : Upper (D 1) (R 1) [52,257,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7130
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7131 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7131 : Upper (D 1) (R 1) [52,257,10,192] 13 := by
  apply FastRouting.sound _ _ [52,257,10,192] 13 (by decide) (choices 1) [2,32,64] r7131 c7131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3594
  · exact u3595
  · exact u3596

def b7132 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 53 259 70 26 248 232 232 232 488), lower := (rows 53 259 70 26 16 32 64 128 256), losses := [] }

theorem u7132 : Upper (D 1) (R 1) [52,257,66,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7132
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7133 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 70 56 218 234 202 202 458), lower := (rows 53 259 70 56 16 32 64 128 256), losses := [] }

theorem u7133 : Upper (D 1) (R 1) [52,257,66,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7133
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7134 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 259 70 74 184 184 248 184 440), lower := (rows 53 259 70 74 16 32 64 128 256), losses := [] }

theorem u7134 : Upper (D 1) (R 1) [52,257,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7134
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7135 : Route 9 := (fun mask => (mask,id))

def c7135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7135 : Upper (D 1) (R 1) [52,257,66,80] 13 := by
  apply FastRouting.sound _ _ [52,257,66,80] 13 (by decide) (choices 1) [2,8,32,128] r7135 c7135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3597
  · exact u3598
  · exact u3599
  · exact u3600

def r7136 : Route 9 := (fun mask => (mask,id))

def c7136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7136 : Upper (D 1) (R 1) [52,257,66,130] 13 := by
  apply FastRouting.sound _ _ [52,257,66,130] 13 (by decide) (choices 1) [8,32,64,128] r7136 c7136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3601
  · exact u3602
  · exact u3603
  · exact u3604

def r7137 : Route 9 := (fun mask => (mask,id))

def c7137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7137 : Upper (D 1) (R 1) [52,257,66,144] 13 := by
  apply FastRouting.sound _ _ [52,257,66,144] 13 (by decide) (choices 1) [2,8,32,64,128] r7137 c7137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3605
  · exact u3606
  · exact u3607
  · exact u3608
  · exact u3609

def r7138 : Route 9 := (fun mask => (mask,id))

def c7138 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7138 : Upper (D 1) (R 1) [52,257,66,192] 13 := by
  apply FastRouting.sound _ _ [52,257,66,192] 13 (by decide) (choices 1) [2,8,32,128] r7138 c7138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3610
  · exact u3611
  · exact u3612
  · exact u3613

def b7139 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 259 76 26 242 226 226 226 482), lower := (rows 53 259 76 26 16 32 64 128 256), losses := [] }

theorem u7139 : Upper (D 1) (R 1) [52,257,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7139
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7139
end Delivery.IrregularNine14.P01
