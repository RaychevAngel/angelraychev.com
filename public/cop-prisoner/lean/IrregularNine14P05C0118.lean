import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0059
import IrregularNine14P05C0060

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7080 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 392 26 37 101 165 293), lower := (rows 19 35 76 392 26 32 64 128 256), losses := [] }

theorem u7080 : Upper (D 5) (R 5) [18,33,72,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7080
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7081 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 35 76 392 28 39 103 167 295), lower := (rows 19 35 76 392 28 32 64 128 256), losses := [] }

theorem u7081 : Upper (D 5) (R 5) [18,33,72,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7081
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7082 : PairBound 9 := { available := 14, camps := [{ cop := 5, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 392 49 46 78 142 270), lower := (rows 19 35 76 392 49 32 64 128 256), losses := [] }

theorem u7082 : Upper (D 5) (R 5) [18,33,72,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7082
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7083 : PairBound 9 := { available := 13, camps := [{ cop := 5, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 392 50 45 77 141 269), lower := (rows 19 35 76 392 50 32 64 128 256), losses := [] }

theorem u7083 : Upper (D 5) (R 5) [18,33,72,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7083
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7084 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 392 52 47 79 143 271), lower := (rows 19 35 76 392 52 32 64 128 256), losses := [] }

theorem u7084 : Upper (D 5) (R 5) [18,33,72,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7084
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7085 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 392 56 39 71 135 263), lower := (rows 19 35 76 392 56 32 64 128 256), losses := [] }

theorem u7085 : Upper (D 5) (R 5) [18,33,72,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7085
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7086 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 100 392 19 44 76 140 268), lower := (rows 19 35 100 392 19 32 64 128 256), losses := [] }

theorem u7086 : Upper (D 5) (R 5) [18,33,96,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7086
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7087 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 100 392 21 46 78 142 270), lower := (rows 19 35 100 392 21 32 64 128 256), losses := [] }

theorem u7087 : Upper (D 5) (R 5) [18,33,96,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7087
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7088 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 100 392 22 45 77 141 269), lower := (rows 19 35 100 392 22 32 64 128 256), losses := [] }

theorem u7088 : Upper (D 5) (R 5) [18,33,96,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7088
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7089 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 100 392 25 46 78 142 270), lower := (rows 19 35 100 392 25 32 64 128 256), losses := [] }

theorem u7089 : Upper (D 5) (R 5) [18,33,96,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7089
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7090 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 100 392 26 45 77 141 269), lower := (rows 19 35 100 392 26 32 64 128 256), losses := [] }

theorem u7090 : Upper (D 5) (R 5) [18,33,96,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7090
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7091 : Route 9 := (fun mask => (mask,id))

def c7091 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7091 : Upper (D 5) (R 5) [18,33,96,384,12] 13 := by
  apply FastRouting.sound _ _ [18,33,96,384,12] 13 (by decide) (choices 1) [1,2,4,8] r7091 c7091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3573
  · exact u3574
  · exact u3575
  · exact u3576

def b7092 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 69 41 22 424 456 392 392), lower := (rows 19 38 69 41 22 32 64 128 256), losses := [] }

theorem u7092 : Upper (D 5) (R 5) [18,36,65,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7092
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7093 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 69 41 26 428 460 396 396), lower := (rows 19 38 69 41 26 32 64 128 256), losses := [] }

theorem u7093 : Upper (D 5) (R 5) [18,36,65,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7093
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7094 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 424, targets := 4 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 38 69 41 28 426 458 394 394), lower := (rows 19 38 69 41 28 32 64 128 256), losses := [] }

theorem u7094 : Upper (D 5) (R 5) [18,36,65,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7094
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7095 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 41 146 300 332 396 268), lower := (rows 19 38 69 41 146 32 64 128 256), losses := [] }

theorem u7095 : Upper (D 5) (R 5) [18,36,65,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7095
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7096 : Route 9 := (fun mask => (mask,id))

def c7096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7096 : Upper (D 5) (R 5) [18,36,65,33,132] 13 := by
  apply FastRouting.sound _ _ [18,36,65,33,132] 13 (by decide) (choices 1) [2,8,256] r7096 c7096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3577
  · exact u3578
  · exact u3579

def r7097 : Route 9 := (fun mask => (mask,id))

def c7097 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7097 : Upper (D 5) (R 5) [18,36,65,33,136] 13 := by
  apply FastRouting.sound _ _ [18,36,65,33,136] 13 (by decide) (choices 1) [2,4,8,256] r7097 c7097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3580
  · exact u3581
  · exact u3582
  · exact u3583

def r7098 : Route 9 := (fun mask => (mask,id))

def c7098 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7098 : Upper (D 5) (R 5) [18,36,65,33,384] 13 := by
  apply FastRouting.sound _ _ [18,36,65,33,384] 13 (by decide) (choices 1) [2,4,8] r7098 c7098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3584
  · exact u3585
  · exact u3586

def b7099 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 69 137 22 296 360 424 296), lower := (rows 19 38 69 137 22 32 64 128 256), losses := [] }

theorem u7099 : Upper (D 5) (R 5) [18,36,65,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7099
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7100 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 137 26 300 364 428 300), lower := (rows 19 38 69 137 26 32 64 128 256), losses := [] }

theorem u7100 : Upper (D 5) (R 5) [18,36,65,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7100
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7101 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 424, targets := 4 },{ cop := 4, region := 290, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 38 69 137 28 298 362 426 298), lower := (rows 19 38 69 137 28 32 64 128 256), losses := [] }

theorem u7101 : Upper (D 5) (R 5) [18,36,65,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7101
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7102 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 137 50 300 332 396 268), lower := (rows 19 38 69 137 50 32 64 128 256), losses := [] }

theorem u7102 : Upper (D 5) (R 5) [18,36,65,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7102
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7103 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 137 52 298 330 394 266), lower := (rows 19 38 69 137 52 32 64 128 256), losses := [] }

theorem u7103 : Upper (D 5) (R 5) [18,36,65,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7103
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7104 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 137 56 302 334 398 270), lower := (rows 19 38 69 137 56 32 64 128 256), losses := [] }

theorem u7104 : Upper (D 5) (R 5) [18,36,65,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7104
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7105 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 137 274 44 108 172 300), lower := (rows 19 38 69 137 274 32 64 128 256), losses := [] }

theorem u7105 : Upper (D 5) (R 5) [18,36,65,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7105
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7106 : Route 9 := (fun mask => (mask,id))

def c7106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7106 : Upper (D 5) (R 5) [18,36,65,129,260] 13 := by
  apply FastRouting.sound _ _ [18,36,65,129,260] 13 (by decide) (choices 1) [2,8] r7106 c7106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3587
  · exact u3588

def r7107 : Route 9 := (fun mask => (mask,id))

def c7107 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7107 : Upper (D 5) (R 5) [18,36,65,129,264] 13 := by
  apply FastRouting.sound _ _ [18,36,65,129,264] 13 (by decide) (choices 1) [2,4,8] r7107 c7107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3589
  · exact u3590
  · exact u3591

def b7108 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 137 304 46 78 142 270), lower := (rows 19 38 69 137 304 32 64 128 256), losses := [] }

theorem u7108 : Upper (D 5) (R 5) [18,36,65,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7108
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7109 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 69 138 21 296 360 424 296), lower := (rows 19 38 69 138 21 32 64 128 256), losses := [] }

theorem u7109 : Upper (D 5) (R 5) [18,36,65,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7109
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7110 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 38 69 138 25 300 364 428 300), lower := (rows 19 38 69 138 25 32 64 128 256), losses := [] }

theorem u7110 : Upper (D 5) (R 5) [18,36,65,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7110
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7111 : Route 9 := (fun mask => (mask,id))

def c7111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7111 : Upper (D 5) (R 5) [18,36,65,130,12] 13 := by
  apply FastRouting.sound _ _ [18,36,65,130,12] 13 (by decide) (choices 1) [1,8,256] r7111 c7111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3592
  · exact u3593
  · exact u3594

def b7112 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 138 49 300 332 396 268), lower := (rows 19 38 69 138 49 32 64 128 256), losses := [] }

theorem u7112 : Upper (D 5) (R 5) [18,36,65,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7112
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7113 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 138 52 297 329 393 265), lower := (rows 19 38 69 138 52 32 64 128 256), losses := [] }

theorem u7113 : Upper (D 5) (R 5) [18,36,65,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7113
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7114 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 138 56 301 333 397 269), lower := (rows 19 38 69 138 56 32 64 128 256), losses := [] }

theorem u7114 : Upper (D 5) (R 5) [18,36,65,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7114
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7115 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 170, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 38 69 138 273 44 108 172 300), lower := (rows 19 38 69 138 273 32 64 128 256), losses := [] }

theorem u7115 : Upper (D 5) (R 5) [18,36,65,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7115
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7116 : Route 9 := (fun mask => (mask,id))

def c7116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7116 : Upper (D 5) (R 5) [18,36,65,130,260] 13 := by
  apply FastRouting.sound _ _ [18,36,65,130,260] 13 (by decide) (choices 1) [1,8] r7116 c7116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3595
  · exact u3596

def r7117 : Route 9 := (fun mask => (mask,id))

def c7117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7117 : Upper (D 5) (R 5) [18,36,65,130,264] 13 := by
  apply FastRouting.sound _ _ [18,36,65,130,264] 13 (by decide) (choices 1) [1,4,8] r7117 c7117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3597
  · exact u3598
  · exact u3599

def b7118 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 138 304 45 77 141 269), lower := (rows 19 38 69 138 304 32 64 128 256), losses := [] }

theorem u7118 : Upper (D 5) (R 5) [18,36,65,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7118
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7119 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 140 19 296 360 424 296), lower := (rows 19 38 69 140 19 32 64 128 256), losses := [] }

theorem u7119 : Upper (D 5) (R 5) [18,36,65,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7119
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7120 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 38 69 140 25 298 362 426 298), lower := (rows 19 38 69 140 25 32 64 128 256), losses := [] }

theorem u7120 : Upper (D 5) (R 5) [18,36,65,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7120
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7121 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 38 69 140 26 297 361 425 297), lower := (rows 19 38 69 140 26 32 64 128 256), losses := [] }

theorem u7121 : Upper (D 5) (R 5) [18,36,65,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7122 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 140 49 298 330 394 266), lower := (rows 19 38 69 140 49 32 64 128 256), losses := [] }

theorem u7122 : Upper (D 5) (R 5) [18,36,65,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7123 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 140 50 297 329 393 265), lower := (rows 19 38 69 140 50 32 64 128 256), losses := [] }

theorem u7123 : Upper (D 5) (R 5) [18,36,65,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7123
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7124 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 140 56 299 331 395 267), lower := (rows 19 38 69 140 56 32 64 128 256), losses := [] }

theorem u7124 : Upper (D 5) (R 5) [18,36,65,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7124
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7125 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 170, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 38 69 140 273 42 106 170 298), lower := (rows 19 38 69 140 273 32 64 128 256), losses := [] }

theorem u7125 : Upper (D 5) (R 5) [18,36,65,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7125
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7126 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 140 274 41 105 169 297), lower := (rows 19 38 69 140 274 32 64 128 256), losses := [] }

theorem u7126 : Upper (D 5) (R 5) [18,36,65,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7126
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7127 : Route 9 := (fun mask => (mask,id))

def c7127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7127 : Upper (D 5) (R 5) [18,36,65,132,264] 13 := by
  apply FastRouting.sound _ _ [18,36,65,132,264] 13 (by decide) (choices 1) [1,2,8] r7127 c7127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3600
  · exact u3601
  · exact u3602

def b7128 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 140 304 43 75 139 267), lower := (rows 19 38 69 140 304 32 64 128 256), losses := [] }

theorem u7128 : Upper (D 5) (R 5) [18,36,65,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7129 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 168 19 300 332 396 268), lower := (rows 19 38 69 168 19 32 64 128 256), losses := [] }

theorem u7129 : Upper (D 5) (R 5) [18,36,65,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7130 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 69 168 21 298 330 394 266), lower := (rows 19 38 69 168 21 32 64 128 256), losses := [] }

theorem u7130 : Upper (D 5) (R 5) [18,36,65,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7130
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7131 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 69 168 22 297 329 393 265), lower := (rows 19 38 69 168 22 32 64 128 256), losses := [] }

theorem u7131 : Upper (D 5) (R 5) [18,36,65,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7131
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7132 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 38 69 168 25 302 334 398 270), lower := (rows 19 38 69 168 25 32 64 128 256), losses := [] }

theorem u7132 : Upper (D 5) (R 5) [18,36,65,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7132
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7133 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 38 69 168 26 301 333 397 269), lower := (rows 19 38 69 168 26 32 64 128 256), losses := [] }

theorem u7133 : Upper (D 5) (R 5) [18,36,65,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7133
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7134 : Route 9 := (fun mask => (mask,id))

def c7134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7134 : Upper (D 5) (R 5) [18,36,65,160,12] 13 := by
  apply FastRouting.sound _ _ [18,36,65,160,12] 13 (by decide) (choices 1) [1,2,8,256] r7134 c7134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3603
  · exact u3604
  · exact u3605
  · exact u3606

def b7135 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 170, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 38 69 168 273 46 78 142 270), lower := (rows 19 38 69 168 273 32 64 128 256), losses := [] }

theorem u7135 : Upper (D 5) (R 5) [18,36,65,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7135
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7136 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 168 274 45 77 141 269), lower := (rows 19 38 69 168 274 32 64 128 256), losses := [] }

theorem u7136 : Upper (D 5) (R 5) [18,36,65,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7136
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7137 : Route 9 := (fun mask => (mask,id))

def c7137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7137 : Upper (D 5) (R 5) [18,36,65,160,260] 13 := by
  apply FastRouting.sound _ _ [18,36,65,160,260] 13 (by decide) (choices 1) [1,2,8] r7137 c7137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3607
  · exact u3608
  · exact u3609

def r7138 : Route 9 := (fun mask => (mask,id))

def c7138 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7138 : Upper (D 5) (R 5) [18,36,65,160,264] 13 := by
  apply FastRouting.sound _ _ [18,36,65,160,264] 13 (by decide) (choices 1) [1,2,4,8] r7138 c7138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3610
  · exact u3611
  · exact u3612
  · exact u3613

def b7139 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 392 19 44 108 172 300), lower := (rows 19 38 69 392 19 32 64 128 256), losses := [] }

theorem u7139 : Upper (D 5) (R 5) [18,36,65,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7139
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7139
end Delivery.IrregularNine14.P05
