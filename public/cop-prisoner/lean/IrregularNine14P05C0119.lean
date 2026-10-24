import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0060

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7140 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 69 392 21 42 106 170 298), lower := (rows 19 38 69 392 21 32 64 128 256), losses := [] }

theorem u7140 : Upper (D 5) (R 5) [18,36,65,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7140
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7141 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 69 392 22 41 105 169 297), lower := (rows 19 38 69 392 22 32 64 128 256), losses := [] }

theorem u7141 : Upper (D 5) (R 5) [18,36,65,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7141
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7142 : PairBound 9 := { available := 46, camps := [{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 38 69 392 25 46 110 174 302), lower := (rows 19 38 69 392 25 32 64 128 256), losses := [] }

theorem u7142 : Upper (D 5) (R 5) [18,36,65,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7142
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7143 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 392 26 45 109 173 301), lower := (rows 19 38 69 392 26 32 64 128 256), losses := [] }

theorem u7143 : Upper (D 5) (R 5) [18,36,65,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7143
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7144 : Route 9 := (fun mask => (mask,id))

def c7144 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7144 : Upper (D 5) (R 5) [18,36,65,384,12] 13 := by
  apply FastRouting.sound _ _ [18,36,65,384,12] 13 (by decide) (choices 1) [1,2,8] r7144 c7144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3614
  · exact u3615
  · exact u3616

def b7145 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 392 49 46 78 142 270), lower := (rows 19 38 69 392 49 32 64 128 256), losses := [] }

theorem u7145 : Upper (D 5) (R 5) [18,36,65,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7145
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7146 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 69 392 50 45 77 141 269), lower := (rows 19 38 69 392 50 32 64 128 256), losses := [] }

theorem u7146 : Upper (D 5) (R 5) [18,36,65,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7146
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7147 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 392 52 43 75 139 267), lower := (rows 19 38 69 392 52 32 64 128 256), losses := [] }

theorem u7147 : Upper (D 5) (R 5) [18,36,65,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7147
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7148 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 69 392 56 47 79 143 271), lower := (rows 19 38 69 392 56 32 64 128 256), losses := [] }

theorem u7148 : Upper (D 5) (R 5) [18,36,65,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7148
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7149 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 70 41 21 424 456 392 392), lower := (rows 19 38 70 41 21 32 64 128 256), losses := [] }

theorem u7149 : Upper (D 5) (R 5) [18,36,66,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7149
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7150 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 70 41 25 428 460 396 396), lower := (rows 19 38 70 41 25 32 64 128 256), losses := [] }

theorem u7150 : Upper (D 5) (R 5) [18,36,66,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7150
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7151 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 41 28 425 457 393 393), lower := (rows 19 38 70 41 28 32 64 128 256), losses := [] }

theorem u7151 : Upper (D 5) (R 5) [18,36,66,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7152 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 326, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 41 145 300 332 396 268), lower := (rows 19 38 70 41 145 32 64 128 256), losses := [] }

theorem u7152 : Upper (D 5) (R 5) [18,36,66,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7152
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7153 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 296, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 41 148 297 329 393 265), lower := (rows 19 38 70 41 148 32 64 128 256), losses := [] }

theorem u7153 : Upper (D 5) (R 5) [18,36,66,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7153
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7154 : Route 9 := (fun mask => (mask,id))

def c7154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7154 : Upper (D 5) (R 5) [18,36,66,33,136] 13 := by
  apply FastRouting.sound _ _ [18,36,66,33,136] 13 (by decide) (choices 1) [1,4,8,256] r7154 c7154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3617
  · exact u3618
  · exact u3619
  · exact u3620

def r7155 : Route 9 := (fun mask => (mask,id))

def c7155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7155 : Upper (D 5) (R 5) [18,36,66,33,384] 13 := by
  apply FastRouting.sound _ _ [18,36,66,33,384] 13 (by decide) (choices 1) [1,4,8] r7155 c7155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3621
  · exact u3622
  · exact u3623

def b7156 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 70 137 21 296 360 424 296), lower := (rows 19 38 70 137 21 32 64 128 256), losses := [] }

theorem u7156 : Upper (D 5) (R 5) [18,36,66,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7156
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7157 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 38 70 137 25 300 364 428 300), lower := (rows 19 38 70 137 25 32 64 128 256), losses := [] }

theorem u7157 : Upper (D 5) (R 5) [18,36,66,129,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7157
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7158 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 137 28 297 361 425 297), lower := (rows 19 38 70 137 28 32 64 128 256), losses := [] }

theorem u7158 : Upper (D 5) (R 5) [18,36,66,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7158
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7159 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 70 137 49 300 332 396 268), lower := (rows 19 38 70 137 49 32 64 128 256), losses := [] }

theorem u7159 : Upper (D 5) (R 5) [18,36,66,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7159
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7160 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 392, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 137 52 297 329 393 265), lower := (rows 19 38 70 137 52 32 64 128 256), losses := [] }

theorem u7160 : Upper (D 5) (R 5) [18,36,66,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7160
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7161 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 70 137 56 301 333 397 269), lower := (rows 19 38 70 137 56 32 64 128 256), losses := [] }

theorem u7161 : Upper (D 5) (R 5) [18,36,66,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7161
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7162 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 137 273 44 108 172 300), lower := (rows 19 38 70 137 273 32 64 128 256), losses := [] }

theorem u7162 : Upper (D 5) (R 5) [18,36,66,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7162
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7163 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 137 276 41 105 169 297), lower := (rows 19 38 70 137 276 32 64 128 256), losses := [] }

theorem u7163 : Upper (D 5) (R 5) [18,36,66,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7163
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7164 : Route 9 := (fun mask => (mask,id))

def c7164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7164 : Upper (D 5) (R 5) [18,36,66,129,264] 13 := by
  apply FastRouting.sound _ _ [18,36,66,129,264] 13 (by decide) (choices 1) [1,4,8] r7164 c7164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3624
  · exact u3625
  · exact u3626

def b7165 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 70 137 304 45 77 141 269), lower := (rows 19 38 70 137 304 32 64 128 256), losses := [] }

theorem u7165 : Upper (D 5) (R 5) [18,36,66,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7165
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7166 : Route 9 := (fun mask => (mask,id))

def c7166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7166 : Upper (D 5) (R 5) [18,36,66,132,9] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132,9] 13 (by decide) (choices 1) [1,8,256] r7166 c7166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3627
  · exact u3628
  · exact u3629

def b7167 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 70 140 49 297 329 393 265), lower := (rows 19 38 70 140 49 32 64 128 256), losses := [] }

theorem u7167 : Upper (D 5) (R 5) [18,36,66,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7167
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7168 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 70 140 56 297 329 393 265), lower := (rows 19 38 70 140 56 32 64 128 256), losses := [] }

theorem u7168 : Upper (D 5) (R 5) [18,36,66,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7168
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7169 : Route 9 := (fun mask => (mask,id))

def c7169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7169 : Upper (D 5) (R 5) [18,36,66,132,257] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132,257] 13 (by decide) (choices 1) [1,8] r7169 c7169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3630
  · exact u3631

def r7170 : Route 9 := (fun mask => (mask,id))

def c7170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7170 : Upper (D 5) (R 5) [18,36,66,132,264] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132,264] 13 (by decide) (choices 1) [1,8] r7170 c7170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3632
  · exact u3633

def b7171 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 70 140 304 41 73 137 265), lower := (rows 19 38 70 140 304 32 64 128 256), losses := [] }

theorem u7171 : Upper (D 5) (R 5) [18,36,66,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7171
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7172 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 70 168 21 297 329 393 265), lower := (rows 19 38 70 168 21 32 64 128 256), losses := [] }

theorem u7172 : Upper (D 5) (R 5) [18,36,66,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7172
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7173 : Route 9 := (fun mask => (mask,id))

def c7173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7173 : Upper (D 5) (R 5) [18,36,66,160,9] 13 := by
  apply FastRouting.sound _ _ [18,36,66,160,9] 13 (by decide) (choices 1) [1,4,8,256] r7173 c7173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3634
  · exact u3635
  · exact u3636
  · exact u3637

def b7174 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 168 28 297 329 393 265), lower := (rows 19 38 70 168 28 32 64 128 256), losses := [] }

theorem u7174 : Upper (D 5) (R 5) [18,36,66,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7174
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7175 : Route 9 := (fun mask => (mask,id))

def c7175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7175 : Upper (D 5) (R 5) [18,36,66,160,257] 13 := by
  apply FastRouting.sound _ _ [18,36,66,160,257] 13 (by decide) (choices 1) [1,4,8] r7175 c7175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3638
  · exact u3639
  · exact u3640

def b7176 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 168 276 41 73 137 265), lower := (rows 19 38 70 168 276 32 64 128 256), losses := [] }

theorem u7176 : Upper (D 5) (R 5) [18,36,66,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7176
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7177 : Route 9 := (fun mask => (mask,id))

def c7177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7177 : Upper (D 5) (R 5) [18,36,66,160,264] 13 := by
  apply FastRouting.sound _ _ [18,36,66,160,264] 13 (by decide) (choices 1) [1,4,8] r7177 c7177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3641
  · exact u3642
  · exact u3643

def b7178 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 70 392 21 41 105 169 297), lower := (rows 19 38 70 392 21 32 64 128 256), losses := [] }

theorem u7178 : Upper (D 5) (R 5) [18,36,66,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7178
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7179 : Route 9 := (fun mask => (mask,id))

def c7179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7179 : Upper (D 5) (R 5) [18,36,66,384,9] 13 := by
  apply FastRouting.sound _ _ [18,36,66,384,9] 13 (by decide) (choices 1) [1,4,8] r7179 c7179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3644
  · exact u3645
  · exact u3646

def b7180 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 392 28 41 105 169 297), lower := (rows 19 38 70 392 28 32 64 128 256), losses := [] }

theorem u7180 : Upper (D 5) (R 5) [18,36,66,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7180
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7181 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 70 392 49 45 77 141 269), lower := (rows 19 38 70 392 49 32 64 128 256), losses := [] }

theorem u7181 : Upper (D 5) (R 5) [18,36,66,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7181
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7182 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 392, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 392 52 41 73 137 265), lower := (rows 19 38 70 392 52 32 64 128 256), losses := [] }

theorem u7182 : Upper (D 5) (R 5) [18,36,66,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7182
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7183 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 70 392 56 45 77 141 269), lower := (rows 19 38 70 392 56 32 64 128 256), losses := [] }

theorem u7183 : Upper (D 5) (R 5) [18,36,66,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7183
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7184 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 41 19 428 460 396 396), lower := (rows 19 38 76 41 19 32 64 128 256), losses := [] }

theorem u7184 : Upper (D 5) (R 5) [18,36,72,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7184
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7185 : PairBound 9 := { available := 394, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 41 21 426 458 394 394), lower := (rows 19 38 76 41 21 32 64 128 256), losses := [] }

theorem u7185 : Upper (D 5) (R 5) [18,36,72,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7185
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7186 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 41 22 425 457 393 393), lower := (rows 19 38 76 41 22 32 64 128 256), losses := [] }

theorem u7186 : Upper (D 5) (R 5) [18,36,72,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7186
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7187 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 41 25 422 454 390 390), lower := (rows 19 38 76 41 25 32 64 128 256), losses := [] }

theorem u7187 : Upper (D 5) (R 5) [18,36,72,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7187
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7188 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 41 26 421 453 389 389), lower := (rows 19 38 76 41 26 32 64 128 256), losses := [] }

theorem u7188 : Upper (D 5) (R 5) [18,36,72,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7188
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7189 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 38 76 41 28 419 451 387 387), lower := (rows 19 38 76 41 28 32 64 128 256), losses := [] }

theorem u7189 : Upper (D 5) (R 5) [18,36,72,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7189
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7190 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 326, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 41 145 302 334 398 270), lower := (rows 19 38 76 41 145 32 64 128 256), losses := [] }

theorem u7190 : Upper (D 5) (R 5) [18,36,72,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7190
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7191 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 41 146 301 333 397 269), lower := (rows 19 38 76 41 146 32 64 128 256), losses := [] }

theorem u7191 : Upper (D 5) (R 5) [18,36,72,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7191
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7192 : Route 9 := (fun mask => (mask,id))

def c7192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7192 : Upper (D 5) (R 5) [18,36,72,33,132] 13 := by
  apply FastRouting.sound _ _ [18,36,72,33,132] 13 (by decide) (choices 1) [1,2,8,256] r7192 c7192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3647
  · exact u3648
  · exact u3649
  · exact u3650

def r7193 : Route 9 := (fun mask => (mask,id))

def c7193 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7193 : Upper (D 5) (R 5) [18,36,72,33,136] 13 := by
  apply FastRouting.sound _ _ [18,36,72,33,136] 13 (by decide) (choices 1) [1,2,4,256] r7193 c7193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3651
  · exact u3652
  · exact u3653
  · exact u3654

def r7194 : Route 9 := (fun mask => (mask,id))

def c7194 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7194 : Upper (D 5) (R 5) [18,36,72,33,384] 13 := by
  apply FastRouting.sound _ _ [18,36,72,33,384] 13 (by decide) (choices 1) [1,2,4,8] r7194 c7194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3655
  · exact u3656
  · exact u3657
  · exact u3658

def b7195 : PairBound 9 := { available := 300, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 137 19 300 364 428 300), lower := (rows 19 38 76 137 19 32 64 128 256), losses := [] }

theorem u7195 : Upper (D 5) (R 5) [18,36,72,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7195
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7196 : PairBound 9 := { available := 298, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 137 21 298 362 426 298), lower := (rows 19 38 76 137 21 32 64 128 256), losses := [] }

theorem u7196 : Upper (D 5) (R 5) [18,36,72,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7196
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7197 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 137 22 297 361 425 297), lower := (rows 19 38 76 137 22 32 64 128 256), losses := [] }

theorem u7197 : Upper (D 5) (R 5) [18,36,72,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7197
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7198 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 38 76 137 25 294 358 422 294), lower := (rows 19 38 76 137 25 32 64 128 256), losses := [] }

theorem u7198 : Upper (D 5) (R 5) [18,36,72,129,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7198
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7199 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 137 26 293 357 421 293), lower := (rows 19 38 76 137 26 32 64 128 256), losses := [] }

theorem u7199 : Upper (D 5) (R 5) [18,36,72,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7199
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7199
end Delivery.IrregularNine14.P05
