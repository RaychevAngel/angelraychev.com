import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0060
import IrregularNine14P01C0061

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7140 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 76 56 210 226 194 194 450), lower := (rows 53 259 76 56 16 32 64 128 256), losses := [] }

theorem u7140 : Upper (D 1) (R 1) [52,257,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7140
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7141 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 259 76 74 178 178 242 178 434), lower := (rows 53 259 76 74 16 32 64 128 256), losses := [] }

theorem u7141 : Upper (D 1) (R 1) [52,257,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7141
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7142 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 259 76 88 178 162 226 162 418), lower := (rows 53 259 76 88 16 32 64 128 256), losses := [] }

theorem u7142 : Upper (D 1) (R 1) [52,257,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7142
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7143 : Route 9 := (fun mask => (mask,id))

def c7143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7143 : Upper (D 1) (R 1) [52,257,72,130] 13 := by
  apply FastRouting.sound _ _ [52,257,72,130] 13 (by decide) (choices 1) [2,32,64,128] r7143 c7143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3614
  · exact u3615
  · exact u3616
  · exact u3617

def b7144 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 259 76 152 242 226 226 226 482), lower := (rows 53 259 76 152 16 32 64 128 256), losses := [] }

theorem u7144 : Upper (D 1) (R 1) [52,257,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7144
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7145 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 259 76 200 178 178 242 178 434), lower := (rows 53 259 76 200 16 32 64 128 256), losses := [] }

theorem u7145 : Upper (D 1) (R 1) [52,257,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7145
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7146 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 53 259 196 26 250 234 234 234 490), lower := (rows 53 259 196 26 16 32 64 128 256), losses := [] }

theorem u7146 : Upper (D 1) (R 1) [52,257,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7146
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7147 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 196 56 218 234 202 202 458), lower := (rows 53 259 196 56 16 32 64 128 256), losses := [] }

theorem u7147 : Upper (D 1) (R 1) [52,257,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7147
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7148 : Route 9 := (fun mask => (mask,id))

def c7148 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7148 : Upper (D 1) (R 1) [52,257,192,66] 13 := by
  apply FastRouting.sound _ _ [52,257,192,66] 13 (by decide) (choices 1) [2,8,32,128] r7148 c7148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3618
  · exact u3619
  · exact u3620
  · exact u3621

def r7149 : Route 9 := (fun mask => (mask,id))

def c7149 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7149 : Upper (D 1) (R 1) [52,257,192,80] 13 := by
  apply FastRouting.sound _ _ [52,257,192,80] 13 (by decide) (choices 1) [2,8,32,128] r7149 c7149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3622
  · exact u3623
  · exact u3624
  · exact u3625

def b7150 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 196 200 58 58 122 186 314), lower := (rows 53 259 196 200 16 32 64 128 256), losses := [] }

theorem u7150 : Upper (D 1) (R 1) [52,257,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7150
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7151 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 53 266 7 26 240 224 224 224 480), lower := (rows 53 266 7 26 16 32 64 128 256), losses := [] }

theorem u7151 : Upper (D 1) (R 1) [52,264,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7151
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7152 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 7 56 210 226 194 194 450), lower := (rows 53 266 7 56 16 32 64 128 256), losses := [] }

theorem u7152 : Upper (D 1) (R 1) [52,264,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7152
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7153 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 53 266 7 74 240 240 240 240 496), lower := (rows 53 266 7 74 16 32 64 128 256), losses := [] }

theorem u7153 : Upper (D 1) (R 1) [52,264,3,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7153
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7154 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 53 266 7 88 242 226 226 226 482), lower := (rows 53 266 7 88 16 32 64 128 256), losses := [] }

theorem u7154 : Upper (D 1) (R 1) [52,264,3,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7154
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7155 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7155 : Upper (D 1) (R 1) [52,264,3,192] 13 := by
  apply FastRouting.sound _ _ [52,264,3,192] 13 (by decide) (choices 1) [2,32,64] r7155 c7155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3626
  · exact u3627
  · exact u3628

def b7156 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 53 266 69 26 242 226 226 226 482), lower := (rows 53 266 69 26 16 32 64 128 256), losses := [] }

theorem u7156 : Upper (D 1) (R 1) [52,264,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7156
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7157 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 69 56 210 226 194 194 450), lower := (rows 53 266 69 56 16 32 64 128 256), losses := [] }

theorem u7157 : Upper (D 1) (R 1) [52,264,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7157
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7158 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 69 74 178 178 242 178 434), lower := (rows 53 266 69 74 16 32 64 128 256), losses := [] }

theorem u7158 : Upper (D 1) (R 1) [52,264,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7158
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7159 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 53 266 69 88 178 162 226 162 418), lower := (rows 53 266 69 88 16 32 64 128 256), losses := [] }

theorem u7159 : Upper (D 1) (R 1) [52,264,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7159
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7160 : Route 9 := (fun mask => (mask,id))

def c7160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7160 : Upper (D 1) (R 1) [52,264,65,130] 13 := by
  apply FastRouting.sound _ _ [52,264,65,130] 13 (by decide) (choices 1) [2,32,64,128] r7160 c7160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3629
  · exact u3630
  · exact u3631
  · exact u3632

def b7161 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 354, targets := 16 }], pairs := [(1,4)], upper := (rows 53 266 69 152 242 226 226 226 482), lower := (rows 53 266 69 152 16 32 64 128 256), losses := [] }

theorem u7161 : Upper (D 1) (R 1) [52,264,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7161
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7162 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 69 200 178 178 242 178 434), lower := (rows 53 266 69 200 16 32 64 128 256), losses := [] }

theorem u7162 : Upper (D 1) (R 1) [52,264,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7162
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7163 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1)], upper := (rows 53 266 70 11 240 240 240 240 496), lower := (rows 53 266 70 11 16 32 64 128 256), losses := [] }

theorem u7163 : Upper (D 1) (R 1) [52,264,66,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7163
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7164 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 70 25 242 226 226 226 482), lower := (rows 53 266 70 25 16 32 64 128 256), losses := [] }

theorem u7164 : Upper (D 1) (R 1) [52,264,66,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7164
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7165 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1)], upper := (rows 53 266 70 26 241 225 225 225 481), lower := (rows 53 266 70 26 16 32 64 128 256), losses := [] }

theorem u7165 : Upper (D 1) (R 1) [52,264,66,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7165
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7166 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 70 56 211 227 195 195 451), lower := (rows 53 266 70 56 16 32 64 128 256), losses := [] }

theorem u7166 : Upper (D 1) (R 1) [52,264,66,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7166
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7167 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 266 70 73 178 178 242 178 434), lower := (rows 53 266 70 73 16 32 64 128 256), losses := [] }

theorem u7167 : Upper (D 1) (R 1) [52,264,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7167
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7168 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 266 70 74 177 177 241 177 433), lower := (rows 53 266 70 74 16 32 64 128 256), losses := [] }

theorem u7168 : Upper (D 1) (R 1) [52,264,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7168
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7169 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 266 70 88 179 163 227 163 419), lower := (rows 53 266 70 88 16 32 64 128 256), losses := [] }

theorem u7169 : Upper (D 1) (R 1) [52,264,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7170 : Route 9 := (fun mask => (mask,id))

def c7170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7170 : Upper (D 1) (R 1) [52,264,66,129] 13 := by
  apply FastRouting.sound _ _ [52,264,66,129] 13 (by decide) (choices 1) [2,32,64,128] r7170 c7170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3633
  · exact u3634
  · exact u3635
  · exact u3636

def b7171 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1)], upper := (rows 53 266 70 138 241 241 241 241 497), lower := (rows 53 266 70 138 16 32 64 128 256), losses := [] }

theorem u7171 : Upper (D 1) (R 1) [52,264,66,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7171
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7172 : Route 9 := (fun mask => (mask,id))

def c7172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7172 : Upper (D 1) (R 1) [52,264,66,144] 13 := by
  apply FastRouting.sound _ _ [52,264,66,144] 13 (by decide) (choices 1) [1,2,32,64,128] r7172 c7172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3637
  · exact u3638
  · exact u3639
  · exact u3640
  · exact u3641

def b7173 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 266 70 200 179 179 243 179 435), lower := (rows 53 266 70 200 16 32 64 128 256), losses := [] }

theorem u7173 : Upper (D 1) (R 1) [52,264,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7173
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7174 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7174 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7174 : Upper (D 1) (R 1) [52,264,192,3] 13 := by
  apply FastRouting.sound _ _ [52,264,192,3] 13 (by decide) (choices 1) [2,32,64] r7174 c7174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3642
  · exact u3643
  · exact u3644

def b7175 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 196 25 242 226 226 226 482), lower := (rows 53 266 196 25 16 32 64 128 256), losses := [] }

theorem u7175 : Upper (D 1) (R 1) [52,264,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7175
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7176 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7176 : Upper (D 1) (R 1) [52,264,192,18] 13 := by
  apply FastRouting.sound _ _ [52,264,192,18] 13 (by decide) (choices 1) [1,2,32,64] r7176 c7176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3645
  · exact u3646
  · exact u3647
  · exact u3648

def b7177 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 196 56 211 227 195 195 451), lower := (rows 53 266 196 56 16 32 64 128 256), losses := [] }

theorem u7177 : Upper (D 1) (R 1) [52,264,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7177
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7178 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 196 73 178 178 242 178 434), lower := (rows 53 266 196 73 16 32 64 128 256), losses := [] }

theorem u7178 : Upper (D 1) (R 1) [52,264,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7178
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7179 : Route 9 := (fun mask => (mask,id))

def c7179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7179 : Upper (D 1) (R 1) [52,264,192,66] 13 := by
  apply FastRouting.sound _ _ [52,264,192,66] 13 (by decide) (choices 1) [1,2,32,128] r7179 c7179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3649
  · exact u3650
  · exact u3651
  · exact u3652

def r7180 : Route 9 := (fun mask => (mask,id))

def c7180 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7180 : Upper (D 1) (R 1) [52,264,192,80] 13 := by
  apply FastRouting.sound _ _ [52,264,192,80] 13 (by decide) (choices 1) [1,2,32,128] r7180 c7180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3653
  · exact u3654
  · exact u3655
  · exact u3656

def b7181 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 196 200 51 51 115 179 307), lower := (rows 53 266 196 200 16 32 64 128 256), losses := [] }

theorem u7181 : Upper (D 1) (R 1) [52,264,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7181
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7182 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 53 274 14 11 240 224 224 224 480), lower := (rows 53 274 14 11 16 32 64 128 256), losses := [] }

theorem u7182 : Upper (D 1) (R 1) [52,272,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7182
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7183 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 274 14 41 210 226 194 194 450), lower := (rows 53 274 14 41 16 32 64 128 256), losses := [] }

theorem u7183 : Upper (D 1) (R 1) [52,272,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7183
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7184 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 274 14 42 209 225 193 193 449), lower := (rows 53 274 14 42 16 32 64 128 256), losses := [] }

theorem u7184 : Upper (D 1) (R 1) [52,272,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7184
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7185 : PairBound 9 := { available := 226, camps := [], pairs := [(3,4)], upper := (rows 53 274 14 73 242 226 226 226 482), lower := (rows 53 274 14 73 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 9 0 38 70 134 262), good := (rows 493 482 494 73 0 32 64 128 256) }] }

theorem u7185 : Upper (D 1) (R 1) [52,272,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7185
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7186 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 274 14 74 241 225 225 225 481), lower := (rows 53 274 14 74 16 32 64 128 256), losses := [] }

theorem u7186 : Upper (D 1) (R 1) [52,272,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7186
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7187 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 14 104 211 227 195 195 451), lower := (rows 53 274 14 104 16 32 64 128 256), losses := [] }

theorem u7187 : Upper (D 1) (R 1) [52,272,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7187
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7188 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7188 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7188 : Upper (D 1) (R 1) [52,272,10,192] 13 := by
  apply FastRouting.sound _ _ [52,272,10,192] 13 (by decide) (choices 1) [1,2,32,64] r7188 c7188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3657
  · exact u3658
  · exact u3659
  · exact u3660

def b7189 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 53 274 70 11 248 232 232 232 488), lower := (rows 53 274 70 11 16 32 64 128 256), losses := [] }

theorem u7189 : Upper (D 1) (R 1) [52,272,66,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7189
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7190 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 274 70 41 218 234 202 202 458), lower := (rows 53 274 70 41 16 32 64 128 256), losses := [] }

theorem u7190 : Upper (D 1) (R 1) [52,272,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7190
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7191 : Route 9 := (fun mask => (mask,id))

def c7191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7191 : Upper (D 1) (R 1) [52,272,66,34] 13 := by
  apply FastRouting.sound _ _ [52,272,66,34] 13 (by decide) (choices 1) [1,8,64,128] r7191 c7191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3661
  · exact u3662
  · exact u3663
  · exact u3664

def b7192 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 70 73 186 170 234 170 426), lower := (rows 53 274 70 73 16 32 64 128 256), losses := [] }

theorem u7192 : Upper (D 1) (R 1) [52,272,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7192
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7193 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 274 70 74 185 169 233 169 425), lower := (rows 53 274 70 74 16 32 64 128 256), losses := [] }

theorem u7193 : Upper (D 1) (R 1) [52,272,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7193
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7194 : Route 9 := (fun mask => (mask,id))

def c7194 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7194 : Upper (D 1) (R 1) [52,272,66,96] 13 := by
  apply FastRouting.sound _ _ [52,272,66,96] 13 (by decide) (choices 1) [1,2,8,128] r7194 c7194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3665
  · exact u3666
  · exact u3667
  · exact u3668

def r7195 : Route 9 := (fun mask => (mask,id))

def c7195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7195 : Upper (D 1) (R 1) [52,272,66,129] 13 := by
  apply FastRouting.sound _ _ [52,272,66,129] 13 (by decide) (choices 1) [2,8,32,64,128] r7195 c7195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3669
  · exact u3670
  · exact u3671
  · exact u3672
  · exact u3673

def r7196 : Route 9 := (fun mask => (mask,id))

def c7196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7196 : Upper (D 1) (R 1) [52,272,66,130] 13 := by
  apply FastRouting.sound _ _ [52,272,66,130] 13 (by decide) (choices 1) [1,8,32,64,128] r7196 c7196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3674
  · exact u3675
  · exact u3676
  · exact u3677
  · exact u3678

def r7197 : Route 9 := (fun mask => (mask,id))

def c7197 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7197 : Upper (D 1) (R 1) [52,272,66,160] 13 := by
  apply FastRouting.sound _ _ [52,272,66,160] 13 (by decide) (choices 1) [1,2,8,64,128] r7197 c7197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3679
  · exact u3680
  · exact u3681
  · exact u3682
  · exact u3683

def r7198 : Route 9 := (fun mask => (mask,id))

def c7198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7198 : Upper (D 1) (R 1) [52,272,66,192] 13 := by
  apply FastRouting.sound _ _ [52,272,66,192] 13 (by decide) (choices 1) [1,2,8,32,128] r7198 c7198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3684
  · exact u3685
  · exact u3686
  · exact u3687
  · exact u3688

def b7199 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 53 274 76 11 242 226 226 226 482), lower := (rows 53 274 76 11 16 32 64 128 256), losses := [] }

theorem u7199 : Upper (D 1) (R 1) [52,272,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7199
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7199
end Delivery.IrregularNine14.P01
