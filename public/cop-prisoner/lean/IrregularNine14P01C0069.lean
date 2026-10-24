import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0018
import IrregularNine14P01C0019

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4140 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 261 26 48 234 202 202 458), lower := (rows 113 134 261 26 48 32 64 128 256), losses := [] }

theorem u4140 : Upper (D 1) (R 1) [112,132,257,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4140
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4141 : PairBound 9 := { available := 106, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 134 261 26 144 106 106 234 362), lower := (rows 113 134 261 26 144 32 64 128 256), losses := [] }

theorem u4141 : Upper (D 1) (R 1) [112,132,257,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4141
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4142 : PairBound 9 := { available := 106, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 134 261 152 18 106 106 234 362), lower := (rows 113 134 261 152 18 32 64 128 256), losses := [] }

theorem u4142 : Upper (D 1) (R 1) [112,132,257,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4142
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4143 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 134 261 152 24 98 98 226 354), lower := (rows 113 134 261 152 24 32 64 128 256), losses := [] }

theorem u4143 : Upper (D 1) (R 1) [112,132,257,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4143
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4144 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 261 152 48 106 74 202 330), lower := (rows 113 134 261 152 48 32 64 128 256), losses := [] }

theorem u4144 : Upper (D 1) (R 1) [112,132,257,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4144
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4145 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 262 137 18 120 120 248 376), lower := (rows 113 134 262 137 18 32 64 128 256), losses := [] }

theorem u4145 : Upper (D 1) (R 1) [112,132,258,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4145
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4146 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 113 134 262 137 24 114 114 242 370), lower := (rows 113 134 262 137 24 32 64 128 256), losses := [] }

theorem u4146 : Upper (D 1) (R 1) [112,132,258,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4146
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4147 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 262 137 48 122 90 218 346), lower := (rows 113 134 262 137 48 32 64 128 256), losses := [] }

theorem u4147 : Upper (D 1) (R 1) [112,132,258,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4147
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4148 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 134 262 152 17 106 106 234 362), lower := (rows 113 134 262 152 17 32 64 128 256), losses := [] }

theorem u4148 : Upper (D 1) (R 1) [112,132,258,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4148
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4149 : PairBound 9 := { available := 105, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 134 262 152 18 105 105 233 361), lower := (rows 113 134 262 152 18 32 64 128 256), losses := [] }

theorem u4149 : Upper (D 1) (R 1) [112,132,258,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4149
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4150 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 134 262 152 24 99 99 227 355), lower := (rows 113 134 262 152 24 32 64 128 256), losses := [] }

theorem u4150 : Upper (D 1) (R 1) [112,132,258,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4150
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4151 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 262 152 48 107 75 203 331), lower := (rows 113 134 262 152 48 32 64 128 256), losses := [] }

theorem u4151 : Upper (D 1) (R 1) [112,132,258,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4151
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4152 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 268 11 18 240 240 240 496), lower := (rows 113 134 268 11 18 32 64 128 256), losses := [] }

theorem u4152 : Upper (D 1) (R 1) [112,132,264,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4152
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4153 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 268 11 48 242 210 210 466), lower := (rows 113 134 268 11 48 32 64 128 256), losses := [] }

theorem u4153 : Upper (D 1) (R 1) [112,132,264,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4153
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4154_2 : Upper (D 1) (R 1) [112,132,264,3,128,2] 13 :=
  permutation_upper _ _ _ [112,132,264,3,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1130

theorem m4154_16 : Upper (D 1) (R 1) [112,132,264,3,128,16] 13 :=
  permutation_upper _ _ _ [112,132,264,3,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1131

theorem m4154_64 : Upper (D 1) (R 1) [112,132,264,3,128,64] 13 :=
  permutation_upper _ _ _ [112,132,264,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1132

def r4154 : Route 9 := (fun mask => (mask,id))

def c4154 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4154 : Upper (D 1) (R 1) [112,132,264,3,128] 13 := by
  apply FastRouting.sound _ _ [112,132,264,3,128] 13 (by decide) (choices 1) [2,16,64] r4154 c4154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4154_2
  · exact m4154_16
  · exact m4154_64

def b4155 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 134 268 26 17 226 226 226 482), lower := (rows 113 134 268 26 17 32 64 128 256), losses := [] }

theorem u4155 : Upper (D 1) (R 1) [112,132,264,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4155
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4156 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 134 268 26 18 225 225 225 481), lower := (rows 113 134 268 26 18 32 64 128 256), losses := [] }

theorem u4156 : Upper (D 1) (R 1) [112,132,264,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4156
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4157 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 268 26 48 227 195 195 451), lower := (rows 113 134 268 26 48 32 64 128 256), losses := [] }

theorem u4157 : Upper (D 1) (R 1) [112,132,264,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4157
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4158 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 134 268 26 144 99 99 227 355), lower := (rows 113 134 268 26 144 32 64 128 256), losses := [] }

theorem u4158 : Upper (D 1) (R 1) [112,132,264,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4158
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4159 : Route 9 := (fun mask => (mask,id))

def c4159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4159 : Upper (D 1) (R 1) [112,132,272,3,2] 13 := by
  apply FastRouting.sound _ _ [112,132,272,3,2] 13 (by decide) (choices 1) [8,64,128] r4159 c4159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1133
  · exact u1134
  · exact u1135

def b4160 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 134 276 11 24 226 226 226 482), lower := (rows 113 134 276 11 24 32 64 128 256), losses := [] }

theorem u4160 : Upper (D 1) (R 1) [112,132,272,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4160
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4161 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 276 11 48 234 202 202 458), lower := (rows 113 134 276 11 48 32 64 128 256), losses := [] }

theorem u4161 : Upper (D 1) (R 1) [112,132,272,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4161
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4162 : Route 9 := (fun mask => (mask,id))

def c4162 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4162 : Upper (D 1) (R 1) [112,132,272,3,128] 13 := by
  apply FastRouting.sound _ _ [112,132,272,3,128] 13 (by decide) (choices 1) [2,8,64] r4162 c4162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1136
  · exact u1137
  · exact u1138

def b4163 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 134 276 42 17 234 202 202 458), lower := (rows 113 134 276 42 17 32 64 128 256), losses := [] }

theorem u4163 : Upper (D 1) (R 1) [112,132,272,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4163
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4164 : Route 9 := (fun mask => (mask,id))

def c4164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4164 : Upper (D 1) (R 1) [112,132,272,34,2] 13 := by
  apply FastRouting.sound _ _ [112,132,272,34,2] 13 (by decide) (choices 1) [1,8,64,128] r4164 c4164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1139
  · exact u1140
  · exact u1141
  · exact u1142

def b4165 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 134 276 42 24 227 195 195 451), lower := (rows 113 134 276 42 24 32 64 128 256), losses := [] }

theorem u4165 : Upper (D 1) (R 1) [112,132,272,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4165
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4166 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 42 80 171 203 139 395), lower := (rows 113 134 276 42 80 32 64 128 256), losses := [] }

theorem u4166 : Upper (D 1) (R 1) [112,132,272,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4166
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4167 : Route 9 := (fun mask => (mask,id))

def c4167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4167 : Upper (D 1) (R 1) [112,132,272,34,128] 13 := by
  apply FastRouting.sound _ _ [112,132,272,34,128] 13 (by decide) (choices 1) [1,2,8,64] r4167 c4167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1143
  · exact u1144
  · exact u1145
  · exact u1146

def r4168 : Route 9 := (fun mask => (mask,id))

def c4168 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4168 : Upper (D 1) (R 1) [112,132,272,129,2] 13 := by
  apply FastRouting.sound _ _ [112,132,272,129,2] 13 (by decide) (choices 1) [2,8,64] r4168 c4168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1147
  · exact u1148
  · exact u1149

def b4169 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 134 276 137 24 98 98 226 354), lower := (rows 113 134 276 137 24 32 64 128 256), losses := [] }

theorem u4169 : Upper (D 1) (R 1) [112,132,272,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4170 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 276 137 48 106 74 202 330), lower := (rows 113 134 276 137 48 32 64 128 256), losses := [] }

theorem u4170 : Upper (D 1) (R 1) [112,132,272,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4170
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4171 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 134 276 168 17 106 74 202 330), lower := (rows 113 134 276 168 17 32 64 128 256), losses := [] }

theorem u4171 : Upper (D 1) (R 1) [112,132,272,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4171
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4172 : Route 9 := (fun mask => (mask,id))

def c4172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4172 : Upper (D 1) (R 1) [112,132,272,160,2] 13 := by
  apply FastRouting.sound _ _ [112,132,272,160,2] 13 (by decide) (choices 1) [1,2,8,64] r4172 c4172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1150
  · exact u1151
  · exact u1152
  · exact u1153

def b4173 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 134 276 168 24 99 67 195 323), lower := (rows 113 134 276 168 24 32 64 128 256), losses := [] }

theorem u4173 : Upper (D 1) (R 1) [112,132,272,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4173
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4174 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 168 80 43 75 139 267), lower := (rows 113 134 276 168 80 32 64 128 256), losses := [] }

theorem u4174 : Upper (D 1) (R 1) [112,132,272,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4174
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4175 : PairBound 9 := { available := 480, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 14 18 480 480 480 480), lower := (rows 113 146 13 14 18 32 64 128 256), losses := [] }

theorem u4175 : Upper (D 1) (R 1) [112,144,9,6,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4175
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4176 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 14 48 482 450 450 450), lower := (rows 113 146 13 14 48 32 64 128 256), losses := [] }

theorem u4176 : Upper (D 1) (R 1) [112,144,9,6,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4176
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4177 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 13 14 144 354 354 482 354), lower := (rows 113 146 13 14 144 32 64 128 256), losses := [] }

theorem u4177 : Upper (D 1) (R 1) [112,144,9,6,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4177
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4178 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 146 13 14 272 226 226 226 482), lower := (rows 113 146 13 14 272 32 64 128 256), losses := [] }

theorem u4178 : Upper (D 1) (R 1) [112,144,9,6,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4178
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4179 : PairBound 9 := { available := 228, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 266 18 228 228 228 484), lower := (rows 113 146 13 266 18 32 64 128 256), losses := [] }

theorem u4179 : Upper (D 1) (R 1) [112,144,9,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4179
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4180 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 146 13 266 20 226 226 226 482), lower := (rows 113 146 13 266 20 32 64 128 256), losses := [] }

theorem u4180 : Upper (D 1) (R 1) [112,144,9,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4180
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4181 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 266 48 230 198 198 454), lower := (rows 113 146 13 266 48 32 64 128 256), losses := [] }

theorem u4181 : Upper (D 1) (R 1) [112,144,9,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4181
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4182 : PairBound 9 := { available := 102, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 13 266 144 102 102 230 358), lower := (rows 113 146 13 266 144 32 64 128 256), losses := [] }

theorem u4182 : Upper (D 1) (R 1) [112,144,9,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4182
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4183 : PairBound 9 := { available := 226, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 268 18 226 226 226 482), lower := (rows 113 146 13 268 18 32 64 128 256), losses := [] }

theorem u4183 : Upper (D 1) (R 1) [112,144,9,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4183
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4184 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 130, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 268 48 226 194 194 450), lower := (rows 113 146 13 268 48 32 64 128 256), losses := [] }

theorem u4184 : Upper (D 1) (R 1) [112,144,9,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4184
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4185 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 13 268 144 98 98 226 354), lower := (rows 113 146 13 268 144 32 64 128 256), losses := [] }

theorem u4185 : Upper (D 1) (R 1) [112,144,9,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4185
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4186 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 392 18 102 102 230 358), lower := (rows 113 146 13 392 18 32 64 128 256), losses := [] }

theorem u4186 : Upper (D 1) (R 1) [112,144,9,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4186
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4187 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 146 13 392 20 98 98 226 354), lower := (rows 113 146 13 392 20 32 64 128 256), losses := [] }

theorem u4187 : Upper (D 1) (R 1) [112,144,9,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4187
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4188 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 392 48 102 70 198 326), lower := (rows 113 146 13 392 48 32 64 128 256), losses := [] }

theorem u4188 : Upper (D 1) (R 1) [112,144,9,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4188
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4189 : PairBound 9 := { available := 228, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 14 265 18 228 228 228 484), lower := (rows 113 146 14 265 18 32 64 128 256), losses := [] }

theorem u4189 : Upper (D 1) (R 1) [112,144,10,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4189
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4190 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 146 14 265 20 226 226 226 482), lower := (rows 113 146 14 265 20 32 64 128 256), losses := [] }

theorem u4190 : Upper (D 1) (R 1) [112,144,10,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4190
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4191 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 14 265 48 230 198 198 454), lower := (rows 113 146 14 265 48 32 64 128 256), losses := [] }

theorem u4191 : Upper (D 1) (R 1) [112,144,10,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4191
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4192 : PairBound 9 := { available := 102, camps := [{ cop := 1, region := 365, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 14 265 144 102 102 230 358), lower := (rows 113 146 14 265 144 32 64 128 256), losses := [] }

theorem u4192 : Upper (D 1) (R 1) [112,144,10,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4192
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4193 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 146 14 268 17 226 226 226 482), lower := (rows 113 146 14 268 17 32 64 128 256), losses := [] }

theorem u4193 : Upper (D 1) (R 1) [112,144,10,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4193
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4194 : PairBound 9 := { available := 225, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 14 268 18 225 225 225 481), lower := (rows 113 146 14 268 18 32 64 128 256), losses := [] }

theorem u4194 : Upper (D 1) (R 1) [112,144,10,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4194
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4195 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 130, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 14 268 48 227 195 195 451), lower := (rows 113 146 14 268 48 32 64 128 256), losses := [] }

theorem u4195 : Upper (D 1) (R 1) [112,144,10,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4195
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4196 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 14 268 144 99 99 227 355), lower := (rows 113 146 14 268 144 32 64 128 256), losses := [] }

theorem u4196 : Upper (D 1) (R 1) [112,144,10,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4196
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4197 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 113 146 14 296 17 230 198 198 454), lower := (rows 113 146 14 296 17 32 64 128 256), losses := [] }

theorem u4197 : Upper (D 1) (R 1) [112,144,10,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4197
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4198 : PairBound 9 := { available := 197, camps := [{ cop := 7, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 14 296 18 229 197 197 453), lower := (rows 113 146 14 296 18 32 64 128 256), losses := [] }

theorem u4198 : Upper (D 1) (R 1) [112,144,10,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4198
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4199 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 146 14 296 20 227 195 195 451), lower := (rows 113 146 14 296 20 32 64 128 256), losses := [] }

theorem u4199 : Upper (D 1) (R 1) [112,144,10,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4199
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4199
end Delivery.IrregularNine14.P01
