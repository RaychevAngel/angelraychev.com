import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0026
import IrregularNine14P03C0027

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4140 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 28 41 273 226 194 194 450), lower := (rows 97 7 28 41 273 32 64 128 256), losses := [] }

theorem u4140 : Upper (D 3) (R 3) [96,5,24,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4140
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4141 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 28 41 274 225 193 193 449), lower := (rows 97 7 28 41 274 32 64 128 256), losses := [] }

theorem u4141 : Upper (D 3) (R 3) [96,5,24,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4141
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4142 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 28 41 400 227 195 195 451), lower := (rows 97 7 28 41 400 32 64 128 256), losses := [] }

theorem u4142 : Upper (D 3) (R 3) [96,5,24,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4142
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4143 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 42 145 481 449 449 449), lower := (rows 97 7 28 42 145 32 64 128 256), losses := [] }

theorem u4143 : Upper (D 3) (R 3) [96,5,24,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4143
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4144 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 42 208 417 449 385 385), lower := (rows 97 7 28 42 208 32 64 128 256), losses := [] }

theorem u4144 : Upper (D 3) (R 3) [96,5,24,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4144
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4145 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 42 273 225 193 193 449), lower := (rows 97 7 28 42 273 32 64 128 256), losses := [] }

theorem u4145 : Upper (D 3) (R 3) [96,5,24,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4145
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4146 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 42 336 161 193 129 385), lower := (rows 97 7 28 42 336 32 64 128 256), losses := [] }

theorem u4146 : Upper (D 3) (R 3) [96,5,24,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4146
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4147 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 42 400 225 193 193 449), lower := (rows 97 7 28 42 400 32 64 128 256), losses := [] }

theorem u4147 : Upper (D 3) (R 3) [96,5,24,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4147
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4148 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 145 419 451 387 387), lower := (rows 97 7 28 104 145 32 64 128 256), losses := [] }

theorem u4148 : Upper (D 3) (R 3) [96,5,24,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4148
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4149 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 146 417 449 385 385), lower := (rows 97 7 28 104 146 32 64 128 256), losses := [] }

theorem u4149 : Upper (D 3) (R 3) [96,5,24,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4149
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4150 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 273 163 195 131 387), lower := (rows 97 7 28 104 273 32 64 128 256), losses := [] }

theorem u4150 : Upper (D 3) (R 3) [96,5,24,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4150
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4151 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 274 161 193 129 385), lower := (rows 97 7 28 104 274 32 64 128 256), losses := [] }

theorem u4151 : Upper (D 3) (R 3) [96,5,24,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4151
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4152 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 400 163 195 131 387), lower := (rows 97 7 28 104 400 32 64 128 256), losses := [] }

theorem u4152 : Upper (D 3) (R 3) [96,5,24,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4152
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4153 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 28 137 145 354 354 482 354), lower := (rows 97 7 28 137 145 32 64 128 256), losses := [] }

theorem u4153 : Upper (D 3) (R 3) [96,5,24,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4153
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4154 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 28 137 146 353 353 481 353), lower := (rows 97 7 28 137 146 32 64 128 256), losses := [] }

theorem u4154 : Upper (D 3) (R 3) [96,5,24,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4154
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4155 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 137 176 355 323 451 323), lower := (rows 97 7 28 137 176 32 64 128 256), losses := [] }

theorem u4155 : Upper (D 3) (R 3) [96,5,24,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4155
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4156 : Route 9 := (fun mask => (mask,id))

def c4156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4156 : Upper (D 3) (R 3) [96,5,24,129,257] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,257] 13 (by decide) (choices 1) [2,64,128] r4156 c4156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1618
  · exact u1619
  · exact u1620

def r4157 : Route 9 := (fun mask => (mask,id))

def c4157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4157 : Upper (D 3) (R 3) [96,5,24,129,258] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,258] 13 (by decide) (choices 1) [1,64,128] r4157 c4157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1621
  · exact u1622
  · exact u1623

def b4158 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 28 137 304 227 195 195 451), lower := (rows 97 7 28 137 304 32 64 128 256), losses := [] }

theorem u4158 : Upper (D 3) (R 3) [96,5,24,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4158
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4159 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 137 400 99 99 227 355), lower := (rows 97 7 28 137 400 32 64 128 256), losses := [] }

theorem u4159 : Upper (D 3) (R 3) [96,5,24,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4159
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4160 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 138 176 353 321 449 321), lower := (rows 97 7 28 138 176 32 64 128 256), losses := [] }

theorem u4160 : Upper (D 3) (R 3) [96,5,24,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4160
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4161 : Route 9 := (fun mask => (mask,id))

def c4161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4161 : Upper (D 3) (R 3) [96,5,24,130,257] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130,257] 13 (by decide) (choices 1) [1,64,128] r4161 c4161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1624
  · exact u1625
  · exact u1626

def b4162 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 28 138 304 225 193 193 449), lower := (rows 97 7 28 138 304 32 64 128 256), losses := [] }

theorem u4162 : Upper (D 3) (R 3) [96,5,24,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4162
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4163 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 138 400 97 97 225 353), lower := (rows 97 7 28 138 400 32 64 128 256), losses := [] }

theorem u4163 : Upper (D 3) (R 3) [96,5,24,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4163
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4164 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 168 208 291 323 387 259), lower := (rows 97 7 28 168 208 32 64 128 256), losses := [] }

theorem u4164 : Upper (D 3) (R 3) [96,5,24,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4164
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4165 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 168 273 227 195 195 451), lower := (rows 97 7 28 168 273 32 64 128 256), losses := [] }

theorem u4165 : Upper (D 3) (R 3) [96,5,24,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4165
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4166 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 168 274 225 193 193 449), lower := (rows 97 7 28 168 274 32 64 128 256), losses := [] }

theorem u4166 : Upper (D 3) (R 3) [96,5,24,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4166
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4167 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 168 336 163 195 131 387), lower := (rows 97 7 28 168 336 32 64 128 256), losses := [] }

theorem u4167 : Upper (D 3) (R 3) [96,5,24,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4167
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4168 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 168 400 99 67 195 323), lower := (rows 97 7 28 168 400 32 64 128 256), losses := [] }

theorem u4168 : Upper (D 3) (R 3) [96,5,24,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4168
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4169 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 25 146 488 456 456 456), lower := (rows 97 7 37 25 146 32 64 128 256), losses := [] }

theorem u4169 : Upper (D 3) (R 3) [96,5,33,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4169
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4170 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 25 152 482 450 450 450), lower := (rows 97 7 37 25 152 32 64 128 256), losses := [] }

theorem u4170 : Upper (D 3) (R 3) [96,5,33,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4170
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4171 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 25 274 232 200 200 456), lower := (rows 97 7 37 25 274 32 64 128 256), losses := [] }

theorem u4171 : Upper (D 3) (R 3) [96,5,33,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4171
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4172 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 25 280 226 194 194 450), lower := (rows 97 7 37 25 280 32 64 128 256), losses := [] }

theorem u4172 : Upper (D 3) (R 3) [96,5,33,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4172
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4173 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 25 400 234 202 202 458), lower := (rows 97 7 37 25 400 32 64 128 256), losses := [] }

theorem u4173 : Upper (D 3) (R 3) [96,5,33,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4173
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4174 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 145 488 456 456 456), lower := (rows 97 7 37 26 145 32 64 128 256), losses := [] }

theorem u4174 : Upper (D 3) (R 3) [96,5,33,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4174
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4175 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 152 481 449 449 449), lower := (rows 97 7 37 26 152 32 64 128 256), losses := [] }

theorem u4175 : Upper (D 3) (R 3) [96,5,33,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4175
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4176 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 208 425 457 393 393), lower := (rows 97 7 37 26 208 32 64 128 256), losses := [] }

theorem u4176 : Upper (D 3) (R 3) [96,5,33,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4176
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4177 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 273 232 200 200 456), lower := (rows 97 7 37 26 273 32 64 128 256), losses := [] }

theorem u4177 : Upper (D 3) (R 3) [96,5,33,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4177
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4178 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 280 225 193 193 449), lower := (rows 97 7 37 26 280 32 64 128 256), losses := [] }

theorem u4178 : Upper (D 3) (R 3) [96,5,33,18,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4178
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4179 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 336 169 201 137 393), lower := (rows 97 7 37 26 336 32 64 128 256), losses := [] }

theorem u4179 : Upper (D 3) (R 3) [96,5,33,18,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4179
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4180 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 400 233 201 201 457), lower := (rows 97 7 37 26 400 32 64 128 256), losses := [] }

theorem u4180 : Upper (D 3) (R 3) [96,5,33,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4180
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4181 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 145 440 472 408 408), lower := (rows 97 7 37 74 145 32 64 128 256), losses := [] }

theorem u4181 : Upper (D 3) (R 3) [96,5,33,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4181
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4182 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 152 433 465 401 401), lower := (rows 97 7 37 74 152 32 64 128 256), losses := [] }

theorem u4182 : Upper (D 3) (R 3) [96,5,33,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4182
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4183 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 273 184 216 152 408), lower := (rows 97 7 37 74 273 32 64 128 256), losses := [] }

theorem u4183 : Upper (D 3) (R 3) [96,5,33,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4183
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4184 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 280 177 209 145 401), lower := (rows 97 7 37 74 280 32 64 128 256), losses := [] }

theorem u4184 : Upper (D 3) (R 3) [96,5,33,66,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4184
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4185 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 400 185 217 153 409), lower := (rows 97 7 37 74 400 32 64 128 256), losses := [] }

theorem u4185 : Upper (D 3) (R 3) [96,5,33,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4185
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4186 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 145 426 458 394 394), lower := (rows 97 7 37 88 145 32 64 128 256), losses := [] }

theorem u4186 : Upper (D 3) (R 3) [96,5,33,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4186
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4187 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 146 425 457 393 393), lower := (rows 97 7 37 88 146 32 64 128 256), losses := [] }

theorem u4187 : Upper (D 3) (R 3) [96,5,33,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4187
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4188 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 273 170 202 138 394), lower := (rows 97 7 37 88 273 32 64 128 256), losses := [] }

theorem u4188 : Upper (D 3) (R 3) [96,5,33,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4188
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4189 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 274 169 201 137 393), lower := (rows 97 7 37 88 274 32 64 128 256), losses := [] }

theorem u4189 : Upper (D 3) (R 3) [96,5,33,80,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4189
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4190 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 88 400 171 203 139 395), lower := (rows 97 7 37 88 400 32 64 128 256), losses := [] }

theorem u4190 : Upper (D 3) (R 3) [96,5,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4190
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4191 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 137 146 376 344 472 344), lower := (rows 97 7 37 137 146 32 64 128 256), losses := [] }

theorem u4191 : Upper (D 3) (R 3) [96,5,33,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4191
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4192 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 137 208 314 346 410 282), lower := (rows 97 7 37 137 208 32 64 128 256), losses := [] }

theorem u4192 : Upper (D 3) (R 3) [96,5,33,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4192
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4193 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 137 274 248 216 216 472), lower := (rows 97 7 37 137 274 32 64 128 256), losses := [] }

theorem u4193 : Upper (D 3) (R 3) [96,5,33,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4193
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4194 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 137 280 242 210 210 466), lower := (rows 97 7 37 137 280 32 64 128 256), losses := [] }

theorem u4194 : Upper (D 3) (R 3) [96,5,33,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4194
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4195 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 137 336 186 218 154 410), lower := (rows 97 7 37 137 336 32 64 128 256), losses := [] }

theorem u4195 : Upper (D 3) (R 3) [96,5,33,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4195
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4196 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 137 400 122 90 218 346), lower := (rows 97 7 37 137 400 32 64 128 256), losses := [] }

theorem u4196 : Upper (D 3) (R 3) [96,5,33,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4196
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4197 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 208 313 345 409 281), lower := (rows 97 7 37 138 208 32 64 128 256), losses := [] }

theorem u4197 : Upper (D 3) (R 3) [96,5,33,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4197
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4198 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 273 248 216 216 472), lower := (rows 97 7 37 138 273 32 64 128 256), losses := [] }

theorem u4198 : Upper (D 3) (R 3) [96,5,33,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4198
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4199 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 280 241 209 209 465), lower := (rows 97 7 37 138 280 32 64 128 256), losses := [] }

theorem u4199 : Upper (D 3) (R 3) [96,5,33,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4199
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4199
end Delivery.IrregularNine14.P03
