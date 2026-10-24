import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0019

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10140 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 52 73 400 36 67 195 323), lower := (rows 7 42 52 73 400 36 64 128 256), losses := [] }

theorem u10140 : Upper (D 6) (R 6) [6,40,48,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10140
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10141 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 52 73 400 96 71 135 263), lower := (rows 7 42 52 73 400 96 64 128 256), losses := [] }

theorem u10141 : Upper (D 6) (R 6) [6,40,48,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10141
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10142 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 52 137 336 33 70 198 326), lower := (rows 7 42 52 137 336 33 64 128 256), losses := [] }

theorem u10142 : Upper (D 6) (R 6) [6,40,48,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10142
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10143 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 52 137 336 34 69 197 325), lower := (rows 7 42 52 137 336 34 64 128 256), losses := [] }

theorem u10143 : Upper (D 6) (R 6) [6,40,48,129,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10143
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10144 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 52 137 336 36 67 195 323), lower := (rows 7 42 52 137 336 36 64 128 256), losses := [] }

theorem u10144 : Upper (D 6) (R 6) [6,40,48,129,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10144
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10145 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 137 336 96 71 135 263), lower := (rows 7 42 52 137 336 96 64 128 256), losses := [] }

theorem u10145 : Upper (D 6) (R 6) [6,40,48,129,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10145
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m10146_4 : Upper (D 6) (R 6) [6,40,48,192,320,1,4] 13 :=
  permutation_upper _ _ _ [6,40,48,192,320,1,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1179

def r10146 : Route 9 := (fun mask => (mask,id))

def c10146 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10146 : Upper (D 6) (R 6) [6,40,48,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320,1] 13 (by decide) (choices 1) [1,2,4] r10146 c10146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1178
  · exact u1179
  · exact m10146_4

def b10147 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 52 200 336 34 69 133 261), lower := (rows 7 42 52 200 336 34 64 128 256), losses := [] }

theorem u10147 : Upper (D 6) (R 6) [6,40,48,192,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10147
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10148 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 84 73 400 33 102 166 294), lower := (rows 7 42 84 73 400 33 64 128 256), losses := [] }

theorem u10148 : Upper (D 6) (R 6) [6,40,80,65,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10148
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10149 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 84 73 400 34 101 165 293), lower := (rows 7 42 84 73 400 34 64 128 256), losses := [] }

theorem u10149 : Upper (D 6) (R 6) [6,40,80,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10149
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10150 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 7 42 84 73 400 36 99 163 291), lower := (rows 7 42 84 73 400 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 116 106 400 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 27 37 0 137 265), good := (rows 439 442 52 443 400 36 0 128 256) }] }

theorem u10150 : Upper (D 6) (R 6) [6,40,80,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10150
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10151 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 84 137 273 34 100 228 356), lower := (rows 7 42 84 137 273 34 64 128 256), losses := [] }

theorem u10151 : Upper (D 6) (R 6) [6,40,80,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10151
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10152 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(2,0),(3,2)], upper := (rows 7 42 84 137 273 36 98 226 354), lower := (rows 7 42 84 137 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 53 75 139 267), good := (rows 486 490 116 490 500 36 64 128 256) },{ target := 2, region := (rows 1 2 0 9 17 32 66 130 258), good := (rows 475 490 80 153 281 32 64 128 256) }] }

theorem u10152 : Upper (D 6) (R 6) [6,40,80,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10152
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m10153_2 : Upper (D 6) (R 6) [6,40,80,129,257,64,2] 13 :=
  permutation_upper _ _ _ [6,40,80,129,257,4,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1181

theorem m10153_4 : Upper (D 6) (R 6) [6,40,80,129,257,64,4] 13 :=
  permutation_upper _ _ _ [6,40,80,129,257,2,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1180

def r10153 : Route 9 := (fun mask => (mask,id))

def c10153 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10153 : Upper (D 6) (R 6) [6,40,80,129,257,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257,64] 13 (by decide) (choices 1) [2,4,32] r10153 c10153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m10153_2
  · exact m10153_4
  · exact u1182

def b10154 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 84 137 274 33 100 228 356), lower := (rows 7 42 84 137 274 33 64 128 256), losses := [] }

theorem u10154 : Upper (D 6) (R 6) [6,40,80,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10154
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10155 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(1,0),(1,6),(3,1)], upper := (rows 7 42 84 137 274 36 97 225 353), lower := (rows 7 42 84 137 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 116 170 274 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 16 37 0 128 256), good := (rows 39 42 52 171 274 36 0 128 256) }] }

theorem u10155 : Upper (D 6) (R 6) [6,40,80,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10155
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10156 : Route 9 := (fun mask => (mask,id))

def c10156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10156 : Upper (D 6) (R 6) [6,40,80,129,258,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,258,64] 13 (by decide) (choices 1) [1,4,32] r10156 c10156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1183
  · exact u1184
  · exact u1185

def b10157 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 234, targets := 4 },{ cop := 1, region := 340, targets := 1 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 42 84 137 276 33 98 226 354), lower := (rows 7 42 84 137 276 33 64 128 256), losses := [] }

theorem u10157 : Upper (D 6) (R 6) [6,40,80,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10157
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10158 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 234, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(3,2)], upper := (rows 7 42 84 137 276 34 97 225 353), lower := (rows 7 42 84 137 276 34 64 128 256), losses := [] }

theorem u10158 : Upper (D 6) (R 6) [6,40,80,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10158
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10159 : Route 9 := (fun mask => (mask,id))

def c10159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10159 : Upper (D 6) (R 6) [6,40,80,129,260,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,260,64] 13 (by decide) (choices 1) [1,2,32] r10159 c10159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1186
  · exact u1187
  · exact u1188

def b10160 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 84 137 304 33 70 198 326), lower := (rows 7 42 84 137 304 33 64 128 256), losses := [] }

theorem u10160 : Upper (D 6) (R 6) [6,40,80,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10160
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10161 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 84 137 304 34 69 197 325), lower := (rows 7 42 84 137 304 34 64 128 256), losses := [] }

theorem u10161 : Upper (D 6) (R 6) [6,40,80,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10161
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10162 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 200, targets := 36 }], pairs := [(1,0),(3,2),(3,5)], upper := (rows 7 42 84 137 304 36 67 195 323), lower := (rows 7 42 84 137 304 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 116 170 304 36 64 128 256) }] }

theorem u10162 : Upper (D 6) (R 6) [6,40,80,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10162
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10163 : Route 9 := (fun mask => (mask,id))

def c10163 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10163 : Upper (D 6) (R 6) [6,40,80,129,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288,64] 13 (by decide) (choices 1) [1,2,4] r10163 c10163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1189
  · exact u1190
  · exact u1191

def b10164 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 232, targets := 2 }], pairs := [(0,6),(1,6),(3,1)], upper := (rows 7 42 84 140 274 33 97 225 353), lower := (rows 7 42 84 140 274 33 64 128 256), losses := [] }

theorem u10164 : Upper (D 6) (R 6) [6,40,80,132,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10164
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10165 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(3,1),(4,2)], upper := (rows 7 42 84 140 274 96 97 161 289), lower := (rows 7 42 84 140 274 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 100 64 128 256), good := (rows 38 42 116 174 274 96 96 128 256) }] }

theorem u10165 : Upper (D 6) (R 6) [6,40,80,132,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10165
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10166 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 84 140 304 33 67 195 323), lower := (rows 7 42 84 140 304 33 64 128 256), losses := [] }

theorem u10166 : Upper (D 6) (R 6) [6,40,80,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10166
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10167 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 7 42 84 140 304 34 65 193 321), lower := (rows 7 42 84 140 304 34 64 128 256), losses := [] }

theorem u10167 : Upper (D 6) (R 6) [6,40,80,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10167
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10168 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 136, targets := 32 },{ cop := 0, region := 136, targets := 64 }], pairs := [(3,5),(3,6),(4,2)], upper := (rows 7 42 84 140 304 96 67 131 259), lower := (rows 7 42 84 140 304 96 64 128 256), losses := [] }

theorem u10168 : Upper (D 6) (R 6) [6,40,80,132,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10168
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10169 : Route 9 := (fun mask => (mask,id))

def c10169 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10169 : Upper (D 6) (R 6) [6,40,80,192,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,288,1] 13 (by decide) (choices 1) [1,2,4] r10169 c10169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1192
  · exact u1193
  · exact u1194

def b10170 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 84 200 304 34 69 133 261), lower := (rows 7 42 84 200 304 34 64 128 256), losses := [] }

theorem u10170 : Upper (D 6) (R 6) [6,40,80,192,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10170
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10171 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 200, targets := 36 },{ cop := 0, region := 304, targets := 64 }], pairs := [(3,2),(3,5),(4,6)], upper := (rows 7 42 84 200 304 36 67 131 259), lower := (rows 7 42 84 200 304 36 64 128 256), losses := [] }

theorem u10171 : Upper (D 6) (R 6) [6,40,80,192,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10171
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10172 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 25 400 33 70 198 326), lower := (rows 7 42 100 25 400 33 64 128 256), losses := [] }

theorem u10172 : Upper (D 6) (R 6) [6,40,96,17,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10172
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10173 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 100 25 400 34 69 197 325), lower := (rows 7 42 100 25 400 34 64 128 256), losses := [] }

theorem u10173 : Upper (D 6) (R 6) [6,40,96,17,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10173
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10174 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 25 400 36 67 195 323), lower := (rows 7 42 100 25 400 36 64 128 256), losses := [] }

theorem u10174 : Upper (D 6) (R 6) [6,40,96,17,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10174
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10175 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 25 400 96 71 135 263), lower := (rows 7 42 100 25 400 96 64 128 256), losses := [] }

theorem u10175 : Upper (D 6) (R 6) [6,40,96,17,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10175
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10176 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 100 137 81 34 340 404 276), lower := (rows 7 42 100 137 81 34 64 128 256), losses := [] }

theorem u10176 : Upper (D 6) (R 6) [6,40,96,129,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10176
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10177 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 137 81 36 338 402 274), lower := (rows 7 42 100 137 81 36 64 128 256), losses := [] }

theorem u10177 : Upper (D 6) (R 6) [6,40,96,129,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10177
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10178 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 137 81 48 326 390 262), lower := (rows 7 42 100 137 81 48 64 128 256), losses := [] }

theorem u10178 : Upper (D 6) (R 6) [6,40,96,129,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10178
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10179 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 137 81 288 86 150 278), lower := (rows 7 42 100 137 81 288 64 128 256), losses := [] }

theorem u10179 : Upper (D 6) (R 6) [6,40,96,129,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10179
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10180 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 137 82 33 340 404 276), lower := (rows 7 42 100 137 82 33 64 128 256), losses := [] }

theorem u10180 : Upper (D 6) (R 6) [6,40,96,129,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10180
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10181 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 137 82 36 337 401 273), lower := (rows 7 42 100 137 82 36 64 128 256), losses := [] }

theorem u10181 : Upper (D 6) (R 6) [6,40,96,129,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10181
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10182 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 137 82 48 325 389 261), lower := (rows 7 42 100 137 82 48 64 128 256), losses := [] }

theorem u10182 : Upper (D 6) (R 6) [6,40,96,129,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10182
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10183 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 137 82 288 85 149 277), lower := (rows 7 42 100 137 82 288 64 128 256), losses := [] }

theorem u10183 : Upper (D 6) (R 6) [6,40,96,129,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10183
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10184 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 100 137 273 34 84 212 340), lower := (rows 7 42 100 137 273 34 64 128 256), losses := [] }

theorem u10184 : Upper (D 6) (R 6) [6,40,96,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10184
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10185 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 137 273 36 82 210 338), lower := (rows 7 42 100 137 273 36 64 128 256), losses := [] }

theorem u10185 : Upper (D 6) (R 6) [6,40,96,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10185
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10186 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 137 273 48 70 198 326), lower := (rows 7 42 100 137 273 48 64 128 256), losses := [] }

theorem u10186 : Upper (D 6) (R 6) [6,40,96,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10186
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10187 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 137 273 96 86 150 278), lower := (rows 7 42 100 137 273 96 64 128 256), losses := [] }

theorem u10187 : Upper (D 6) (R 6) [6,40,96,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10187
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10188 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 137 274 33 84 212 340), lower := (rows 7 42 100 137 274 33 64 128 256), losses := [] }

theorem u10188 : Upper (D 6) (R 6) [6,40,96,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10188
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10189 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 137 274 36 81 209 337), lower := (rows 7 42 100 137 274 36 64 128 256), losses := [] }

theorem u10189 : Upper (D 6) (R 6) [6,40,96,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10189
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10190 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 137 274 48 69 197 325), lower := (rows 7 42 100 137 274 48 64 128 256), losses := [] }

theorem u10190 : Upper (D 6) (R 6) [6,40,96,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10190
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10191 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 137 274 96 85 149 277), lower := (rows 7 42 100 137 274 96 64 128 256), losses := [] }

theorem u10191 : Upper (D 6) (R 6) [6,40,96,129,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10191
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10192 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 137 276 33 82 210 338), lower := (rows 7 42 100 137 276 33 64 128 256), losses := [] }

theorem u10192 : Upper (D 6) (R 6) [6,40,96,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10192
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10193 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 100 137 276 34 81 209 337), lower := (rows 7 42 100 137 276 34 64 128 256), losses := [] }

theorem u10193 : Upper (D 6) (R 6) [6,40,96,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10193
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10194 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 100 137 276 48 67 195 323), lower := (rows 7 42 100 137 276 48 64 128 256), losses := [] }

theorem u10194 : Upper (D 6) (R 6) [6,40,96,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10194
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10195 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 137 276 96 83 147 275), lower := (rows 7 42 100 137 276 96 64 128 256), losses := [] }

theorem u10195 : Upper (D 6) (R 6) [6,40,96,129,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10195
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10196 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 137 336 33 86 150 278), lower := (rows 7 42 100 137 336 33 64 128 256), losses := [] }

theorem u10196 : Upper (D 6) (R 6) [6,40,96,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10196
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10197 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 100 137 336 34 85 149 277), lower := (rows 7 42 100 137 336 34 64 128 256), losses := [] }

theorem u10197 : Upper (D 6) (R 6) [6,40,96,129,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10197
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10198 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 137 336 36 83 147 275), lower := (rows 7 42 100 137 336 36 64 128 256), losses := [] }

theorem u10198 : Upper (D 6) (R 6) [6,40,96,129,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10198
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10199 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 137 336 48 71 135 263), lower := (rows 7 42 100 137 336 48 64 128 256), losses := [] }

theorem u10199 : Upper (D 6) (R 6) [6,40,96,129,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10199
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10199
end Delivery.IrregularNine14.P06
