import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0019
import IrregularNine14P06C0020

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10200 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 152 273 33 70 198 326), lower := (rows 7 42 100 152 273 33 64 128 256), losses := [] }

theorem u10200 : Upper (D 6) (R 6) [6,40,96,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10200
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10201 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 100 152 273 34 69 197 325), lower := (rows 7 42 100 152 273 34 64 128 256), losses := [] }

theorem u10201 : Upper (D 6) (R 6) [6,40,96,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10201
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10202 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 152 273 36 67 195 323), lower := (rows 7 42 100 152 273 36 64 128 256), losses := [] }

theorem u10202 : Upper (D 6) (R 6) [6,40,96,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10202
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10203 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 152 273 96 71 135 263), lower := (rows 7 42 100 152 273 96 64 128 256), losses := [] }

theorem u10203 : Upper (D 6) (R 6) [6,40,96,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10203
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10204 : Route 9 := (fun mask => (mask,id))

def c10204 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10204 : Upper (D 6) (R 6) [6,40,96,144,260,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,260,1] 13 (by decide) (choices 1) [1,2] r10204 c10204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1195
  · exact u1196

def b10205 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 100 152 276 34 65 193 321), lower := (rows 7 42 100 152 276 34 64 128 256), losses := [] }

theorem u10205 : Upper (D 6) (R 6) [6,40,96,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10205
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10206 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 152 276 96 67 131 259), lower := (rows 7 42 100 152 276 96 64 128 256), losses := [] }

theorem u10206 : Upper (D 6) (R 6) [6,40,96,144,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10206
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10207 : Route 9 := (fun mask => (mask,id))

def c10207 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10207 : Upper (D 6) (R 6) [6,40,96,144,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320,1] 13 (by decide) (choices 1) [1,2,4] r10207 c10207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1197
  · exact u1198
  · exact u1199

def b10208 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 100 152 336 34 69 133 261), lower := (rows 7 42 100 152 336 34 64 128 256), losses := [] }

theorem u10208 : Upper (D 6) (R 6) [6,40,96,144,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10208
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10209 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 152 336 36 67 131 259), lower := (rows 7 42 100 152 336 36 64 128 256), losses := [] }

theorem u10209 : Upper (D 6) (R 6) [6,40,96,144,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10209
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10210 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 100 392 81 33 86 150 278), lower := (rows 7 42 100 392 81 33 64 128 256), losses := [] }

theorem u10210 : Upper (D 6) (R 6) [6,40,96,384,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10210
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10211 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 100 392 81 34 85 149 277), lower := (rows 7 42 100 392 81 34 64 128 256), losses := [] }

theorem u10211 : Upper (D 6) (R 6) [6,40,96,384,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10211
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10212 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 392 81 36 83 147 275), lower := (rows 7 42 100 392 81 36 64 128 256), losses := [] }

theorem u10212 : Upper (D 6) (R 6) [6,40,96,384,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10212
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10213 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 392 81 48 71 135 263), lower := (rows 7 42 100 392 81 48 64 128 256), losses := [] }

theorem u10213 : Upper (D 6) (R 6) [6,40,96,384,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10213
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10214 : Route 9 := (fun mask => (mask,id))

def c10214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10214 : Upper (D 6) (R 6) [6,40,96,384,66,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,66,1] 13 (by decide) (choices 1) [1,4,16] r10214 c10214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1200
  · exact u1201
  · exact u1202

def b10215 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 100 392 82 36 81 145 273), lower := (rows 7 42 100 392 82 36 64 128 256), losses := [] }

theorem u10215 : Upper (D 6) (R 6) [6,40,96,384,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10215
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10216 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 392 82 48 69 133 261), lower := (rows 7 42 100 392 82 48 64 128 256), losses := [] }

theorem u10216 : Upper (D 6) (R 6) [6,40,96,384,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10216
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10217 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 25 336 34 100 228 356), lower := (rows 7 42 133 25 336 34 64 128 256), losses := [] }

theorem u10217 : Upper (D 6) (R 6) [6,40,129,17,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10217
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10218 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 336, targets := 5 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 42 133 25 336 36 98 226 354), lower := (rows 7 42 133 25 336 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 31 37 75 139 267), good := (rows 502 506 500 506 336 52 64 128 256) }] }

theorem u10218 : Upper (D 6) (R 6) [6,40,129,17,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10218
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10219 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 0, region := 368, targets := 1 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 7 42 133 25 336 96 102 166 294), lower := (rows 7 42 133 25 336 96 64 128 256), losses := [] }

theorem u10219 : Upper (D 6) (R 6) [6,40,129,17,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10219
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10220 : Route 9 := (fun mask => (mask,id))

def c10220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10220 : Upper (D 6) (R 6) [6,40,129,18,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,129,18,320,1] 13 (by decide) (choices 1) [4,32] r10220 c10220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1203
  · exact u1204

def r10221 : Route 9 := (fun mask => (mask,id))

def c10221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10221 : Upper (D 6) (R 6) [6,40,129,18,320,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,18,320,4] 13 (by decide) (choices 1) [1,32] r10221 c10221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1205
  · exact u1206

def b10222 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 26 336 96 101 165 293), lower := (rows 7 42 133 26 336 96 64 128 256), losses := [] }

theorem u10222 : Upper (D 6) (R 6) [6,40,129,18,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10222
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10223 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 7 42 133 28 336 33 98 226 354), lower := (rows 7 42 133 28 336 33 64 128 256), losses := [] }

theorem u10223 : Upper (D 6) (R 6) [6,40,129,20,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10223
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10224 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 133 28 336 34 97 225 353), lower := (rows 7 42 133 28 336 34 64 128 256), losses := [] }

theorem u10224 : Upper (D 6) (R 6) [6,40,129,20,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10224
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10225 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 42 133 28 336 96 99 163 291), lower := (rows 7 42 133 28 336 96 64 128 256), losses := [] }

theorem u10225 : Upper (D 6) (R 6) [6,40,129,20,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10225
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10226 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 73 52 34 336 464 336), lower := (rows 7 42 133 73 52 34 64 128 256), losses := [] }

theorem u10226 : Upper (D 6) (R 6) [6,40,129,65,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10226
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10227 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 73 52 48 322 450 322), lower := (rows 7 42 133 73 52 48 64 128 256), losses := [] }

theorem u10227 : Upper (D 6) (R 6) [6,40,129,65,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10227
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10228 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 73 52 96 338 402 274), lower := (rows 7 42 133 73 52 96 64 128 256), losses := [] }

theorem u10228 : Upper (D 6) (R 6) [6,40,129,65,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10228
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10229 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 133 73 52 288 82 210 338), lower := (rows 7 42 133 73 52 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 21 303 73 137 265), good := (rows 502 490 500 506 52 288 64 128 288) }] }

theorem u10229 : Upper (D 6) (R 6) [6,40,129,65,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10229
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10230 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 73 84 34 368 432 304), lower := (rows 7 42 133 73 84 34 64 128 256), losses := [] }

theorem u10230 : Upper (D 6) (R 6) [6,40,129,65,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10230
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10231 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 42 133 73 84 48 354 418 290), lower := (rows 7 42 133 73 84 48 64 128 256), losses := [] }

theorem u10231 : Upper (D 6) (R 6) [6,40,129,65,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10231
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10232 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 133 73 84 288 114 178 306), lower := (rows 7 42 133 73 84 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 21 303 73 137 265), good := (rows 502 490 500 506 116 288 64 128 288) }] }

theorem u10232 : Upper (D 6) (R 6) [6,40,129,65,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10232
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10233 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 133 73 112 34 340 404 276), lower := (rows 7 42 133 73 112 34 64 128 256), losses := [] }

theorem u10233 : Upper (D 6) (R 6) [6,40,129,65,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10233
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10234 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 336, targets := 5 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 42 133 73 112 36 338 402 274), lower := (rows 7 42 133 73 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 31 37 75 139 267), good := (rows 502 506 500 506 112 52 64 128 256) }] }

theorem u10234 : Upper (D 6) (R 6) [6,40,129,65,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10234
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10235 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 73 112 48 326 390 262), lower := (rows 7 42 133 73 112 48 64 128 256), losses := [] }

theorem u10235 : Upper (D 6) (R 6) [6,40,129,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10235
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10236 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 133 73 112 288 86 150 278), lower := (rows 7 42 133 73 112 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 29 301 65 129 257), good := (rows 502 58 500 506 112 288 64 128 288) }] }

theorem u10236 : Upper (D 6) (R 6) [6,40,129,65,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10236
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10237 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 336, targets := 5 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 42 133 73 274 36 112 240 368), lower := (rows 7 42 133 73 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 27 37 79 143 271), good := (rows 502 506 500 506 466 484 64 128 256) }] }

theorem u10237 : Upper (D 6) (R 6) [6,40,129,65,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10237
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10238 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 133 73 274 48 100 228 356), lower := (rows 7 42 133 73 274 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 25 63 69 133 261), good := (rows 502 58 500 506 306 48 64 128 256) }] }

theorem u10238 : Upper (D 6) (R 6) [6,40,129,65,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10238
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10239 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 73 274 96 116 180 308), lower := (rows 7 42 133 73 274 96 64 128 256), losses := [] }

theorem u10239 : Upper (D 6) (R 6) [6,40,129,65,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10239
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10240 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 73 276 34 112 240 368), lower := (rows 7 42 133 73 276 34 64 128 256), losses := [] }

theorem u10240 : Upper (D 6) (R 6) [6,40,129,65,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10240
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10241 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 133 73 276 48 98 226 354), lower := (rows 7 42 133 73 276 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 21 61 75 139 267), good := (rows 502 490 500 506 308 48 64 128 256) }] }

theorem u10241 : Upper (D 6) (R 6) [6,40,129,65,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10241
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10242 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 73 276 96 114 178 306), lower := (rows 7 42 133 73 276 96 64 128 256), losses := [] }

theorem u10242 : Upper (D 6) (R 6) [6,40,129,65,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10242
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10243 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 73 304 34 84 212 340), lower := (rows 7 42 133 73 304 34 64 128 256), losses := [] }

theorem u10243 : Upper (D 6) (R 6) [6,40,129,65,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10243
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10244 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 336, targets := 5 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 42 133 73 304 36 82 210 338), lower := (rows 7 42 133 73 304 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 31 37 75 139 267), good := (rows 502 506 500 506 304 52 64 128 256) }] }

theorem u10244 : Upper (D 6) (R 6) [6,40,129,65,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10244
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10245 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 133 73 304 48 70 198 326), lower := (rows 7 42 133 73 304 48 64 128 256), losses := [] }

theorem u10245 : Upper (D 6) (R 6) [6,40,129,65,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10245
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10246 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 73 304 96 86 150 278), lower := (rows 7 42 133 73 304 96 64 128 256), losses := [] }

theorem u10246 : Upper (D 6) (R 6) [6,40,129,65,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10246
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10247 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 73 336 34 116 180 308), lower := (rows 7 42 133 73 336 34 64 128 256), losses := [] }

theorem u10247 : Upper (D 6) (R 6) [6,40,129,65,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10247
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10248 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 336, targets := 5 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 42 133 73 336 36 114 178 306), lower := (rows 7 42 133 73 336 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 31 37 75 139 267), good := (rows 502 506 500 506 336 52 64 128 256) }] }

theorem u10248 : Upper (D 6) (R 6) [6,40,129,65,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10248
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10249 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 42 133 73 336 48 102 166 294), lower := (rows 7 42 133 73 336 48 64 128 256), losses := [] }

theorem u10249 : Upper (D 6) (R 6) [6,40,129,65,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10249
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10250 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 330, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 74 52 33 336 464 336), lower := (rows 7 42 133 74 52 33 64 128 256), losses := [] }

theorem u10250 : Upper (D 6) (R 6) [6,40,129,66,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10250
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10251 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 74 52 48 321 449 321), lower := (rows 7 42 133 74 52 48 64 128 256), losses := [] }

theorem u10251 : Upper (D 6) (R 6) [6,40,129,66,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10251
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10252 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 74 52 96 337 401 273), lower := (rows 7 42 133 74 52 96 64 128 256), losses := [] }

theorem u10252 : Upper (D 6) (R 6) [6,40,129,66,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10252
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10253 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 42 133 74 52 288 81 209 337), lower := (rows 7 42 133 74 52 288 64 128 256), losses := [] }

theorem u10253 : Upper (D 6) (R 6) [6,40,129,66,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10253
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10254 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 133 74 84 33 368 432 304), lower := (rows 7 42 133 74 84 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 37 80 144 272), good := (rows 35 42 161 74 506 33 64 128 256) }] }

theorem u10254 : Upper (D 6) (R 6) [6,40,129,66,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10254
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10255 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 74 84 48 353 417 289), lower := (rows 7 42 133 74 84 48 64 128 256), losses := [] }

theorem u10255 : Upper (D 6) (R 6) [6,40,129,66,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10255
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10256 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 42 133 74 84 288 113 177 305), lower := (rows 7 42 133 74 84 288 64 128 256), losses := [] }

theorem u10256 : Upper (D 6) (R 6) [6,40,129,66,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10256
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10257 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 133 74 273 36 112 240 368), lower := (rows 7 42 133 74 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 80 144 272), good := (rows 38 42 164 74 506 36 64 128 256) }] }

theorem u10257 : Upper (D 6) (R 6) [6,40,129,66,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10257
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10258 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 42 133 74 273 48 100 228 356), lower := (rows 7 42 133 74 273 48 64 128 256), losses := [] }

theorem u10258 : Upper (D 6) (R 6) [6,40,129,66,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10258
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10259 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 74 273 96 116 180 308), lower := (rows 7 42 133 74 273 96 64 128 256), losses := [] }

theorem u10259 : Upper (D 6) (R 6) [6,40,129,66,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10259
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10259
end Delivery.IrregularNine14.P06
