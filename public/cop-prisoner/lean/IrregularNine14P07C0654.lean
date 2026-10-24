import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0451
import IrregularNine14P07C0452
import IrregularNine14P07C0453

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39240 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5),(4,0)], upper := (rows 37 290 196 88 152 35 67 131 259), lower := (rows 37 290 196 88 152 32 64 128 256), losses := [] }

theorem u39240 : Upper (D 7) (R 7) [36,288,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39241 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 322 7 11 56 240 208 208 464), lower := (rows 37 322 7 11 56 32 64 128 256), losses := [] }

theorem u39241 : Upper (D 7) (R 7) [36,320,3,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39242 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 322 7 11 88 176 240 176 432), lower := (rows 37 322 7 11 88 32 64 128 256), losses := [] }

theorem u39242 : Upper (D 7) (R 7) [36,320,3,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39243 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 322 7 11 112 184 216 152 408), lower := (rows 37 322 7 11 112 32 64 128 256), losses := [] }

theorem u39243 : Upper (D 7) (R 7) [36,320,3,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39244 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 322 7 11 152 240 240 240 496), lower := (rows 37 322 7 11 152 32 64 128 256), losses := [] }

theorem u39244 : Upper (D 7) (R 7) [36,320,3,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39245 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 322 7 11 176 248 216 216 472), lower := (rows 37 322 7 11 176 32 64 128 256), losses := [] }

theorem u39245 : Upper (D 7) (R 7) [36,320,3,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39246 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 322 7 11 208 184 248 184 440), lower := (rows 37 322 7 11 208 32 64 128 256), losses := [] }

theorem u39246 : Upper (D 7) (R 7) [36,320,3,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39247 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 37 322 7 25 26 224 224 224 480), lower := (rows 37 322 7 25 26 32 64 128 256), losses := [] }

theorem u39247 : Upper (D 7) (R 7) [36,320,3,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39248 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 25 50 232 200 200 456), lower := (rows 37 322 7 25 50 32 64 128 256), losses := [] }

theorem u39248 : Upper (D 7) (R 7) [36,320,3,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39249 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 7 25 56 226 194 194 450), lower := (rows 37 322 7 25 56 32 64 128 256), losses := [] }

theorem u39249 : Upper (D 7) (R 7) [36,320,3,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39250 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 7 25 82 168 232 168 424), lower := (rows 37 322 7 25 82 32 64 128 256), losses := [] }

theorem u39250 : Upper (D 7) (R 7) [36,320,3,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39251 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 322 7 25 88 162 226 162 418), lower := (rows 37 322 7 25 88 32 64 128 256), losses := [] }

theorem u39251 : Upper (D 7) (R 7) [36,320,3,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39252 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 322 7 25 112 170 202 138 394), lower := (rows 37 322 7 25 112 32 64 128 256), losses := [] }

theorem u39252 : Upper (D 7) (R 7) [36,320,3,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39253 : Route 9 := (fun mask => (mask,id))

def c39253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39253 : Upper (D 7) (R 7) [36,320,3,17,130] 13 := by
  apply FastRouting.sound _ _ [36,320,3,17,130] 13 (by decide) (choices 1) [8,64,128] r39253 c39253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27118
  · exact u27119
  · exact u27120

def r39254 : Route 9 := (fun mask => (mask,id))

def c39254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39254 : Upper (D 7) (R 7) [36,320,3,17,136] 13 := by
  apply FastRouting.sound _ _ [36,320,3,17,136] 13 (by decide) (choices 1) [2,64,128] r39254 c39254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27121
  · exact u27122
  · exact u27123

def b39255 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 322 7 25 176 234 202 202 458), lower := (rows 37 322 7 25 176 32 64 128 256), losses := [] }

theorem u39255 : Upper (D 7) (R 7) [36,320,3,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39256 : Route 9 := (fun mask => (mask,id))

def c39256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39256 : Upper (D 7) (R 7) [36,320,3,17,192] 13 := by
  apply FastRouting.sound _ _ [36,320,3,17,192] 13 (by decide) (choices 1) [2,8,128] r39256 c39256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27124
  · exact u27125
  · exact u27126

def b39257 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 7 26 49 232 200 200 456), lower := (rows 37 322 7 26 49 32 64 128 256), losses := [] }

theorem u39257 : Upper (D 7) (R 7) [36,320,3,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39258 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(3,0)], upper := (rows 37 322 7 26 56 225 193 193 449), lower := (rows 37 322 7 26 56 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 32 64 128 256), good := (rows 60 322 30 26 56 32 64 128 256) }] }

theorem u39258 : Upper (D 7) (R 7) [36,320,3,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39259 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 322 7 26 81 168 232 168 424), lower := (rows 37 322 7 26 81 32 64 128 256), losses := [] }

theorem u39259 : Upper (D 7) (R 7) [36,320,3,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39260 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 322 7 26 88 161 225 161 417), lower := (rows 37 322 7 26 88 32 64 128 256), losses := [] }

theorem u39260 : Upper (D 7) (R 7) [36,320,3,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39261 : Route 9 := (fun mask => (mask,id))

def c39261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39261 : Upper (D 7) (R 7) [36,320,3,18,96] 13 := by
  apply FastRouting.sound _ _ [36,320,3,18,96] 13 (by decide) (choices 1) [1,8,128] r39261 c39261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27127
  · exact u27128
  · exact u27129

def r39262 : Route 9 := (fun mask => (mask,id))

def c39262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39262 : Upper (D 7) (R 7) [36,320,3,18,129] 13 := by
  apply FastRouting.sound _ _ [36,320,3,18,129] 13 (by decide) (choices 1) [8,64,128] r39262 c39262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27130
  · exact u27131
  · exact u27132

def r39263 : Route 9 := (fun mask => (mask,id))

def c39263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39263 : Upper (D 7) (R 7) [36,320,3,18,136] 13 := by
  apply FastRouting.sound _ _ [36,320,3,18,136] 13 (by decide) (choices 1) [1,64,128] r39263 c39263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27133
  · exact u27134
  · exact u27135

def r39264 : Route 9 := (fun mask => (mask,id))

def c39264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39264 : Upper (D 7) (R 7) [36,320,3,18,160] 13 := by
  apply FastRouting.sound _ _ [36,320,3,18,160] 13 (by decide) (choices 1) [1,8,64,128] r39264 c39264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27136
  · exact u27137
  · exact u27138
  · exact u27139

def r39265 : Route 9 := (fun mask => (mask,id))

def c39265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39265 : Upper (D 7) (R 7) [36,320,3,18,192] 13 := by
  apply FastRouting.sound _ _ [36,320,3,18,192] 13 (by decide) (choices 1) [1,8,128] r39265 c39265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27140
  · exact u27141
  · exact u27142

def b39266 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 7 41 88 178 210 146 402), lower := (rows 37 322 7 41 88 32 64 128 256), losses := [] }

theorem u39266 : Upper (D 7) (R 7) [36,320,3,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39267 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 7 41 146 248 216 216 472), lower := (rows 37 322 7 41 146 32 64 128 256), losses := [] }

theorem u39267 : Upper (D 7) (R 7) [36,320,3,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39268 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 7 41 152 242 210 210 466), lower := (rows 37 322 7 41 152 32 64 128 256), losses := [] }

theorem u39268 : Upper (D 7) (R 7) [36,320,3,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39269 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 7 41 208 186 218 154 410), lower := (rows 37 322 7 41 208 32 64 128 256), losses := [] }

theorem u39269 : Upper (D 7) (R 7) [36,320,3,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39270 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 42 81 184 216 152 408), lower := (rows 37 322 7 42 81 32 64 128 256), losses := [] }

theorem u39270 : Upper (D 7) (R 7) [36,320,3,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39271 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 42 88 177 209 145 401), lower := (rows 37 322 7 42 88 32 64 128 256), losses := [] }

theorem u39271 : Upper (D 7) (R 7) [36,320,3,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39272 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 42 145 248 216 216 472), lower := (rows 37 322 7 42 145 32 64 128 256), losses := [] }

theorem u39272 : Upper (D 7) (R 7) [36,320,3,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39273 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 42 152 241 209 209 465), lower := (rows 37 322 7 42 152 32 64 128 256), losses := [] }

theorem u39273 : Upper (D 7) (R 7) [36,320,3,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39274 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 42 208 185 217 153 409), lower := (rows 37 322 7 42 208 32 64 128 256), losses := [] }

theorem u39274 : Upper (D 7) (R 7) [36,320,3,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39275 : Route 9 := (fun mask => (mask,id))

def c39275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39275 : Upper (D 7) (R 7) [36,320,3,48,65] 13 := by
  apply FastRouting.sound _ _ [36,320,3,48,65] 13 (by decide) (choices 1) [2,8,128] r39275 c39275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27143
  · exact u27144
  · exact u27145

def b39276 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 7 56 82 169 201 137 393), lower := (rows 37 322 7 56 82 32 64 128 256), losses := [] }

theorem u39276 : Upper (D 7) (R 7) [36,320,3,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39277 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 37 322 7 56 88 163 195 131 387), lower := (rows 37 322 7 56 88 32 64 128 256), losses := [] }

theorem u39277 : Upper (D 7) (R 7) [36,320,3,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39278 : Route 9 := (fun mask => (mask,id))

def c39278 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39278 : Upper (D 7) (R 7) [36,320,3,48,129] 13 := by
  apply FastRouting.sound _ _ [36,320,3,48,129] 13 (by decide) (choices 1) [2,8,64,128] r39278 c39278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27146
  · exact u27147
  · exact u27148
  · exact u27149

def r39279 : Route 9 := (fun mask => (mask,id))

def c39279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39279 : Upper (D 7) (R 7) [36,320,3,48,130] 13 := by
  apply FastRouting.sound _ _ [36,320,3,48,130] 13 (by decide) (choices 1) [1,8,64,128] r39279 c39279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27150
  · exact u27151
  · exact u27152
  · exact u27153

def r39280 : Route 9 := (fun mask => (mask,id))

def c39280 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39280 : Upper (D 7) (R 7) [36,320,3,48,136] 13 := by
  apply FastRouting.sound _ _ [36,320,3,48,136] 13 (by decide) (choices 1) [1,2,64,128] r39280 c39280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27154
  · exact u27155
  · exact u27156
  · exact u27157

def r39281 : Route 9 := (fun mask => (mask,id))

def c39281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39281 : Upper (D 7) (R 7) [36,320,3,48,192] 13 := by
  apply FastRouting.sound _ _ [36,320,3,48,192] 13 (by decide) (choices 1) [1,2,8,128] r39281 c39281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27158
  · exact u27159
  · exact u27160
  · exact u27161

def r39282 : Route 9 := (fun mask => (mask,id))

def c39282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39282 : Upper (D 7) (R 7) [36,320,3,65,130] 13 := by
  apply FastRouting.sound _ _ [36,320,3,65,130] 13 (by decide) (choices 1) [8,16,128] r39282 c39282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27162
  · exact u27163
  · exact u27164

def r39283 : Route 9 := (fun mask => (mask,id))

def c39283 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39283 : Upper (D 7) (R 7) [36,320,3,65,136] 13 := by
  apply FastRouting.sound _ _ [36,320,3,65,136] 13 (by decide) (choices 1) [2,16,128] r39283 c39283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27165
  · exact u27166
  · exact u27167

def r39284 : Route 9 := (fun mask => (mask,id))

def c39284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39284 : Upper (D 7) (R 7) [36,320,3,65,160] 13 := by
  apply FastRouting.sound _ _ [36,320,3,65,160] 13 (by decide) (choices 1) [2,8,16,128] r39284 c39284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27168
  · exact u27169
  · exact u27170
  · exact u27171

def b39285 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 7 74 145 184 248 184 440), lower := (rows 37 322 7 74 145 32 64 128 256), losses := [] }

theorem u39285 : Upper (D 7) (R 7) [36,320,3,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39286 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 7 74 152 177 241 177 433), lower := (rows 37 322 7 74 152 32 64 128 256), losses := [] }

theorem u39286 : Upper (D 7) (R 7) [36,320,3,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39287 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 7 74 176 185 217 153 409), lower := (rows 37 322 7 74 176 32 64 128 256), losses := [] }

theorem u39287 : Upper (D 7) (R 7) [36,320,3,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39288 : Route 9 := (fun mask => (mask,id))

def c39288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39288 : Upper (D 7) (R 7) [36,320,3,80,129] 13 := by
  apply FastRouting.sound _ _ [36,320,3,80,129] 13 (by decide) (choices 1) [2,8,128] r39288 c39288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27172
  · exact u27173
  · exact u27174

def r39289 : Route 9 := (fun mask => (mask,id))

def c39289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39289 : Upper (D 7) (R 7) [36,320,3,80,130] 13 := by
  apply FastRouting.sound _ _ [36,320,3,80,130] 13 (by decide) (choices 1) [1,8,128] r39289 c39289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27175
  · exact u27176
  · exact u27177

def r39290 : Route 9 := (fun mask => (mask,id))

def c39290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39290 : Upper (D 7) (R 7) [36,320,3,80,136] 13 := by
  apply FastRouting.sound _ _ [36,320,3,80,136] 13 (by decide) (choices 1) [1,2,128] r39290 c39290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27178
  · exact u27179
  · exact u27180

def r39291 : Route 9 := (fun mask => (mask,id))

def c39291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39291 : Upper (D 7) (R 7) [36,320,3,80,160] 13 := by
  apply FastRouting.sound _ _ [36,320,3,80,160] 13 (by decide) (choices 1) [1,2,8,128] r39291 c39291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27181
  · exact u27182
  · exact u27183
  · exact u27184

def r39292 : Route 9 := (fun mask => (mask,id))

def c39292 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39292 : Upper (D 7) (R 7) [36,320,3,96,129] 13 := by
  apply FastRouting.sound _ _ [36,320,3,96,129] 13 (by decide) (choices 1) [2,8,16,128] r39292 c39292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27185
  · exact u27186
  · exact u27187
  · exact u27188

def r39293 : Route 9 := (fun mask => (mask,id))

def c39293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39293 : Upper (D 7) (R 7) [36,320,3,96,130] 13 := by
  apply FastRouting.sound _ _ [36,320,3,96,130] 13 (by decide) (choices 1) [1,8,16,128] r39293 c39293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27189
  · exact u27190
  · exact u27191
  · exact u27192

def r39294 : Route 9 := (fun mask => (mask,id))

def c39294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39294 : Upper (D 7) (R 7) [36,320,3,96,136] 13 := by
  apply FastRouting.sound _ _ [36,320,3,96,136] 13 (by decide) (choices 1) [1,2,16,128] r39294 c39294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27193
  · exact u27194
  · exact u27195
  · exact u27196

def r39295 : Route 9 := (fun mask => (mask,id))

def c39295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39295 : Upper (D 7) (R 7) [36,320,3,129,130] 13 := by
  apply FastRouting.sound _ _ [36,320,3,129,130] 13 (by decide) (choices 1) [8,16,64] r39295 c39295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27197
  · exact u27198
  · exact u27199

def b39296 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(4,1),(4,5),(4,6)], upper := (rows 37 322 7 137 152 114 114 242 370), lower := (rows 37 322 7 137 152 32 64 128 256), losses := [] }

theorem u39296 : Upper (D 7) (R 7) [36,320,3,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39297 : Route 9 := (fun mask => (mask,id))

def c39297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39297 : Upper (D 7) (R 7) [36,320,3,129,160] 13 := by
  apply FastRouting.sound _ _ [36,320,3,129,160] 13 (by decide) (choices 1) [2,8,16,64] r39297 c39297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27200
  · exact u27201
  · exact u27202
  · exact u27203

def r39298 : Route 9 := (fun mask => (mask,id))

def c39298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39298 : Upper (D 7) (R 7) [36,320,3,129,192] 13 := by
  apply FastRouting.sound _ _ [36,320,3,129,192] 13 (by decide) (choices 1) [2,8,16] r39298 c39298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27204
  · exact u27205
  · exact u27206

def b39299 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 322 7 138 152 113 113 241 369), lower := (rows 37 322 7 138 152 32 64 128 256), losses := [] }

theorem u39299 : Upper (D 7) (R 7) [36,320,3,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39299
end Delivery.IrregularNine14.P07
