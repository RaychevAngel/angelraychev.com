import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0019
import IrregularNine14P07C0020

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12240 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 56 400 34 193 193 449), lower := (rows 7 35 76 56 400 34 64 128 256), losses := [] }

theorem u12240 : Upper (D 7) (R 7) [6,33,72,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12241 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 56 400 96 195 131 387), lower := (rows 7 35 76 56 400 96 64 128 256), losses := [] }

theorem u12241 : Upper (D 7) (R 7) [6,33,72,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12242 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 76 56 400 160 67 195 323), lower := (rows 7 35 76 56 400 160 64 128 256), losses := [] }

theorem u12242 : Upper (D 7) (R 7) [6,33,72,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12243 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 137 82 48 480 416 416), lower := (rows 7 35 76 137 82 48 64 128 256), losses := [] }

theorem u12243 : Upper (D 7) (R 7) [6,33,72,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12243 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12244 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 82 160 368 432 304), lower := (rows 7 35 76 137 82 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 191 91 155 283), good := (rows 502 498 492 508 498 160 64 160 256) }] }

theorem u12244 : Upper (D 7) (R 7) [6,33,72,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12245 : Route 9 := (fun mask => (mask,id))

def c12245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12245 : Upper (D 7) (R 7) [6,33,72,129,66,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,66,256] 13 (by decide) (choices 1) [16,32,128] r12245 c12245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1179
  · exact u1180
  · exact u1181

def b12246 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 137 112 34 464 400 400), lower := (rows 7 35 76 137 112 34 64 128 256), losses := [] }

theorem u12246 : Upper (D 7) (R 7) [6,33,72,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12247 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 137 112 48 450 386 386), lower := (rows 7 35 76 137 112 48 64 128 256), losses := [] }

theorem u12247 : Upper (D 7) (R 7) [6,33,72,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12247 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12248 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 112 160 338 402 274), lower := (rows 7 35 76 137 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 31 171 67 131 259), good := (rows 502 498 124 508 112 160 64 160 256) }] }

theorem u12248 : Upper (D 7) (R 7) [6,33,72,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12249 : Route 9 := (fun mask => (mask,id))

def c12249 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12249 : Upper (D 7) (R 7) [6,33,72,129,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,96,256] 13 (by decide) (choices 1) [2,16,128] r12249 c12249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1182
  · exact u1183
  · exact u1184

def b12250 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 460, targets := 2 },{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 7 35 76 137 146 48 352 480 352), lower := (rows 7 35 76 137 146 48 64 128 256), losses := [] }

theorem u12250 : Upper (D 7) (R 7) [6,33,72,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12250 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12251 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 137 146 96 368 432 304), lower := (rows 7 35 76 137 146 96 64 128 256), losses := [] }

theorem u12251 : Upper (D 7) (R 7) [6,33,72,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12252 : Route 9 := (fun mask => (mask,id))

def c12252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12252 : Upper (D 7) (R 7) [6,33,72,129,130,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,130,256] 13 (by decide) (choices 1) [16,32] r12252 c12252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1185
  · exact u1186

def b12253 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 137 176 34 336 464 336), lower := (rows 7 35 76 137 176 34 64 128 256), losses := [] }

theorem u12253 : Upper (D 7) (R 7) [6,33,72,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12254 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 137 176 48 322 450 322), lower := (rows 7 35 76 137 176 48 64 128 256), losses := [] }

theorem u12254 : Upper (D 7) (R 7) [6,33,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12254 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12255 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 137 176 96 338 402 274), lower := (rows 7 35 76 137 176 96 64 128 256), losses := [] }

theorem u12255 : Upper (D 7) (R 7) [6,33,72,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12256 : Route 9 := (fun mask => (mask,id))

def c12256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12256 : Upper (D 7) (R 7) [6,33,72,129,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,160,256] 13 (by decide) (choices 1) [2,16] r12256 c12256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1187
  · exact u1188

def b12257 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 137 208 34 368 432 304), lower := (rows 7 35 76 137 208 34 64 128 256), losses := [] }

theorem u12257 : Upper (D 7) (R 7) [6,33,72,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12258 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(2,0),(3,6),(4,0)], upper := (rows 7 35 76 137 208 48 354 418 290), lower := (rows 7 35 76 137 208 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 63 67 131 259), good := (rows 502 498 124 508 240 48 64 128 256) }] }

theorem u12258 : Upper (D 7) (R 7) [6,33,72,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12258 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12259 : Route 9 := (fun mask => (mask,id))

def c12259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12259 : Upper (D 7) (R 7) [6,33,72,129,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,192,256] 13 (by decide) (choices 1) [2,16,32] r12259 c12259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1189
  · exact u1190
  · exact u1191

def b12260 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 204, targets := 2 },{ cop := 0, region := 496, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 35 76 137 274 48 224 224 480), lower := (rows 7 35 76 137 274 48 64 128 256), losses := [] }

theorem u12260 : Upper (D 7) (R 7) [6,33,72,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12260 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12261 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 137 274 96 240 176 432), lower := (rows 7 35 76 137 274 96 64 128 256), losses := [] }

theorem u12261 : Upper (D 7) (R 7) [6,33,72,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12262 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 274 160 112 240 368), lower := (rows 7 35 76 137 274 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 191 91 155 283), good := (rows 502 498 492 508 498 160 64 160 256) }] }

theorem u12262 : Upper (D 7) (R 7) [6,33,72,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12263 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 137 304 34 208 208 464), lower := (rows 7 35 76 137 304 34 64 128 256), losses := [] }

theorem u12263 : Upper (D 7) (R 7) [6,33,72,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12264 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 35 76 137 304 48 194 194 450), lower := (rows 7 35 76 137 304 48 64 128 256), losses := [] }

theorem u12264 : Upper (D 7) (R 7) [6,33,72,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12264 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12265 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 137 304 96 210 146 402), lower := (rows 7 35 76 137 304 96 64 128 256), losses := [] }

theorem u12265 : Upper (D 7) (R 7) [6,33,72,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12266 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 304 160 82 210 338), lower := (rows 7 35 76 137 304 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 171 67 131 259), good := (rows 502 498 124 508 304 160 64 160 256) }] }

theorem u12266 : Upper (D 7) (R 7) [6,33,72,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12267 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 137 336 34 240 176 432), lower := (rows 7 35 76 137 336 34 64 128 256), losses := [] }

theorem u12267 : Upper (D 7) (R 7) [6,33,72,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12268 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 1, region := 136, targets := 64 }], pairs := [(2,0),(3,6),(4,0)], upper := (rows 7 35 76 137 336 48 226 162 418), lower := (rows 7 35 76 137 336 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 63 67 131 259), good := (rows 502 498 124 508 368 48 64 128 256) }] }

theorem u12268 : Upper (D 7) (R 7) [6,33,72,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12268 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12269 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 336 160 114 178 306), lower := (rows 7 35 76 137 336 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 171 67 131 259), good := (rows 502 498 124 508 336 160 64 160 256) }] }

theorem u12269 : Upper (D 7) (R 7) [6,33,72,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12270 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 137 400 34 112 240 368), lower := (rows 7 35 76 137 400 34 64 128 256), losses := [] }

theorem u12270 : Upper (D 7) (R 7) [6,33,72,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12271 : Route 9 := (fun mask => (mask,id))

def c12271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12271 : Upper (D 7) (R 7) [6,33,72,129,384,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,384,16] 13 (by decide) (choices 1) [2,32] r12271 c12271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1192
  · exact u1193

def b12272 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 137 400 96 114 178 306), lower := (rows 7 35 76 137 400 96 64 128 256), losses := [] }

theorem u12272 : Upper (D 7) (R 7) [6,33,72,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12273 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 138 112 33 464 400 400), lower := (rows 7 35 76 138 112 33 64 128 256), losses := [] }

theorem u12273 : Upper (D 7) (R 7) [6,33,72,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12274 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 138 112 48 449 385 385), lower := (rows 7 35 76 138 112 48 64 128 256), losses := [] }

theorem u12274 : Upper (D 7) (R 7) [6,33,72,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12274 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12275 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 336, targets := 128 }], pairs := [(2,1),(4,0),(4,1),(4,7)], upper := (rows 7 35 76 138 112 160 337 401 273), lower := (rows 7 35 76 138 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 22 34 124 170 112 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 31 171 67 131 259), good := (rows 501 497 124 508 112 160 64 160 256) }] }

theorem u12275 : Upper (D 7) (R 7) [6,33,72,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12276 : Route 9 := (fun mask => (mask,id))

def c12276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12276 : Upper (D 7) (R 7) [6,33,72,130,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,96,256] 13 (by decide) (choices 1) [1,16,128] r12276 c12276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1194
  · exact u1195
  · exact u1196

def b12277 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 76 138 145 48 352 480 352), lower := (rows 7 35 76 138 145 48 64 128 256), losses := [] }

theorem u12277 : Upper (D 7) (R 7) [6,33,72,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12277 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12278 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 138 145 96 368 432 304), lower := (rows 7 35 76 138 145 96 64 128 256), losses := [] }

theorem u12278 : Upper (D 7) (R 7) [6,33,72,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12279 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,7),(2,1),(4,1)], upper := (rows 7 35 76 138 145 288 112 240 368), lower := (rows 7 35 76 138 145 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 319 91 155 283), good := (rows 501 497 492 508 497 288 64 128 288) }] }

theorem u12279 : Upper (D 7) (R 7) [6,33,72,130,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12279 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12280 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 138 176 33 336 464 336), lower := (rows 7 35 76 138 176 33 64 128 256), losses := [] }

theorem u12280 : Upper (D 7) (R 7) [6,33,72,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12281 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 138 176 48 321 449 321), lower := (rows 7 35 76 138 176 48 64 128 256), losses := [] }

theorem u12281 : Upper (D 7) (R 7) [6,33,72,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12281 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12282 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 138 176 96 337 401 273), lower := (rows 7 35 76 138 176 96 64 128 256), losses := [] }

theorem u12282 : Upper (D 7) (R 7) [6,33,72,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12283 : Route 9 := (fun mask => (mask,id))

def c12283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12283 : Upper (D 7) (R 7) [6,33,72,130,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,160,256] 13 (by decide) (choices 1) [1,16] r12283 c12283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1197
  · exact u1198

def b12284 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 138 208 33 368 432 304), lower := (rows 7 35 76 138 208 33 64 128 256), losses := [] }

theorem u12284 : Upper (D 7) (R 7) [6,33,72,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12285 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 392, targets := 64 }], pairs := [(2,1),(3,6),(4,1)], upper := (rows 7 35 76 138 208 48 353 417 289), lower := (rows 7 35 76 138 208 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 63 67 131 259), good := (rows 501 497 124 508 240 48 64 128 256) }] }

theorem u12285 : Upper (D 7) (R 7) [6,33,72,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12285 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12286 : Route 9 := (fun mask => (mask,id))

def c12286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12286 : Upper (D 7) (R 7) [6,33,72,130,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,192,256] 13 (by decide) (choices 1) [1,16,32] r12286 c12286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1199
  · exact u1200
  · exact u1201

def b12287 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 76 138 273 48 224 224 480), lower := (rows 7 35 76 138 273 48 64 128 256), losses := [] }

theorem u12287 : Upper (D 7) (R 7) [6,33,72,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12287 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12288 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 138 273 96 240 176 432), lower := (rows 7 35 76 138 273 96 64 128 256), losses := [] }

theorem u12288 : Upper (D 7) (R 7) [6,33,72,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12289 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(2,1),(4,1),(4,7)], upper := (rows 7 35 76 138 273 160 112 240 368), lower := (rows 7 35 76 138 273 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 191 91 155 283), good := (rows 501 497 492 508 497 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 170 273 160 0 160 256) }] }

theorem u12289 : Upper (D 7) (R 7) [6,33,72,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12290 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 138 304 33 208 208 464), lower := (rows 7 35 76 138 304 33 64 128 256), losses := [] }

theorem u12290 : Upper (D 7) (R 7) [6,33,72,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12291 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 35 76 138 304 48 193 193 449), lower := (rows 7 35 76 138 304 48 64 128 256), losses := [] }

theorem u12291 : Upper (D 7) (R 7) [6,33,72,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12291 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12292 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 138 304 96 209 145 401), lower := (rows 7 35 76 138 304 96 64 128 256), losses := [] }

theorem u12292 : Upper (D 7) (R 7) [6,33,72,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12293 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(2,1),(4,1),(4,7)], upper := (rows 7 35 76 138 304 160 81 209 337), lower := (rows 7 35 76 138 304 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 171 67 131 259), good := (rows 501 497 124 508 304 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 170 304 160 0 160 256) }] }

theorem u12293 : Upper (D 7) (R 7) [6,33,72,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12294 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 138 336 33 240 176 432), lower := (rows 7 35 76 138 336 33 64 128 256), losses := [] }

theorem u12294 : Upper (D 7) (R 7) [6,33,72,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12295 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 136, targets := 64 }], pairs := [(2,1),(3,6),(4,1)], upper := (rows 7 35 76 138 336 48 225 161 417), lower := (rows 7 35 76 138 336 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 63 67 131 259), good := (rows 501 497 124 508 368 48 64 128 256) }] }

theorem u12295 : Upper (D 7) (R 7) [6,33,72,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12295 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12296 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(2,1),(4,1),(4,7)], upper := (rows 7 35 76 138 336 160 113 177 305), lower := (rows 7 35 76 138 336 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 171 67 131 259), good := (rows 501 497 124 508 336 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 170 272 160 0 160 256) }] }

theorem u12296 : Upper (D 7) (R 7) [6,33,72,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12297 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 138 400 33 112 240 368), lower := (rows 7 35 76 138 400 33 64 128 256), losses := [] }

theorem u12297 : Upper (D 7) (R 7) [6,33,72,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12298 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 496, targets := 2 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 7 35 76 138 400 48 97 225 353), lower := (rows 7 35 76 138 400 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 63 67 131 259), good := (rows 501 497 124 508 432 48 64 128 256) },{ target := 7, region := (rows 9 2 12 8 16 48 66 0 258), good := (rows 327 355 77 335 304 48 64 0 256) }] }

theorem u12298 : Upper (D 7) (R 7) [6,33,72,130,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12298 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12299 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 138 400 96 113 177 305), lower := (rows 7 35 76 138 400 96 64 128 256), losses := [] }

theorem u12299 : Upper (D 7) (R 7) [6,33,72,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12299
end Delivery.IrregularNine14.P07
