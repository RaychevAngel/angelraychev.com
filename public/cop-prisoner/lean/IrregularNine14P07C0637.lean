import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0423
import IrregularNine14P07C0424

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38220 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u38220 : Upper (D 7) (R 7) [36,192,257,3,34] 13 := by
  apply FastRouting.sound _ _ [36,192,257,3,34] 13 (by decide) (choices 1) [8,16,64] r38220 c38220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25407
  · exact u25408
  · exact u25409

def r38221 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38221 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38221 : Upper (D 7) (R 7) [36,192,257,3,40] 13 := by
  apply FastRouting.sound _ _ [36,192,257,3,40] 13 (by decide) (choices 1) [2,16,64] r38221 c38221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25410
  · exact u25411
  · exact u25412

def b38222 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 261 11 82 184 248 184 440), lower := (rows 37 194 261 11 82 32 64 128 256), losses := [] }

theorem u38222 : Upper (D 7) (R 7) [36,192,257,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38223 : Route 9 := (fun mask => (mask,id))

def c38223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38223 : Upper (D 7) (R 7) [36,192,257,3,72] 13 := by
  apply FastRouting.sound _ _ [36,192,257,3,72] 13 (by decide) (choices 1) [2,16,128] r38223 c38223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25413
  · exact u25414
  · exact u25415

def r38224 : Route 9 := (fun mask => (mask,id))

def c38224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38224 : Upper (D 7) (R 7) [36,192,257,3,96] 13 := by
  apply FastRouting.sound _ _ [36,192,257,3,96] 13 (by decide) (choices 1) [2,8,16,128] r38224 c38224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25416
  · exact u25417
  · exact u25418
  · exact u25419

def b38225 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 261 11 208 58 122 186 314), lower := (rows 37 194 261 11 208 32 64 128 256), losses := [] }

theorem u38225 : Upper (D 7) (R 7) [36,192,257,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38226 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38226 : Upper (D 7) (R 7) [36,192,257,17,10] 13 := by
  apply FastRouting.sound _ _ [36,192,257,17,10] 13 (by decide) (choices 1) [2,64] r38226 c38226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25420
  · exact u25421

def b38227 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 194 261 25 50 234 202 202 458), lower := (rows 37 194 261 25 50 32 64 128 256), losses := [] }

theorem u38227 : Upper (D 7) (R 7) [36,192,257,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38228 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 261 25 56 226 194 194 450), lower := (rows 37 194 261 25 56 32 64 128 256), losses := [] }

theorem u38228 : Upper (D 7) (R 7) [36,192,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38229 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 261 25 82 170 234 170 426), lower := (rows 37 194 261 25 82 32 64 128 256), losses := [] }

theorem u38229 : Upper (D 7) (R 7) [36,192,257,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38230 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 194 261 25 88 162 226 162 418), lower := (rows 37 194 261 25 88 32 64 128 256), losses := [] }

theorem u38230 : Upper (D 7) (R 7) [36,192,257,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38231 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 194 261 25 112 170 202 138 394), lower := (rows 37 194 261 25 112 32 64 128 256), losses := [] }

theorem u38231 : Upper (D 7) (R 7) [36,192,257,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38232 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 261 25 208 42 106 170 298), lower := (rows 37 194 261 25 208 32 64 128 256), losses := [] }

theorem u38232 : Upper (D 7) (R 7) [36,192,257,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38233 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 261 26 26 225 225 225 481), lower := (rows 37 194 261 26 26 32 64 128 256), losses := [] }

theorem u38233 : Upper (D 7) (R 7) [36,192,257,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38234 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 261 26 49 234 202 202 458), lower := (rows 37 194 261 26 49 32 64 128 256), losses := [] }

theorem u38234 : Upper (D 7) (R 7) [36,192,257,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38235 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 261 26 50 233 201 201 457), lower := (rows 37 194 261 26 50 32 64 128 256), losses := [] }

theorem u38235 : Upper (D 7) (R 7) [36,192,257,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38236 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38236 : Upper (D 7) (R 7) [36,192,257,18,40] 13 := by
  apply FastRouting.sound _ _ [36,192,257,18,40] 13 (by decide) (choices 1) [1,2,64] r38236 c38236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25422
  · exact u25423
  · exact u25424

def b38237 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 170, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 194 261 26 81 170 234 170 426), lower := (rows 37 194 261 26 81 32 64 128 256), losses := [] }

theorem u38237 : Upper (D 7) (R 7) [36,192,257,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38238 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 194 261 26 82 169 233 169 425), lower := (rows 37 194 261 26 82 32 64 128 256), losses := [] }

theorem u38238 : Upper (D 7) (R 7) [36,192,257,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38239 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 194 261 26 88 163 227 163 419), lower := (rows 37 194 261 26 88 32 64 128 256), losses := [] }

theorem u38239 : Upper (D 7) (R 7) [36,192,257,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38240 : Route 9 := (fun mask => (mask,id))

def c38240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38240 : Upper (D 7) (R 7) [36,192,257,18,96] 13 := by
  apply FastRouting.sound _ _ [36,192,257,18,96] 13 (by decide) (choices 1) [1,2,8,128] r38240 c38240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25425
  · exact u25426
  · exact u25427
  · exact u25428

def b38241 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 261 26 208 43 107 171 299), lower := (rows 37 194 261 26 208 32 64 128 256), losses := [] }

theorem u38241 : Upper (D 7) (R 7) [36,192,257,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38242 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 261 41 88 178 210 146 402), lower := (rows 37 194 261 41 88 32 64 128 256), losses := [] }

theorem u38242 : Upper (D 7) (R 7) [36,192,257,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38243 : Route 9 := (fun mask => (mask,id))

def c38243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38243 : Upper (D 7) (R 7) [36,192,257,34,65] 13 := by
  apply FastRouting.sound _ _ [36,192,257,34,65] 13 (by decide) (choices 1) [2,8,16,128] r38243 c38243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25429
  · exact u25430
  · exact u25431
  · exact u25432

def b38244 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 261 42 82 185 217 153 409), lower := (rows 37 194 261 42 82 32 64 128 256), losses := [] }

theorem u38244 : Upper (D 7) (R 7) [36,192,257,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38245 : Route 9 := (fun mask => (mask,id))

def c38245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38245 : Upper (D 7) (R 7) [36,192,257,34,72] 13 := by
  apply FastRouting.sound _ _ [36,192,257,34,72] 13 (by decide) (choices 1) [1,2,16,128] r38245 c38245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25433
  · exact u25434
  · exact u25435
  · exact u25436

def b38246 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 261 42 208 59 91 155 283), lower := (rows 37 194 261 42 208 32 64 128 256), losses := [] }

theorem u38246 : Upper (D 7) (R 7) [36,192,257,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38247 : Route 9 := (fun mask => (mask,id))

def c38247 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38247 : Upper (D 7) (R 7) [36,192,257,48,65] 13 := by
  apply FastRouting.sound _ _ [36,192,257,48,65] 13 (by decide) (choices 1) [2,8,128] r38247 c38247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25437
  · exact u25438
  · exact u25439

def b38248 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 261 56 82 171 203 139 395), lower := (rows 37 194 261 56 82 32 64 128 256), losses := [] }

theorem u38248 : Upper (D 7) (R 7) [36,192,257,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38249 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 37 194 261 56 88 163 195 131 387), lower := (rows 37 194 261 56 88 32 64 128 256), losses := [] }

theorem u38249 : Upper (D 7) (R 7) [36,192,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38250 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 261 56 208 43 75 139 267), lower := (rows 37 194 261 56 208 32 64 128 256), losses := [] }

theorem u38250 : Upper (D 7) (R 7) [36,192,257,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38251 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 261 73 146 58 122 186 314), lower := (rows 37 194 261 73 146 32 64 128 256), losses := [] }

theorem u38251 : Upper (D 7) (R 7) [36,192,257,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38252 : Route 9 := (fun mask => (mask,id))

def c38252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38252 : Upper (D 7) (R 7) [36,192,257,65,136] 13 := by
  apply FastRouting.sound _ _ [36,192,257,65,136] 13 (by decide) (choices 1) [2,16] r38252 c38252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25440
  · exact u25441

def r38253 : Route 9 := (fun mask => (mask,id))

def c38253 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38253 : Upper (D 7) (R 7) [36,192,257,65,160] 13 := by
  apply FastRouting.sound _ _ [36,192,257,65,160] 13 (by decide) (choices 1) [2,8,16] r38253 c38253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25442
  · exact u25443
  · exact u25444

def b38254 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 261 74 152 51 115 179 307), lower := (rows 37 194 261 74 152 32 64 128 256), losses := [] }

theorem u38254 : Upper (D 7) (R 7) [36,192,257,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38255 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 261 74 176 59 91 155 283), lower := (rows 37 194 261 74 176 32 64 128 256), losses := [] }

theorem u38255 : Upper (D 7) (R 7) [36,192,257,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38256 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 261 88 152 35 99 163 291), lower := (rows 37 194 261 88 152 32 64 128 256), losses := [] }

theorem u38256 : Upper (D 7) (R 7) [36,192,257,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38257 : Route 9 := (fun mask => (mask,id))

def c38257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38257 : Upper (D 7) (R 7) [36,192,257,80,160] 13 := by
  apply FastRouting.sound _ _ [36,192,257,80,160] 13 (by decide) (choices 1) [1,2,8] r38257 c38257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25445
  · exact u25446
  · exact u25447

def b38258 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 37 194 262 11 25 240 240 240 496), lower := (rows 37 194 262 11 25 32 64 128 256), losses := [] }

theorem u38258 : Upper (D 7) (R 7) [36,192,258,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38259 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 262 11 49 248 216 216 472), lower := (rows 37 194 262 11 49 32 64 128 256), losses := [] }

theorem u38259 : Upper (D 7) (R 7) [36,192,258,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38260 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38260 : Upper (D 7) (R 7) [36,192,258,3,40] 13 := by
  apply FastRouting.sound _ _ [36,192,258,3,40] 13 (by decide) (choices 1) [1,16,64] r38260 c38260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25448
  · exact u25449
  · exact u25450

def r38261 : Route 9 := (fun mask => (mask,id))

def c38261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38261 : Upper (D 7) (R 7) [36,192,258,3,65] 13 := by
  apply FastRouting.sound _ _ [36,192,258,3,65] 13 (by decide) (choices 1) [8,16,128] r38261 c38261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25451
  · exact u25452
  · exact u25453

def r38262 : Route 9 := (fun mask => (mask,id))

def c38262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38262 : Upper (D 7) (R 7) [36,192,258,3,72] 13 := by
  apply FastRouting.sound _ _ [36,192,258,3,72] 13 (by decide) (choices 1) [1,16,128] r38262 c38262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25454
  · exact u25455
  · exact u25456

def r38263 : Route 9 := (fun mask => (mask,id))

def c38263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38263 : Upper (D 7) (R 7) [36,192,258,3,96] 13 := by
  apply FastRouting.sound _ _ [36,192,258,3,96] 13 (by decide) (choices 1) [1,8,16,128] r38263 c38263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25457
  · exact u25458
  · exact u25459
  · exact u25460

def b38264 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 262 11 208 57 121 185 313), lower := (rows 37 194 262 11 208 32 64 128 256), losses := [] }

theorem u38264 : Upper (D 7) (R 7) [36,192,258,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38265 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 262 25 25 226 226 226 482), lower := (rows 37 194 262 25 25 32 64 128 256), losses := [] }

theorem u38265 : Upper (D 7) (R 7) [36,192,258,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38266 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38266 : Upper (D 7) (R 7) [36,192,258,17,10] 13 := by
  apply FastRouting.sound _ _ [36,192,258,17,10] 13 (by decide) (choices 1) [1,64] r38266 c38266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25461
  · exact u25462

def b38267 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 262 25 49 234 202 202 458), lower := (rows 37 194 262 25 49 32 64 128 256), losses := [] }

theorem u38267 : Upper (D 7) (R 7) [36,192,258,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38268 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38268 : Upper (D 7) (R 7) [36,192,258,17,34] 13 := by
  apply FastRouting.sound _ _ [36,192,258,17,34] 13 (by decide) (choices 1) [1,8,64] r38268 c38268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25463
  · exact u25464
  · exact u25465

def b38269 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 262 25 56 227 195 195 451), lower := (rows 37 194 262 25 56 32 64 128 256), losses := [] }

theorem u38269 : Upper (D 7) (R 7) [36,192,258,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38270 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 262 25 81 170 234 170 426), lower := (rows 37 194 262 25 81 32 64 128 256), losses := [] }

theorem u38270 : Upper (D 7) (R 7) [36,192,258,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38271 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 262 25 82 169 233 169 425), lower := (rows 37 194 262 25 82 32 64 128 256), losses := [] }

theorem u38271 : Upper (D 7) (R 7) [36,192,258,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38272 : Route 9 := (fun mask => (mask,id))

def c38272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38272 : Upper (D 7) (R 7) [36,192,258,17,72] 13 := by
  apply FastRouting.sound _ _ [36,192,258,17,72] 13 (by decide) (choices 1) [1,2,128] r38272 c38272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25466
  · exact u25467
  · exact u25468

def r38273 : Route 9 := (fun mask => (mask,id))

def c38273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38273 : Upper (D 7) (R 7) [36,192,258,17,96] 13 := by
  apply FastRouting.sound _ _ [36,192,258,17,96] 13 (by decide) (choices 1) [1,2,8,128] r38273 c38273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25469
  · exact u25470
  · exact u25471
  · exact u25472

def b38274 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 262 25 208 43 107 171 299), lower := (rows 37 194 262 25 208 32 64 128 256), losses := [] }

theorem u38274 : Upper (D 7) (R 7) [36,192,258,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38275 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 262 26 49 233 201 201 457), lower := (rows 37 194 262 26 49 32 64 128 256), losses := [] }

theorem u38275 : Upper (D 7) (R 7) [36,192,258,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38276 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38276 : Upper (D 7) (R 7) [36,192,258,18,40] 13 := by
  apply FastRouting.sound _ _ [36,192,258,18,40] 13 (by decide) (choices 1) [1,64] r38276 c38276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25473
  · exact u25474

def r38277 : Route 9 := (fun mask => (mask,id))

def c38277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38277 : Upper (D 7) (R 7) [36,192,258,18,65] 13 := by
  apply FastRouting.sound _ _ [36,192,258,18,65] 13 (by decide) (choices 1) [1,8,128] r38277 c38277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25475
  · exact u25476
  · exact u25477

def b38278 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 194 262 26 88 161 225 161 417), lower := (rows 37 194 262 26 88 32 64 128 256), losses := [] }

theorem u38278 : Upper (D 7) (R 7) [36,192,258,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38279 : Route 9 := (fun mask => (mask,id))

def c38279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38279 : Upper (D 7) (R 7) [36,192,258,18,96] 13 := by
  apply FastRouting.sound _ _ [36,192,258,18,96] 13 (by decide) (choices 1) [1,8,128] r38279 c38279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25478
  · exact u25479
  · exact u25480

#print axioms u38279
end Delivery.IrregularNine14.P07
