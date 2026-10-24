import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0088
import IrregularNine14P06C0089

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18300 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 70 137 276 34 100 228 356), lower := (rows 25 35 70 137 276 34 64 128 256), losses := [] }

theorem u18300 : Upper (D 6) (R 6) [24,33,66,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18301 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 1, region := 200, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 70 137 276 36 98 226 354), lower := (rows 25 35 70 137 276 36 64 128 256), losses := [] }

theorem u18301 : Upper (D 6) (R 6) [24,33,66,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18302 : Route 9 := (fun mask => (mask,id))

def c18302 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18302 : Upper (D 6) (R 6) [24,33,66,129,260,64] 13 := by
  apply FastRouting.sound _ _ [24,33,66,129,260,64] 13 (by decide) (choices 1) [2,4,32] r18302 c18302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5320
  · exact u5321
  · exact u5322

def b18303 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 70 137 336 34 100 164 292), lower := (rows 25 35 70 137 336 34 64 128 256), losses := [] }

theorem u18303 : Upper (D 6) (R 6) [24,33,66,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18304 : Route 9 := (fun mask => (mask,id))

def c18304 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18304 : Upper (D 6) (R 6) [24,33,66,129,320,4] 13 := by
  apply FastRouting.sound _ _ [24,33,66,129,320,4] 13 (by decide) (choices 1) [2,4,32] r18304 c18304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5323
  · exact u5324
  · exact u5325

def b18305 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 138 276 33 100 228 356), lower := (rows 25 35 70 138 276 33 64 128 256), losses := [] }

theorem u18305 : Upper (D 6) (R 6) [24,33,66,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18306 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 200, targets := 4 }], pairs := [(0,2),(3,2),(4,1)], upper := (rows 25 35 70 138 276 36 97 225 353), lower := (rows 25 35 70 138 276 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 52 67 131 259), good := (rows 505 481 500 456 308 52 64 128 256) },{ target := 2, region := (rows 17 2 0 14 16 32 66 130 258), good := (rows 25 491 458 458 281 40 64 128 256) }] }

theorem u18306 : Upper (D 6) (R 6) [24,33,66,130,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18307 : Route 9 := (fun mask => (mask,id))

def c18307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18307 : Upper (D 6) (R 6) [24,33,66,130,260,64] 13 := by
  apply FastRouting.sound _ _ [24,33,66,130,260,64] 13 (by decide) (choices 1) [1,4,32] r18307 c18307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5326
  · exact u5327
  · exact u5328

def b18308 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 138 304 33 68 196 324), lower := (rows 25 35 70 138 304 33 64 128 256), losses := [] }

theorem u18308 : Upper (D 6) (R 6) [24,33,66,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18309 : Route 9 := (fun mask => (mask,id))

def c18309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18309 : Upper (D 6) (R 6) [24,33,66,130,288,4] 13 := by
  apply FastRouting.sound _ _ [24,33,66,130,288,4] 13 (by decide) (choices 1) [1,4] r18309 c18309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5329
  · exact u5330

def r18310 : Route 9 := (fun mask => (mask,id))

def c18310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18310 : Upper (D 6) (R 6) [24,33,66,130,288,64] 13 := by
  apply FastRouting.sound _ _ [24,33,66,130,288,64] 13 (by decide) (choices 1) [1,4] r18310 c18310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5331
  · exact u5332

def b18311 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 138 336 33 100 164 292), lower := (rows 25 35 70 138 336 33 64 128 256), losses := [] }

theorem u18311 : Upper (D 6) (R 6) [24,33,66,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18312 : Route 9 := (fun mask => (mask,id))

def c18312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18312 : Upper (D 6) (R 6) [24,33,66,130,320,4] 13 := by
  apply FastRouting.sound _ _ [24,33,66,130,320,4] 13 (by decide) (choices 1) [1,4,32] r18312 c18312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5333
  · exact u5334
  · exact u5335

def b18313 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 140 276 33 98 226 354), lower := (rows 25 35 70 140 276 33 64 128 256), losses := [] }

theorem u18313 : Upper (D 6) (R 6) [24,33,66,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18314 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 34, targets := 4 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,1),(1,2),(1,6)], upper := (rows 25 35 70 140 276 34 97 225 353), lower := (rows 25 35 70 140 276 34 64 128 256), losses := [{ target := 1, region := (rows 29 0 4 12 20 32 66 130 258), good := (rows 25 481 477 157 285 480 64 128 256) }] }

theorem u18314 : Upper (D 6) (R 6) [24,33,66,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18315 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 98, targets := 4 }], pairs := [(0,6),(1,2),(3,6)], upper := (rows 25 35 70 140 276 96 99 163 291), lower := (rows 25 35 70 140 276 96 64 128 256), losses := [{ target := 6, region := (rows 29 2 4 12 20 32 0 130 258), good := (rows 25 419 415 157 285 32 0 128 256) }] }

theorem u18315 : Upper (D 6) (R 6) [24,33,66,132,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18316 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 140 304 33 70 198 326), lower := (rows 25 35 70 140 304 33 64 128 256), losses := [] }

theorem u18316 : Upper (D 6) (R 6) [24,33,66,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18317 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 70 140 304 34 69 197 325), lower := (rows 25 35 70 140 304 34 64 128 256), losses := [] }

theorem u18317 : Upper (D 6) (R 6) [24,33,66,132,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18318 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 1, region := 336, targets := 4 }], pairs := [(2,5),(3,5),(4,2)], upper := (rows 25 35 70 140 304 36 67 195 323), lower := (rows 25 35 70 140 304 36 64 128 256), losses := [] }

theorem u18318 : Upper (D 6) (R 6) [24,33,66,132,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18319 : Route 9 := (fun mask => (mask,id))

def c18319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18319 : Upper (D 6) (R 6) [24,33,66,132,288,64] 13 := by
  apply FastRouting.sound _ _ [24,33,66,132,288,64] 13 (by decide) (choices 1) [1,2,4] r18319 c18319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5336
  · exact u5337
  · exact u5338

def b18320 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 140 336 33 102 166 294), lower := (rows 25 35 70 140 336 33 64 128 256), losses := [] }

theorem u18320 : Upper (D 6) (R 6) [24,33,66,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18321 : Route 9 := (fun mask => (mask,id))

def c18321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18321 : Upper (D 6) (R 6) [24,33,66,132,320,2] 13 := by
  apply FastRouting.sound _ _ [24,33,66,132,320,2] 13 (by decide) (choices 1) [1,4,32] r18321 c18321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5339
  · exact u5340
  · exact u5341

def b18322 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 336, targets := 4 }], pairs := [(0,2),(1,6),(4,2)], upper := (rows 25 35 70 140 336 36 99 163 291), lower := (rows 25 35 70 140 336 36 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 22 32 66 130 258), good := (rows 25 499 466 153 336 48 64 128 256) },{ target := 6, region := (rows 1 3 4 12 16 44 0 131 259), good := (rows 443 419 430 172 272 44 0 128 256) }] }

theorem u18322 : Upper (D 6) (R 6) [24,33,66,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18323 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 168 336 33 70 134 262), lower := (rows 25 35 70 168 336 33 64 128 256), losses := [] }

theorem u18323 : Upper (D 6) (R 6) [24,33,66,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18324 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 70 168 336 34 69 133 261), lower := (rows 25 35 70 168 336 34 64 128 256), losses := [] }

theorem u18324 : Upper (D 6) (R 6) [24,33,66,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18325 : Route 9 := (fun mask => (mask,id))

def c18325 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18325 : Upper (D 6) (R 6) [24,33,66,160,320,4] 13 := by
  apply FastRouting.sound _ _ [24,33,66,160,320,4] 13 (by decide) (choices 1) [1,2,4] r18325 c18325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5342
  · exact u5343
  · exact u5344

def b18326 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 324, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 13 146 34 324 452 324), lower := (rows 25 35 100 13 146 34 64 128 256), losses := [] }

theorem u18326 : Upper (D 6) (R 6) [24,33,96,5,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18327 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 464, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 100 13 146 36 322 450 322), lower := (rows 25 35 100 13 146 36 64 128 256), losses := [] }

theorem u18327 : Upper (D 6) (R 6) [24,33,96,5,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18328 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 13 146 96 326 390 262), lower := (rows 25 35 100 13 146 96 64 128 256), losses := [] }

theorem u18328 : Upper (D 6) (R 6) [24,33,96,5,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18329 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 25 35 100 13 146 288 70 198 326), lower := (rows 25 35 100 13 146 288 64 128 256), losses := [] }

theorem u18329 : Upper (D 6) (R 6) [24,33,96,5,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18329 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18330 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 13 400 34 70 198 326), lower := (rows 25 35 100 13 400 34 64 128 256), losses := [] }

theorem u18330 : Upper (D 6) (R 6) [24,33,96,5,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18331 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 464, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 100 13 400 36 66 194 322), lower := (rows 25 35 100 13 400 36 64 128 256), losses := [] }

theorem u18331 : Upper (D 6) (R 6) [24,33,96,5,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18332 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 13 400 96 70 134 262), lower := (rows 25 35 100 13 400 96 64 128 256), losses := [] }

theorem u18332 : Upper (D 6) (R 6) [24,33,96,5,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18333 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 14 208 33 326 390 262), lower := (rows 25 35 100 14 208 33 64 128 256), losses := [] }

theorem u18333 : Upper (D 6) (R 6) [24,33,96,6,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18334 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 465, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 35 100 14 208 34 325 389 261), lower := (rows 25 35 100 14 208 34 64 128 256), losses := [] }

theorem u18334 : Upper (D 6) (R 6) [24,33,96,6,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18335 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 465, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 35 100 14 208 36 323 387 259), lower := (rows 25 35 100 14 208 36 64 128 256), losses := [] }

theorem u18335 : Upper (D 6) (R 6) [24,33,96,6,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18336 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 209, targets := 32 }], pairs := [(0,5),(4,5)], upper := (rows 25 35 100 14 208 288 71 135 263), lower := (rows 25 35 100 14 208 288 64 128 256), losses := [] }

theorem u18336 : Upper (D 6) (R 6) [24,33,96,6,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18336 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18337 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 14 400 33 70 198 326), lower := (rows 25 35 100 14 400 33 64 128 256), losses := [] }

theorem u18337 : Upper (D 6) (R 6) [24,33,96,6,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18338 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 465, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 35 100 14 400 34 69 197 325), lower := (rows 25 35 100 14 400 34 64 128 256), losses := [] }

theorem u18338 : Upper (D 6) (R 6) [24,33,96,6,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18339 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 465, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 35 100 14 400 36 67 195 323), lower := (rows 25 35 100 14 400 36 64 128 256), losses := [] }

theorem u18339 : Upper (D 6) (R 6) [24,33,96,6,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18340 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 14 400 96 71 135 263), lower := (rows 25 35 100 14 400 96 64 128 256), losses := [] }

theorem u18340 : Upper (D 6) (R 6) [24,33,96,6,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18341 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 324, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 73 146 34 324 388 260), lower := (rows 25 35 100 73 146 34 64 128 256), losses := [] }

theorem u18341 : Upper (D 6) (R 6) [24,33,96,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18342 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 35 100 73 146 36 326 390 262), lower := (rows 25 35 100 73 146 36 64 128 256), losses := [] }

theorem u18342 : Upper (D 6) (R 6) [24,33,96,65,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18343 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 25 35 100 73 146 288 70 134 262), lower := (rows 25 35 100 73 146 288 64 128 256), losses := [] }

theorem u18343 : Upper (D 6) (R 6) [24,33,96,65,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18343 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18344 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 324, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 73 148 34 326 390 262), lower := (rows 25 35 100 73 148 34 64 128 256), losses := [] }

theorem u18344 : Upper (D 6) (R 6) [24,33,96,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18345 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 328, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 100 73 148 36 322 386 258), lower := (rows 25 35 100 73 148 36 64 128 256), losses := [] }

theorem u18345 : Upper (D 6) (R 6) [24,33,96,65,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18346 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 25 35 100 73 148 288 70 134 262), lower := (rows 25 35 100 73 148 288 64 128 256), losses := [] }

theorem u18346 : Upper (D 6) (R 6) [24,33,96,65,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18346 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18347 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 73 400 34 70 134 262), lower := (rows 25 35 100 73 400 34 64 128 256), losses := [] }

theorem u18347 : Upper (D 6) (R 6) [24,33,96,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18348 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 35 100 73 400 36 70 134 262), lower := (rows 25 35 100 73 400 36 64 128 256), losses := [] }

theorem u18348 : Upper (D 6) (R 6) [24,33,96,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18349 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 324, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 74 145 34 324 388 260), lower := (rows 25 35 100 74 145 34 64 128 256), losses := [] }

theorem u18349 : Upper (D 6) (R 6) [24,33,96,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18350 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 332, targets := 1 },{ cop := 3, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 25 35 100 74 145 36 326 390 262), lower := (rows 25 35 100 74 145 36 64 128 256), losses := [] }

theorem u18350 : Upper (D 6) (R 6) [24,33,96,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18351 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 25 35 100 74 145 288 70 134 262), lower := (rows 25 35 100 74 145 288 64 128 256), losses := [] }

theorem u18351 : Upper (D 6) (R 6) [24,33,96,66,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18351 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18352 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 74 146 33 324 388 260), lower := (rows 25 35 100 74 146 33 64 128 256), losses := [] }

theorem u18352 : Upper (D 6) (R 6) [24,33,96,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18353 : Route 9 := (fun mask => (mask,id))

def c18353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u18353 : Upper (D 6) (R 6) [24,33,96,66,130,4] 13 := by
  apply FastRouting.sound _ _ [24,33,96,66,130,4] 13 (by decide) (choices 1) [1,4,256] r18353 c18353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5345
  · exact u5346
  · exact u5347

def r18354 : Route 9 := (fun mask => (mask,id))

def c18354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18354 : Upper (D 6) (R 6) [24,33,96,66,130,256] 13 := by
  apply FastRouting.sound _ _ [24,33,96,66,130,256] 13 (by decide) (choices 1) [1,4] r18354 c18354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5348
  · exact u5349

def b18355 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 74 148 33 326 390 262), lower := (rows 25 35 100 74 148 33 64 128 256), losses := [] }

theorem u18355 : Upper (D 6) (R 6) [24,33,96,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18356 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 324, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 100 74 148 34 325 389 261), lower := (rows 25 35 100 74 148 34 64 128 256), losses := [] }

theorem u18356 : Upper (D 6) (R 6) [24,33,96,66,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18357 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 328, targets := 36 },{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0),(3,2),(3,5)], upper := (rows 25 35 100 74 148 36 323 387 259), lower := (rows 25 35 100 74 148 36 64 128 256), losses := [] }

theorem u18357 : Upper (D 6) (R 6) [24,33,96,66,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18358 : Route 9 := (fun mask => (mask,id))

def c18358 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18358 : Upper (D 6) (R 6) [24,33,96,66,132,256] 13 := by
  apply FastRouting.sound _ _ [24,33,96,66,132,256] 13 (by decide) (choices 1) [1,2,4] r18358 c18358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5350
  · exact u5351
  · exact u5352

def b18359 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 74 400 33 70 134 262), lower := (rows 25 35 100 74 400 33 64 128 256), losses := [] }

theorem u18359 : Upper (D 6) (R 6) [24,33,96,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18359
end Delivery.IrregularNine14.P06
