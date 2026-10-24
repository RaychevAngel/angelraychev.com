import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0145
import IrregularNine14P07C0146

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25320 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 37 194 76 56 274 160 67 131 259), lower := (rows 37 194 76 56 274 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 162 64 128 256), good := (rows 36 226 76 56 314 160 64 160 256) },{ target := 1, region := (rows 1 0 4 24 16 162 64 128 256), good := (rows 37 224 76 56 312 160 64 160 256) }] }

theorem u25320 : Upper (D 7) (R 7) [36,192,72,48,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25321 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 56 400 33 67 131 259), lower := (rows 37 194 76 56 400 33 64 128 256), losses := [] }

theorem u25321 : Upper (D 7) (R 7) [36,192,72,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25322 : Route 9 := (fun mask => (mask,id))

def c25322 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25322 : Upper (D 7) (R 7) [36,192,72,48,384,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,48,384,2] 13 (by decide) (choices 1) [1,2] r25322 c25322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8706
  · exact u8707

def r25323 : Route 9 := (fun mask => (mask,id))

def c25323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u25323 : Upper (D 7) (R 7) [36,192,72,129,3,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,3,2] 13 (by decide) (choices 1) [16,32,256] r25323 c25323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8708
  · exact u8709
  · exact u8710

def b25324 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,0),(2,0),(3,6)], upper := (rows 37 194 76 137 19 48 354 418 290), lower := (rows 37 194 76 137 19 48 64 128 256), losses := [{ target := 0, region := (rows 0 59 12 8 16 48 113 177 305), good := (rows 486 194 78 462 498 498 64 128 256) }] }

theorem u25324 : Upper (D 7) (R 7) [36,192,72,129,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25324 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25325 : Route 9 := (fun mask => (mask,id))

def c25325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25325 : Upper (D 7) (R 7) [36,192,72,129,3,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,3,256] 13 (by decide) (choices 1) [2,16,32] r25325 c25325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8711
  · exact u8712
  · exact u8713

def b25326 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 194 76 137 50 33 338 402 274), lower := (rows 37 194 76 137 50 33 64 128 256), losses := [] }

theorem u25326 : Upper (D 7) (R 7) [36,192,72,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25327 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 194 76 137 50 34 337 401 273), lower := (rows 37 194 76 137 50 34 64 128 256), losses := [] }

theorem u25327 : Upper (D 7) (R 7) [36,192,72,129,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25328 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 76 137 50 48 323 387 259), lower := (rows 37 194 76 137 50 48 64 128 256), losses := [] }

theorem u25328 : Upper (D 7) (R 7) [36,192,72,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25328 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25329 : Route 9 := (fun mask => (mask,id))

def c25329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25329 : Upper (D 7) (R 7) [36,192,72,129,34,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,34,256] 13 (by decide) (choices 1) [1,2,16] r25329 c25329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8714
  · exact u8715
  · exact u8716

def r25330 : Route 9 := (fun mask => (mask,id))

def c25330 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25330 : Upper (D 7) (R 7) [36,192,72,129,257,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,257,2] 13 (by decide) (choices 1) [2,16,32] r25330 c25330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8717
  · exact u8718
  · exact u8719

def r25331 : Route 9 := (fun mask => (mask,id))

def c25331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25331 : Upper (D 7) (R 7) [36,192,72,129,257,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,257,16] 13 (by decide) (choices 1) [2,32] r25331 c25331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8720
  · exact u8721

def b25332 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 194 76 137 274 33 114 178 306), lower := (rows 37 194 76 137 274 33 64 128 256), losses := [] }

theorem u25332 : Upper (D 7) (R 7) [36,192,72,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25333 : Route 9 := (fun mask => (mask,id))

def c25333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25333 : Upper (D 7) (R 7) [36,192,72,129,258,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,258,2] 13 (by decide) (choices 1) [1,16,32] r25333 c25333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8722
  · exact u8723
  · exact u8724

def r25334 : Route 9 := (fun mask => (mask,id))

def c25334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25334 : Upper (D 7) (R 7) [36,192,72,129,258,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,258,16] 13 (by decide) (choices 1) [1,2,32] r25334 c25334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8725
  · exact u8726
  · exact u8727

def b25335 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 194 76 137 304 33 82 146 274), lower := (rows 37 194 76 137 304 33 64 128 256), losses := [] }

theorem u25335 : Upper (D 7) (R 7) [36,192,72,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25336 : Route 9 := (fun mask => (mask,id))

def c25336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25336 : Upper (D 7) (R 7) [36,192,72,129,288,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,288,2] 13 (by decide) (choices 1) [1,2,16] r25336 c25336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8728
  · exact u8729
  · exact u8730

def b25337 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 194 76 137 304 48 67 131 259), lower := (rows 37 194 76 137 304 48 64 128 256), losses := [] }

theorem u25337 : Upper (D 7) (R 7) [36,192,72,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25337 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25338 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 152 19 33 354 418 290), lower := (rows 37 194 76 152 19 33 64 128 256), losses := [] }

theorem u25338 : Upper (D 7) (R 7) [36,192,72,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25339 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 424, targets := 64 }], pairs := [(0,7),(2,1),(3,1),(3,6)], upper := (rows 37 194 76 152 19 34 353 417 289), lower := (rows 37 194 76 152 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 65 129 257), good := (rows 485 192 76 156 477 32 64 128 256) },{ target := 7, region := (rows 9 2 12 8 16 50 89 0 281), good := (rows 357 98 333 381 371 34 64 0 256) }] }

theorem u25339 : Upper (D 7) (R 7) [36,192,72,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25340 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 194 76 152 19 288 99 163 291), lower := (rows 37 194 76 152 19 288 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 24 16 312 0 144 272), good := (rows 37 130 45 440 443 288 0 128 288) },{ target := 7, region := (rows 13 2 12 8 16 312 80 0 272), good := (rows 37 66 109 381 371 288 64 0 288) }] }

theorem u25340 : Upper (D 7) (R 7) [36,192,72,144,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25340 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25341 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 152 50 33 323 387 259), lower := (rows 37 194 76 152 50 33 64 128 256), losses := [] }

theorem u25341 : Upper (D 7) (R 7) [36,192,72,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25342 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 60, targets := 1 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(2,0),(3,0),(4,0)], upper := (rows 37 194 76 152 50 34 321 385 257), lower := (rows 37 194 76 152 50 34 64 128 256), losses := [] }

theorem u25342 : Upper (D 7) (R 7) [36,192,72,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25343 : Route 9 := (fun mask => (mask,id))

def c25343 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25343 : Upper (D 7) (R 7) [36,192,72,144,34,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,34,256] 13 (by decide) (choices 1) [1,2] r25343 c25343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8731
  · exact u8732

def b25344 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 152 273 33 98 162 290), lower := (rows 37 194 76 152 273 33 64 128 256), losses := [] }

theorem u25344 : Upper (D 7) (R 7) [36,192,72,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25345 : Route 9 := (fun mask => (mask,id))

def c25345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25345 : Upper (D 7) (R 7) [36,192,72,144,257,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,257,2] 13 (by decide) (choices 1) [1,2,32] r25345 c25345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8733
  · exact u8734
  · exact u8735

def r25346 : Route 9 := (fun mask => (mask,id))

def c25346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25346 : Upper (D 7) (R 7) [36,192,72,144,258,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,258,1] 13 (by decide) (choices 1) [1,2,32] r25346 c25346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8736
  · exact u8737
  · exact u8738

def r25347 : Route 9 := (fun mask => (mask,id))

def c25347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25347 : Upper (D 7) (R 7) [36,192,72,144,258,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,258,2] 13 (by decide) (choices 1) [1,32] r25347 c25347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8739
  · exact u8740

def b25348 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 194 76 152 304 33 67 131 259), lower := (rows 37 194 76 152 304 33 64 128 256), losses := [] }

theorem u25348 : Upper (D 7) (R 7) [36,192,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25349 : Route 9 := (fun mask => (mask,id))

def c25349 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25349 : Upper (D 7) (R 7) [36,192,72,144,288,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,288,2] 13 (by decide) (choices 1) [1,2] r25349 c25349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8741
  · exact u8742

def b25350 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 37 194 76 168 19 33 338 402 274), lower := (rows 37 194 76 168 19 33 64 128 256), losses := [] }

theorem u25350 : Upper (D 7) (R 7) [36,192,72,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25351 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 44, targets := 1 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 37 194 76 168 19 34 337 401 273), lower := (rows 37 194 76 168 19 34 64 128 256), losses := [] }

theorem u25351 : Upper (D 7) (R 7) [36,192,72,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25352 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 37 194 76 168 19 48 323 387 259), lower := (rows 37 194 76 168 19 48 64 128 256), losses := [] }

theorem u25352 : Upper (D 7) (R 7) [36,192,72,160,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25352 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25353 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 37 194 76 168 19 288 83 147 275), lower := (rows 37 194 76 168 19 288 64 128 256), losses := [] }

theorem u25353 : Upper (D 7) (R 7) [36,192,72,160,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25353 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25354 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 37 194 76 168 273 33 82 146 274), lower := (rows 37 194 76 168 273 33 64 128 256), losses := [] }

theorem u25354 : Upper (D 7) (R 7) [36,192,72,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25355 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 44, targets := 1 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 37 194 76 168 273 34 83 147 275), lower := (rows 37 194 76 168 273 34 64 128 256), losses := [] }

theorem u25355 : Upper (D 7) (R 7) [36,192,72,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25356 : Route 9 := (fun mask => (mask,id))

def c25356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25356 : Upper (D 7) (R 7) [36,192,72,160,257,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,160,257,16] 13 (by decide) (choices 1) [1,2] r25356 c25356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8743
  · exact u8744

def b25357 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 37 194 76 168 274 33 83 147 275), lower := (rows 37 194 76 168 274 33 64 128 256), losses := [] }

theorem u25357 : Upper (D 7) (R 7) [36,192,72,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25358 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 44, targets := 1 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 37 194 76 168 274 34 81 145 273), lower := (rows 37 194 76 168 274 34 64 128 256), losses := [] }

theorem u25358 : Upper (D 7) (R 7) [36,192,72,160,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25359 : Route 9 := (fun mask => (mask,id))

def c25359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25359 : Upper (D 7) (R 7) [36,192,72,160,258,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,160,258,16] 13 (by decide) (choices 1) [1,2] r25359 c25359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8745
  · exact u8746

def r25360 : Route 9 := (fun mask => (mask,id))

def c25360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u25360 : Upper (D 7) (R 7) [36,192,72,257,3,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,257,3,2] 13 (by decide) (choices 1) [16,32,128] r25360 c25360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8747
  · exact u8748
  · exact u8749

def b25361 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,0),(2,0),(3,6)], upper := (rows 37 194 76 265 19 48 226 162 418), lower := (rows 37 194 76 265 19 48 64 128 256), losses := [{ target := 0, region := (rows 0 59 12 8 16 48 113 177 305), good := (rows 486 194 78 462 498 498 64 128 256) }] }

theorem u25361 : Upper (D 7) (R 7) [36,192,72,257,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25361 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25362 : Route 9 := (fun mask => (mask,id))

def c25362 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25362 : Upper (D 7) (R 7) [36,192,72,257,3,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,257,3,128] 13 (by decide) (choices 1) [2,16,32] r25362 c25362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8750
  · exact u8751
  · exact u8752

def b25363 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 265 50 33 210 146 402), lower := (rows 37 194 76 265 50 33 64 128 256), losses := [] }

theorem u25363 : Upper (D 7) (R 7) [36,192,72,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25364 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 194 76 265 50 34 209 145 401), lower := (rows 37 194 76 265 50 34 64 128 256), losses := [] }

theorem u25364 : Upper (D 7) (R 7) [36,192,72,257,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25365 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 76 265 50 48 195 131 387), lower := (rows 37 194 76 265 50 48 64 128 256), losses := [] }

theorem u25365 : Upper (D 7) (R 7) [36,192,72,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25365 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25366 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 76 265 50 160 83 147 275), lower := (rows 37 194 76 265 50 160 64 128 256), losses := [] }

theorem u25366 : Upper (D 7) (R 7) [36,192,72,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25367 : Route 9 := (fun mask => (mask,id))

def c25367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25367 : Upper (D 7) (R 7) [36,192,72,257,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,257,129,2] 13 (by decide) (choices 1) [2,16,32] r25367 c25367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8753
  · exact u8754
  · exact u8755

def r25368 : Route 9 := (fun mask => (mask,id))

def c25368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25368 : Upper (D 7) (R 7) [36,192,72,257,129,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,257,129,16] 13 (by decide) (choices 1) [2,32] r25368 c25368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8756
  · exact u8757

def b25369 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 76 265 176 33 82 146 274), lower := (rows 37 194 76 265 176 33 64 128 256), losses := [] }

theorem u25369 : Upper (D 7) (R 7) [36,192,72,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25370 : Route 9 := (fun mask => (mask,id))

def c25370 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25370 : Upper (D 7) (R 7) [36,192,72,257,160,2] 13 := by
  apply FastRouting.sound _ _ [36,192,72,257,160,2] 13 (by decide) (choices 1) [1,2,16] r25370 c25370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8758
  · exact u8759
  · exact u8760

def b25371 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 76 265 176 48 67 131 259), lower := (rows 37 194 76 265 176 48 64 128 256), losses := [] }

theorem u25371 : Upper (D 7) (R 7) [36,192,72,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25371 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25372 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 194 76 266 19 33 240 176 432), lower := (rows 37 194 76 266 19 33 64 128 256), losses := [] }

theorem u25372 : Upper (D 7) (R 7) [36,192,72,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25373 : Route 9 := (fun mask => (mask,id))

def c25373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25373 : Upper (D 7) (R 7) [36,192,72,258,3,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,3,16] 13 (by decide) (choices 1) [1,32,128] r25373 c25373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8761
  · exact u8762
  · exact u8763

def r25374 : Route 9 := (fun mask => (mask,id))

def c25374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25374 : Upper (D 7) (R 7) [36,192,72,258,3,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,3,128] 13 (by decide) (choices 1) [1,16,32] r25374 c25374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8764
  · exact u8765
  · exact u8766

def r25375 : Route 9 := (fun mask => (mask,id))

def c25375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25375 : Upper (D 7) (R 7) [36,192,72,258,34,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,34,1] 13 (by decide) (choices 1) [1,16,128] r25375 c25375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8767
  · exact u8768
  · exact u8769

def b25376 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 76 266 50 48 193 129 385), lower := (rows 37 194 76 266 50 48 64 128 256), losses := [] }

theorem u25376 : Upper (D 7) (R 7) [36,192,72,258,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25376 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25377 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 76 266 50 160 81 145 273), lower := (rows 37 194 76 266 50 160 64 128 256), losses := [] }

theorem u25377 : Upper (D 7) (R 7) [36,192,72,258,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25378 : Route 9 := (fun mask => (mask,id))

def c25378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25378 : Upper (D 7) (R 7) [36,192,72,258,129,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,129,1] 13 (by decide) (choices 1) [2,16,32] r25378 c25378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8770
  · exact u8771
  · exact u8772

def b25379 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 144, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 37 194 76 266 145 34 113 177 305), lower := (rows 37 194 76 266 145 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 21 42 0 133 261), good := (rows 437 162 445 298 401 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 98 109 298 17 34 64 0 256) }] }

theorem u25379 : Upper (D 7) (R 7) [36,192,72,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25379
end Delivery.IrregularNine14.P07
