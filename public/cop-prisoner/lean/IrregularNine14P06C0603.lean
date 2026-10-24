import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0341
import IrregularNine14P06C0342
import IrregularNine14P06C0343

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36180 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,0),(4,5)], upper := (rows 35 70 140 73 22 305 369 433 305), lower := (rows 35 70 140 73 22 32 64 128 256), losses := [] }

theorem u36180 : Upper (D 6) (R 6) [34,68,136,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36181 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 140 73 49 310 342 406 278), lower := (rows 35 70 140 73 49 32 64 128 256), losses := [] }

theorem u36181 : Upper (D 6) (R 6) [34,68,136,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36182 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 70 140 73 50 309 341 405 277), lower := (rows 35 70 140 73 50 32 64 128 256), losses := [] }

theorem u36182 : Upper (D 6) (R 6) [34,68,136,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36183 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 140 73 52 307 339 403 275), lower := (rows 35 70 140 73 52 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 26 35 0 131 259), good := (rows 435 439 156 445 52 32 0 128 256) }] }

theorem u36183 : Upper (D 6) (R 6) [34,68,136,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36184 : Route 9 := (fun mask => (mask,id))

def c36184 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36184 : Upper (D 6) (R 6) [34,68,136,65,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,257] 13 (by decide) (choices 1) [2,4,16] r36184 c36184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20512
  · exact u20513
  · exact u20514

def b36185 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 140 73 274 53 117 181 309), lower := (rows 35 70 140 73 274 32 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 42 0 138 266), good := (rows 435 439 428 445 435 32 0 128 256) }] }

theorem u36185 : Upper (D 6) (R 6) [34,68,136,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36186 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 140 73 276 51 115 179 307), lower := (rows 35 70 140 73 276 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 26 35 0 131 259), good := (rows 435 439 156 445 276 32 0 128 256) }] }

theorem u36186 : Upper (D 6) (R 6) [34,68,136,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36187 : Route 9 := (fun mask => (mask,id))

def c36187 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36187 : Upper (D 6) (R 6) [34,68,136,65,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65,288] 13 (by decide) (choices 1) [1,2,4,16] r36187 c36187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20515
  · exact u20516
  · exact u20517
  · exact u20518

def b36188 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 140 88 19 293 357 421 293), lower := (rows 35 70 140 88 19 32 64 128 256), losses := [] }

theorem u36188 : Upper (D 6) (R 6) [34,68,136,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36189 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 88 21 291 355 419 291), lower := (rows 35 70 140 88 21 32 64 128 256), losses := [] }

theorem u36189 : Upper (D 6) (R 6) [34,68,136,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36190 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 140 88 22 289 353 417 289), lower := (rows 35 70 140 88 22 32 64 128 256), losses := [] }

theorem u36190 : Upper (D 6) (R 6) [34,68,136,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36191 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 140 88 49 295 327 391 263), lower := (rows 35 70 140 88 49 32 64 128 256), losses := [] }

theorem u36191 : Upper (D 6) (R 6) [34,68,136,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36192 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 70 140 88 50 293 325 389 261), lower := (rows 35 70 140 88 50 32 64 128 256), losses := [] }

theorem u36192 : Upper (D 6) (R 6) [34,68,136,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36193 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 88 52 291 323 387 259), lower := (rows 35 70 140 88 52 32 64 128 256), losses := [] }

theorem u36193 : Upper (D 6) (R 6) [34,68,136,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36194 : Route 9 := (fun mask => (mask,id))

def c36194 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36194 : Upper (D 6) (R 6) [34,68,136,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,257] 13 (by decide) (choices 1) [1,2,4] r36194 c36194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20519
  · exact u20520
  · exact u20521

def b36195 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 140 88 274 37 101 165 293), lower := (rows 35 70 140 88 274 32 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 42 0 138 266), good := (rows 435 439 428 445 435 32 0 128 256) }] }

theorem u36195 : Upper (D 6) (R 6) [34,68,136,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36196 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 88 276 35 99 163 291), lower := (rows 35 70 140 88 276 32 64 128 256), losses := [] }

theorem u36196 : Upper (D 6) (R 6) [34,68,136,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36197 : Route 9 := (fun mask => (mask,id))

def c36197 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36197 : Upper (D 6) (R 6) [34,68,136,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,288] 13 (by decide) (choices 1) [1,2,4] r36197 c36197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20522
  · exact u20523
  · exact u20524

def b36198 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 140 104 19 309 341 405 277), lower := (rows 35 70 140 104 19 32 64 128 256), losses := [] }

theorem u36198 : Upper (D 6) (R 6) [34,68,136,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36199 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 322, targets := 32 }], pairs := [(0,6),(1,5),(4,6)], upper := (rows 35 70 140 104 21 307 339 403 275), lower := (rows 35 70 140 104 21 32 64 128 256), losses := [] }

theorem u36199 : Upper (D 6) (R 6) [34,68,136,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36200 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,0),(4,5)], upper := (rows 35 70 140 104 22 305 337 401 273), lower := (rows 35 70 140 104 22 32 64 128 256), losses := [] }

theorem u36200 : Upper (D 6) (R 6) [34,68,136,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36201 : Route 9 := (fun mask => (mask,id))

def c36201 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36201 : Upper (D 6) (R 6) [34,68,136,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,257] 13 (by decide) (choices 1) [1,2,4,16] r36201 c36201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20525
  · exact u20526
  · exact u20527
  · exact u20528

def r36202 : Route 9 := (fun mask => (mask,id))

def c36202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36202 : Upper (D 6) (R 6) [34,68,136,96,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,258] 13 (by decide) (choices 1) [1,4,16] r36202 c36202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20529
  · exact u20530
  · exact u20531

def r36203 : Route 9 := (fun mask => (mask,id))

def c36203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36203 : Upper (D 6) (R 6) [34,68,136,96,260] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96,260] 13 (by decide) (choices 1) [1,2,16] r36203 c36203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20532
  · exact u20533
  · exact u20534

def b36204 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 140 265 19 116 116 244 372), lower := (rows 35 70 140 265 19 32 64 128 256), losses := [] }

theorem u36204 : Upper (D 6) (R 6) [34,68,136,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36205 : Route 9 := (fun mask => (mask,id))

def c36205 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36205 : Upper (D 6) (R 6) [34,68,136,257,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,5] 13 (by decide) (choices 1) [2,16,64] r36205 c36205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20535
  · exact u20536
  · exact u20537

def b36206 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 70 140 265 22 113 113 241 369), lower := (rows 35 70 140 265 22 32 64 128 256), losses := [] }

theorem u36206 : Upper (D 6) (R 6) [34,68,136,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36207 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 140 265 49 118 86 214 342), lower := (rows 35 70 140 265 49 32 64 128 256), losses := [] }

theorem u36207 : Upper (D 6) (R 6) [34,68,136,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36208 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 70 140 265 50 117 85 213 341), lower := (rows 35 70 140 265 50 32 64 128 256), losses := [] }

theorem u36208 : Upper (D 6) (R 6) [34,68,136,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36209 : Route 9 := (fun mask => (mask,id))

def c36209 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36209 : Upper (D 6) (R 6) [34,68,136,257,36] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,36] 13 (by decide) (choices 1) [1,2,16,64] r36209 c36209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20538
  · exact u20539
  · exact u20540
  · exact u20541

def r36210 : Route 9 := (fun mask => (mask,id))

def c36210 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36210 : Upper (D 6) (R 6) [34,68,136,257,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,65] 13 (by decide) (choices 1) [2,4,16] r36210 c36210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20542
  · exact u20543
  · exact u20544

def b36211 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 140 265 82 53 117 181 309), lower := (rows 35 70 140 265 82 32 64 128 256), losses := [] }

theorem u36211 : Upper (D 6) (R 6) [34,68,136,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36212 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 140 265 84 51 115 179 307), lower := (rows 35 70 140 265 84 32 64 128 256), losses := [] }

theorem u36212 : Upper (D 6) (R 6) [34,68,136,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36213 : Route 9 := (fun mask => (mask,id))

def c36213 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36213 : Upper (D 6) (R 6) [34,68,136,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,96] 13 (by decide) (choices 1) [1,2,4,16] r36213 c36213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20545
  · exact u20546
  · exact u20547
  · exact u20548

def r36214 : Route 9 := (fun mask => (mask,id))

def c36214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36214 : Upper (D 6) (R 6) [34,68,136,258,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,5] 13 (by decide) (choices 1) [1,16,64] r36214 c36214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20549
  · exact u20550
  · exact u20551

def b36215 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 140 266 49 117 85 213 341), lower := (rows 35 70 140 266 49 32 64 128 256), losses := [] }

theorem u36215 : Upper (D 6) (R 6) [34,68,136,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36216 : Route 9 := (fun mask => (mask,id))

def c36216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36216 : Upper (D 6) (R 6) [34,68,136,258,36] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,36] 13 (by decide) (choices 1) [1,16,64] r36216 c36216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20552
  · exact u20553
  · exact u20554

def r36217 : Route 9 := (fun mask => (mask,id))

def c36217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36217 : Upper (D 6) (R 6) [34,68,136,258,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,65] 13 (by decide) (choices 1) [1,4,16] r36217 c36217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20555
  · exact u20556
  · exact u20557

def b36218 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 140 266 84 49 113 177 305), lower := (rows 35 70 140 266 84 32 64 128 256), losses := [] }

theorem u36218 : Upper (D 6) (R 6) [34,68,136,258,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36219 : Route 9 := (fun mask => (mask,id))

def c36219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36219 : Upper (D 6) (R 6) [34,68,136,258,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,96] 13 (by decide) (choices 1) [1,4,16] r36219 c36219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20558
  · exact u20559
  · exact u20560

def b36220 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 1, region := 49, targets := 4 }], pairs := [(0,2),(4,5),(4,6)], upper := (rows 35 70 140 268 19 113 113 241 369), lower := (rows 35 70 140 268 19 32 64 128 256), losses := [] }

theorem u36220 : Upper (D 6) (R 6) [34,68,136,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36221 : PairBound 9 := { available := 83, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 140 268 49 115 83 211 339), lower := (rows 35 70 140 268 49 32 64 128 256), losses := [] }

theorem u36221 : Upper (D 6) (R 6) [34,68,136,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36222 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 70 140 268 50 113 81 209 337), lower := (rows 35 70 140 268 50 32 64 128 256), losses := [] }

theorem u36222 : Upper (D 6) (R 6) [34,68,136,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36223 : Route 9 := (fun mask => (mask,id))

def c36223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36223 : Upper (D 6) (R 6) [34,68,136,260,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,260,65] 13 (by decide) (choices 1) [1,2,16] r36223 c36223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20561
  · exact u20562
  · exact u20563

def b36224 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 140 268 82 49 113 177 305), lower := (rows 35 70 140 268 82 32 64 128 256), losses := [] }

theorem u36224 : Upper (D 6) (R 6) [34,68,136,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36225 : Route 9 := (fun mask => (mask,id))

def c36225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36225 : Upper (D 6) (R 6) [34,68,136,260,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,260,96] 13 (by decide) (choices 1) [1,2,16] r36225 c36225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20564
  · exact u20565
  · exact u20566

def b36226 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 140 280 19 101 101 229 357), lower := (rows 35 70 140 280 19 32 64 128 256), losses := [] }

theorem u36226 : Upper (D 6) (R 6) [34,68,136,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36227 : Route 9 := (fun mask => (mask,id))

def c36227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36227 : Upper (D 6) (R 6) [34,68,136,272,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,5] 13 (by decide) (choices 1) [1,2,64] r36227 c36227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20567
  · exact u20568
  · exact u20569

def b36228 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 70 140 280 22 97 97 225 353), lower := (rows 35 70 140 280 22 32 64 128 256), losses := [] }

theorem u36228 : Upper (D 6) (R 6) [34,68,136,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36229 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 140 280 49 103 71 199 327), lower := (rows 35 70 140 280 49 32 64 128 256), losses := [] }

theorem u36229 : Upper (D 6) (R 6) [34,68,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36230 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 70 140 280 50 101 69 197 325), lower := (rows 35 70 140 280 50 32 64 128 256), losses := [] }

theorem u36230 : Upper (D 6) (R 6) [34,68,136,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36231 : Route 9 := (fun mask => (mask,id))

def c36231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36231 : Upper (D 6) (R 6) [34,68,136,272,36] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,36] 13 (by decide) (choices 1) [1,2,64] r36231 c36231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20570
  · exact u20571
  · exact u20572

def r36232 : Route 9 := (fun mask => (mask,id))

def c36232 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36232 : Upper (D 6) (R 6) [34,68,136,272,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,65] 13 (by decide) (choices 1) [1,2,4] r36232 c36232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20573
  · exact u20574
  · exact u20575

def b36233 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 140 280 82 37 101 165 293), lower := (rows 35 70 140 280 82 32 64 128 256), losses := [] }

theorem u36233 : Upper (D 6) (R 6) [34,68,136,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36234 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 140 280 84 35 99 163 291), lower := (rows 35 70 140 280 84 32 64 128 256), losses := [] }

theorem u36234 : Upper (D 6) (R 6) [34,68,136,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36235 : Route 9 := (fun mask => (mask,id))

def c36235 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36235 : Upper (D 6) (R 6) [34,68,136,272,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,96] 13 (by decide) (choices 1) [1,2,4] r36235 c36235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20576
  · exact u20577
  · exact u20578

def b36236 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 140 296 19 117 85 213 341), lower := (rows 35 70 140 296 19 32 64 128 256), losses := [] }

theorem u36236 : Upper (D 6) (R 6) [34,68,136,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36237 : Route 9 := (fun mask => (mask,id))

def c36237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36237 : Upper (D 6) (R 6) [34,68,136,288,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,5] 13 (by decide) (choices 1) [1,2,16,64] r36237 c36237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20579
  · exact u20580
  · exact u20581
  · exact u20582

def b36238 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 70 140 296 22 113 81 209 337), lower := (rows 35 70 140 296 22 32 64 128 256), losses := [] }

theorem u36238 : Upper (D 6) (R 6) [34,68,136,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36239 : Route 9 := (fun mask => (mask,id))

def c36239 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36239 : Upper (D 6) (R 6) [34,68,136,288,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,65] 13 (by decide) (choices 1) [1,2,4,16] r36239 c36239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20583
  · exact u20584
  · exact u20585
  · exact u20586

#print axioms u36239
end Delivery.IrregularNine14.P06
