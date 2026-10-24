import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0423
import IrregularNine14P06C0424
import IrregularNine14P06C0425

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39180 : Route 9 := (fun mask => (mask,id))

def c39180 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39180 : Upper (D 6) (R 6) [40,48,129,66,260] 13 := by
  apply FastRouting.sound _ _ [40,48,129,66,260] 13 (by decide) (choices 1) [1,2,4,64] r39180 c39180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25431
  · exact u25432
  · exact u25433
  · exact u25434

def r39181 : Route 9 := (fun mask => (mask,id))

def c39181 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39181 : Upper (D 6) (R 6) [40,48,129,66,320] 13 := by
  apply FastRouting.sound _ _ [40,48,129,66,320] 13 (by decide) (choices 1) [1,2,4] r39181 c39181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25435
  · exact u25436
  · exact u25437

def b39182 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 18, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 133 76 19 358 326 454 326), lower := (rows 41 50 133 76 19 32 64 128 256), losses := [] }

theorem u39182 : Upper (D 6) (R 6) [40,48,129,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39183 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 50 133 76 21 354 322 450 322), lower := (rows 41 50 133 76 21 32 64 128 256), losses := [] }

theorem u39183 : Upper (D 6) (R 6) [40,48,129,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39184 : Route 9 := (fun mask => (mask,id))

def c39184 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39184 : Upper (D 6) (R 6) [40,48,129,68,6] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68,6] 13 (by decide) (choices 1) [1,2,64,256] r39184 c39184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25438
  · exact u25439
  · exact u25440
  · exact u25441

def r39185 : Route 9 := (fun mask => (mask,id))

def c39185 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39185 : Upper (D 6) (R 6) [40,48,129,68,65] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68,65] 13 (by decide) (choices 1) [2,4,256] r39185 c39185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25442
  · exact u25443
  · exact u25444

def r39186 : Route 9 := (fun mask => (mask,id))

def c39186 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39186 : Upper (D 6) (R 6) [40,48,129,68,66] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68,66] 13 (by decide) (choices 1) [1,2,4,256] r39186 c39186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25445
  · exact u25446
  · exact u25447
  · exact u25448

def b39187 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 50 133 76 84 291 323 387 259), lower := (rows 41 50 133 76 84 32 64 128 256), losses := [] }

theorem u39187 : Upper (D 6) (R 6) [40,48,129,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39188 : Route 9 := (fun mask => (mask,id))

def c39188 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39188 : Upper (D 6) (R 6) [40,48,129,68,257] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68,257] 13 (by decide) (choices 1) [2,4,64] r39188 c39188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25449
  · exact u25450
  · exact u25451

def r39189 : Route 9 := (fun mask => (mask,id))

def c39189 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39189 : Upper (D 6) (R 6) [40,48,129,68,258] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68,258] 13 (by decide) (choices 1) [1,2,4,64] r39189 c39189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25452
  · exact u25453
  · exact u25454
  · exact u25455

def r39190 : Route 9 := (fun mask => (mask,id))

def c39190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39190 : Upper (D 6) (R 6) [40,48,129,68,260] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68,260] 13 (by decide) (choices 1) [1,2,64] r39190 c39190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25456
  · exact u25457
  · exact u25458

def r39191 : Route 9 := (fun mask => (mask,id))

def c39191 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39191 : Upper (D 6) (R 6) [40,48,129,68,320] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68,320] 13 (by decide) (choices 1) [1,2,4] r39191 c39191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25459
  · exact u25460
  · exact u25461

def r39192 : Route 9 := (fun mask => (mask,id))

def c39192 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39192 : Upper (D 6) (R 6) [40,48,129,257,6] 13 := by
  apply FastRouting.sound _ _ [40,48,129,257,6] 13 (by decide) (choices 1) [2,4,64] r39192 c39192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25462
  · exact u25463
  · exact u25464

def r39193 : Route 9 := (fun mask => (mask,id))

def c39193 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39193 : Upper (D 6) (R 6) [40,48,129,257,66] 13 := by
  apply FastRouting.sound _ _ [40,48,129,257,66] 13 (by decide) (choices 1) [2,4,64] r39193 c39193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25465
  · exact u25466
  · exact u25467

def r39194 : Route 9 := (fun mask => (mask,id))

def c39194 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39194 : Upper (D 6) (R 6) [40,48,129,257,68] 13 := by
  apply FastRouting.sound _ _ [40,48,129,257,68] 13 (by decide) (choices 1) [2,4,64] r39194 c39194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25468
  · exact u25469
  · exact u25470

def b39195 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 18, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 133 266 19 100 68 196 324), lower := (rows 41 50 133 266 19 32 64 128 256), losses := [] }

theorem u39195 : Upper (D 6) (R 6) [40,48,129,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39196 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 50 133 266 21 102 70 198 326), lower := (rows 41 50 133 266 21 32 64 128 256), losses := [] }

theorem u39196 : Upper (D 6) (R 6) [40,48,129,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39197 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 133 266 22 101 69 197 325), lower := (rows 41 50 133 266 22 32 64 128 256), losses := [] }

theorem u39197 : Upper (D 6) (R 6) [40,48,129,258,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39198 : Route 9 := (fun mask => (mask,id))

def c39198 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39198 : Upper (D 6) (R 6) [40,48,129,258,65] 13 := by
  apply FastRouting.sound _ _ [40,48,129,258,65] 13 (by decide) (choices 1) [2,4,64] r39198 c39198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25471
  · exact u25472
  · exact u25473

def b39199 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 133 266 82 101 69 197 325), lower := (rows 41 50 133 266 82 32 64 128 256), losses := [] }

theorem u39199 : Upper (D 6) (R 6) [40,48,129,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39200 : Route 9 := (fun mask => (mask,id))

def c39200 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39200 : Upper (D 6) (R 6) [40,48,129,258,68] 13 := by
  apply FastRouting.sound _ _ [40,48,129,258,68] 13 (by decide) (choices 1) [1,2,4,64] r39200 c39200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25474
  · exact u25475
  · exact u25476
  · exact u25477

def b39201 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 18, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 133 268 19 102 70 198 326), lower := (rows 41 50 133 268 19 32 64 128 256), losses := [] }

theorem u39201 : Upper (D 6) (R 6) [40,48,129,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39202 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 50 133 268 21 98 66 194 322), lower := (rows 41 50 133 268 21 32 64 128 256), losses := [] }

theorem u39202 : Upper (D 6) (R 6) [40,48,129,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39203 : Route 9 := (fun mask => (mask,id))

def c39203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39203 : Upper (D 6) (R 6) [40,48,129,260,6] 13 := by
  apply FastRouting.sound _ _ [40,48,129,260,6] 13 (by decide) (choices 1) [1,2,64] r39203 c39203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25478
  · exact u25479
  · exact u25480

def r39204 : Route 9 := (fun mask => (mask,id))

def c39204 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39204 : Upper (D 6) (R 6) [40,48,129,260,65] 13 := by
  apply FastRouting.sound _ _ [40,48,129,260,65] 13 (by decide) (choices 1) [2,4,64] r39204 c39204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25481
  · exact u25482
  · exact u25483

def r39205 : Route 9 := (fun mask => (mask,id))

def c39205 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39205 : Upper (D 6) (R 6) [40,48,129,260,66] 13 := by
  apply FastRouting.sound _ _ [40,48,129,260,66] 13 (by decide) (choices 1) [1,2,4,64] r39205 c39205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25484
  · exact u25485
  · exact u25486
  · exact u25487

def r39206 : Route 9 := (fun mask => (mask,id))

def c39206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39206 : Upper (D 6) (R 6) [40,48,129,260,68] 13 := by
  apply FastRouting.sound _ _ [40,48,129,260,68] 13 (by decide) (choices 1) [1,2,64] r39206 c39206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25488
  · exact u25489
  · exact u25490

def b39207 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 18, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 133 328 19 102 70 198 326), lower := (rows 41 50 133 328 19 32 64 128 256), losses := [] }

theorem u39207 : Upper (D 6) (R 6) [40,48,129,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39208 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 50 133 328 21 102 70 198 326), lower := (rows 41 50 133 328 21 32 64 128 256), losses := [] }

theorem u39208 : Upper (D 6) (R 6) [40,48,129,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39209 : Route 9 := (fun mask => (mask,id))

def c39209 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39209 : Upper (D 6) (R 6) [40,48,129,320,6] 13 := by
  apply FastRouting.sound _ _ [40,48,129,320,6] 13 (by decide) (choices 1) [1,2,4,64] r39209 c39209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25491
  · exact u25492
  · exact u25493
  · exact u25494

def r39210 : Route 9 := (fun mask => (mask,id))

def c39210 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39210 : Upper (D 6) (R 6) [40,48,129,320,65] 13 := by
  apply FastRouting.sound _ _ [40,48,129,320,65] 13 (by decide) (choices 1) [2,4] r39210 c39210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25495
  · exact u25496

def r39211 : Route 9 := (fun mask => (mask,id))

def c39211 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39211 : Upper (D 6) (R 6) [40,48,129,320,66] 13 := by
  apply FastRouting.sound _ _ [40,48,129,320,66] 13 (by decide) (choices 1) [1,2,4] r39211 c39211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25497
  · exact u25498
  · exact u25499

def r39212 : Route 9 := (fun mask => (mask,id))

def c39212 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39212 : Upper (D 6) (R 6) [40,48,129,320,68] 13 := by
  apply FastRouting.sound _ _ [40,48,129,320,68] 13 (by decide) (choices 1) [1,2,4] r39212 c39212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25500
  · exact u25501
  · exact u25502

def b39213 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 196 11 21 358 326 454 326), lower := (rows 41 50 196 11 21 32 64 128 256), losses := [] }

theorem u39213 : Upper (D 6) (R 6) [40,48,192,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39214 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 196 11 22 357 325 453 325), lower := (rows 41 50 196 11 22 32 64 128 256), losses := [] }

theorem u39214 : Upper (D 6) (R 6) [40,48,192,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39215 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 196 11 81 294 326 390 262), lower := (rows 41 50 196 11 81 32 64 128 256), losses := [] }

theorem u39215 : Upper (D 6) (R 6) [40,48,192,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39216 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 196 11 82 293 325 389 261), lower := (rows 41 50 196 11 82 32 64 128 256), losses := [] }

theorem u39216 : Upper (D 6) (R 6) [40,48,192,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39217 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 196 11 273 102 70 198 326), lower := (rows 41 50 196 11 273 32 64 128 256), losses := [] }

theorem u39217 : Upper (D 6) (R 6) [40,48,192,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39218 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 196 11 274 101 69 197 325), lower := (rows 41 50 196 11 274 32 64 128 256), losses := [] }

theorem u39218 : Upper (D 6) (R 6) [40,48,192,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39219 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 196 11 276 103 71 199 327), lower := (rows 41 50 196 11 276 32 64 128 256), losses := [] }

theorem u39219 : Upper (D 6) (R 6) [40,48,192,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39220 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 196 11 336 39 71 135 263), lower := (rows 41 50 196 11 336 32 64 128 256), losses := [] }

theorem u39220 : Upper (D 6) (R 6) [40,48,192,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39221 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 50 196 13 21 354 322 450 322), lower := (rows 41 50 196 13 21 32 64 128 256), losses := [] }

theorem u39221 : Upper (D 6) (R 6) [40,48,192,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39222 : PairBound 9 := { available := 323, camps := [], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 50 196 13 22 355 323 451 323), lower := (rows 41 50 196 13 22 32 64 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 24 32 64 128 256), good := (rows 58 50 196 30 22 32 64 128 256) },{ target := 1, region := (rows 3 0 4 24 16 32 64 128 256), good := (rows 41 57 196 13 29 32 64 128 256) }] }

theorem u39222 : Upper (D 6) (R 6) [40,48,192,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39223 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 50 196 13 81 294 326 390 262), lower := (rows 41 50 196 13 81 32 64 128 256), losses := [] }

theorem u39223 : Upper (D 6) (R 6) [40,48,192,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39224 : Route 9 := (fun mask => (mask,id))

def c39224 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39224 : Upper (D 6) (R 6) [40,48,192,5,66] 13 := by
  apply FastRouting.sound _ _ [40,48,192,5,66] 13 (by decide) (choices 1) [1,2,4,256] r39224 c39224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25503
  · exact u25504
  · exact u25505
  · exact u25506

def b39225 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 50 196 13 84 291 323 387 259), lower := (rows 41 50 196 13 84 32 64 128 256), losses := [] }

theorem u39225 : Upper (D 6) (R 6) [40,48,192,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39226 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 50 196 13 273 102 70 198 326), lower := (rows 41 50 196 13 273 32 64 128 256), losses := [] }

theorem u39226 : Upper (D 6) (R 6) [40,48,192,5,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39227 : Route 9 := (fun mask => (mask,id))

def c39227 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39227 : Upper (D 6) (R 6) [40,48,192,5,258] 13 := by
  apply FastRouting.sound _ _ [40,48,192,5,258] 13 (by decide) (choices 1) [1,2,4,64] r39227 c39227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25507
  · exact u25508
  · exact u25509
  · exact u25510

def r39228 : Route 9 := (fun mask => (mask,id))

def c39228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39228 : Upper (D 6) (R 6) [40,48,192,5,260] 13 := by
  apply FastRouting.sound _ _ [40,48,192,5,260] 13 (by decide) (choices 1) [1,2,64] r39228 c39228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25511
  · exact u25512
  · exact u25513

def r39229 : Route 9 := (fun mask => (mask,id))

def c39229 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39229 : Upper (D 6) (R 6) [40,48,192,5,320] 13 := by
  apply FastRouting.sound _ _ [40,48,192,5,320] 13 (by decide) (choices 1) [1,2,4] r39229 c39229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25514
  · exact u25515
  · exact u25516

def b39230 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 353, targets := 4 },{ cop := 4, region := 354, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 41 50 196 14 21 355 323 451 323), lower := (rows 41 50 196 14 21 32 64 128 256), losses := [{ target := 6, region := (rows 3 3 4 24 24 32 0 128 256), good := (rows 59 59 132 31 31 32 0 128 256) }] }

theorem u39230 : Upper (D 6) (R 6) [40,48,192,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39231 : Route 9 := (fun mask => (mask,id))

def c39231 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39231 : Upper (D 6) (R 6) [40,48,192,6,65] 13 := by
  apply FastRouting.sound _ _ [40,48,192,6,65] 13 (by decide) (choices 1) [1,2,4,256] r39231 c39231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25517
  · exact u25518
  · exact u25519
  · exact u25520

def b39232 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 485, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 196 14 82 293 325 389 261), lower := (rows 41 50 196 14 82 32 64 128 256), losses := [] }

theorem u39232 : Upper (D 6) (R 6) [40,48,192,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39233 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 50 196 14 84 291 323 387 259), lower := (rows 41 50 196 14 84 32 64 128 256), losses := [] }

theorem u39233 : Upper (D 6) (R 6) [40,48,192,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39234 : Route 9 := (fun mask => (mask,id))

def c39234 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39234 : Upper (D 6) (R 6) [40,48,192,6,257] 13 := by
  apply FastRouting.sound _ _ [40,48,192,6,257] 13 (by decide) (choices 1) [1,2,4,64] r39234 c39234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25521
  · exact u25522
  · exact u25523
  · exact u25524

def b39235 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 196 14 274 101 69 197 325), lower := (rows 41 50 196 14 274 32 64 128 256), losses := [] }

theorem u39235 : Upper (D 6) (R 6) [40,48,192,6,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39236 : Route 9 := (fun mask => (mask,id))

def c39236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39236 : Upper (D 6) (R 6) [40,48,192,6,260] 13 := by
  apply FastRouting.sound _ _ [40,48,192,6,260] 13 (by decide) (choices 1) [1,2,64] r39236 c39236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25525
  · exact u25526
  · exact u25527

def r39237 : Route 9 := (fun mask => (mask,id))

def c39237 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39237 : Upper (D 6) (R 6) [40,48,192,6,320] 13 := by
  apply FastRouting.sound _ _ [40,48,192,6,320] 13 (by decide) (choices 1) [1,2,4] r39237 c39237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25528
  · exact u25529
  · exact u25530

def b39238 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 50 196 73 273 38 70 134 262), lower := (rows 41 50 196 73 273 32 64 128 256), losses := [] }

theorem u39238 : Upper (D 6) (R 6) [40,48,192,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39239 : Route 9 := (fun mask => (mask,id))

def c39239 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39239 : Upper (D 6) (R 6) [40,48,192,65,258] 13 := by
  apply FastRouting.sound _ _ [40,48,192,65,258] 13 (by decide) (choices 1) [1,2,4] r39239 c39239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25531
  · exact u25532
  · exact u25533

#print axioms u39239
end Delivery.IrregularNine14.P06
