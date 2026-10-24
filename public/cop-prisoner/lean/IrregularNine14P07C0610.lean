import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0371
import IrregularNine14P07C0372
import IrregularNine14P07C0373

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36600 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 69 328 19 178 210 146 402), lower := (rows 37 42 69 328 19 32 64 128 256), losses := [] }

theorem u36600 : Upper (D 7) (R 7) [36,40,65,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36601 : Route 9 := (fun mask => (mask,id))

def c36601 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36601 : Upper (D 7) (R 7) [36,40,65,320,129] 13 := by
  apply FastRouting.sound _ _ [36,40,65,320,129] 13 (by decide) (choices 1) [2,16,128] r36601 c36601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22303
  · exact u22304
  · exact u22305

def r36602 : Route 9 := (fun mask => (mask,id))

def c36602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36602 : Upper (D 7) (R 7) [36,40,65,320,130] 13 := by
  apply FastRouting.sound _ _ [36,40,65,320,130] 13 (by decide) (choices 1) [1,2,16,128] r36602 c36602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22306
  · exact u22307
  · exact u22308
  · exact u22309

def b36603 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 69 392 19 242 210 210 466), lower := (rows 37 42 69 392 19 32 64 128 256), losses := [] }

theorem u36603 : Upper (D 7) (R 7) [36,40,65,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36604 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 42 69 392 81 178 210 146 402), lower := (rows 37 42 69 392 81 32 64 128 256), losses := [] }

theorem u36604 : Upper (D 7) (R 7) [36,40,65,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36605 : Route 9 := (fun mask => (mask,id))

def c36605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36605 : Upper (D 7) (R 7) [36,40,65,384,66] 13 := by
  apply FastRouting.sound _ _ [36,40,65,384,66] 13 (by decide) (choices 1) [1,2,16,128] r36605 c36605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22310
  · exact u22311
  · exact u22312
  · exact u22313

def r36606 : Route 9 := (fun mask => (mask,id))

def c36606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36606 : Upper (D 7) (R 7) [36,40,65,384,129] 13 := by
  apply FastRouting.sound _ _ [36,40,65,384,129] 13 (by decide) (choices 1) [2,16,64] r36606 c36606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22314
  · exact u22315
  · exact u22316

def r36607 : Route 9 := (fun mask => (mask,id))

def c36607 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36607 : Upper (D 7) (R 7) [36,40,65,384,130] 13 := by
  apply FastRouting.sound _ _ [36,40,65,384,130] 13 (by decide) (choices 1) [1,2,16,64] r36607 c36607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22317
  · exact u22318
  · exact u22319
  · exact u22320

def r36608 : Route 9 := (fun mask => (mask,id))

def c36608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36608 : Upper (D 7) (R 7) [36,40,65,384,192] 13 := by
  apply FastRouting.sound _ _ [36,40,65,384,192] 13 (by decide) (choices 1) [1,2,16] r36608 c36608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22321
  · exact u22322
  · exact u22323

def b36609 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 4, region := 460, targets := 32 }], pairs := [(0,6),(2,5),(3,5),(4,6)], upper := (rows 37 42 70 88 19 417 449 385 385), lower := (rows 37 42 70 88 19 32 64 128 256), losses := [] }

theorem u36609 : Upper (D 7) (R 7) [36,40,66,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36610 : Route 9 := (fun mask => (mask,id))

def c36610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36610 : Upper (D 7) (R 7) [36,40,66,80,129] 13 := by
  apply FastRouting.sound _ _ [36,40,66,80,129] 13 (by decide) (choices 1) [1,2,128,256] r36610 c36610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22324
  · exact u22325
  · exact u22326
  · exact u22327

def r36611 : Route 9 := (fun mask => (mask,id))

def c36611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36611 : Upper (D 7) (R 7) [36,40,66,80,130] 13 := by
  apply FastRouting.sound _ _ [36,40,66,80,130] 13 (by decide) (choices 1) [1,128,256] r36611 c36611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22328
  · exact u22329
  · exact u22330

def r36612 : Route 9 := (fun mask => (mask,id))

def c36612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36612 : Upper (D 7) (R 7) [36,40,66,80,257] 13 := by
  apply FastRouting.sound _ _ [36,40,66,80,257] 13 (by decide) (choices 1) [1,2,128] r36612 c36612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22331
  · exact u22332
  · exact u22333

def r36613 : Route 9 := (fun mask => (mask,id))

def c36613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36613 : Upper (D 7) (R 7) [36,40,66,80,258] 13 := by
  apply FastRouting.sound _ _ [36,40,66,80,258] 13 (by decide) (choices 1) [1,128] r36613 c36613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22334
  · exact u22335

def r36614 : Route 9 := (fun mask => (mask,id))

def c36614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36614 : Upper (D 7) (R 7) [36,40,66,80,384] 13 := by
  apply FastRouting.sound _ _ [36,40,66,80,384] 13 (by decide) (choices 1) [1,2,128] r36614 c36614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22336
  · exact u22337
  · exact u22338

def b36615 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 452, targets := 1 },{ cop := 4, region := 456, targets := 2 }], pairs := [(2,0),(2,5),(3,1),(3,5)], upper := (rows 37 42 70 137 19 496 464 464 464), lower := (rows 37 42 70 137 19 32 64 128 256), losses := [] }

theorem u36615 : Upper (D 7) (R 7) [36,40,66,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36616 : Route 9 := (fun mask => (mask,id))

def c36616 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u36616 : Upper (D 7) (R 7) [36,40,66,129,65] 13 := by
  apply FastRouting.sound _ _ [36,40,66,129,65] 13 (by decide) (choices 1) [2,16,128,256] r36616 c36616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22339
  · exact u22340
  · exact u22341
  · exact u22342

def b36617 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 42 70 137 82 433 465 401 401), lower := (rows 37 42 70 137 82 32 64 128 256), losses := [] }

theorem u36617 : Upper (D 7) (R 7) [36,40,66,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m36618_2 : Upper (D 7) (R 7) [36,40,66,129,192,2] 13 :=
  permutation_upper _ _ _ [36,40,66,129,192,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22343

def r36618 : Route 9 := (fun mask => (mask,id))

def c36618 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36618 : Upper (D 7) (R 7) [36,40,66,129,192] 13 := by
  apply FastRouting.sound _ _ [36,40,66,129,192] 13 (by decide) (choices 1) [1,2,16,256] r36618 c36618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22343
  · exact m36618_2
  · exact u22344
  · exact u22345

def r36619 : Route 9 := (fun mask => (mask,id))

def c36619 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36619 : Upper (D 7) (R 7) [36,40,66,129,257] 13 := by
  apply FastRouting.sound _ _ [36,40,66,129,257] 13 (by decide) (choices 1) [2,16,64,128] r36619 c36619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22346
  · exact u22347
  · exact u22348
  · exact u22349

def r36620 : Route 9 := (fun mask => (mask,id))

def c36620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36620 : Upper (D 7) (R 7) [36,40,66,129,320] 13 := by
  apply FastRouting.sound _ _ [36,40,66,129,320] 13 (by decide) (choices 1) [1,2,16,128] r36620 c36620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22350
  · exact u22351
  · exact u22352
  · exact u22353

def b36621 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 2, region := 417, targets := 2 },{ cop := 4, region := 456, targets := 2 }], pairs := [(0,1),(2,5),(3,1),(3,5)], upper := (rows 37 42 70 152 19 481 449 449 449), lower := (rows 37 42 70 152 19 32 64 128 256), losses := [] }

theorem u36621 : Upper (D 7) (R 7) [36,40,66,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36622 : Route 9 := (fun mask => (mask,id))

def c36622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36622 : Upper (D 7) (R 7) [36,40,66,144,65] 13 := by
  apply FastRouting.sound _ _ [36,40,66,144,65] 13 (by decide) (choices 1) [1,2,128,256] r36622 c36622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22354
  · exact u22355
  · exact u22356
  · exact u22357

def b36623 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 42 70 152 82 417 449 385 385), lower := (rows 37 42 70 152 82 32 64 128 256), losses := [] }

theorem u36623 : Upper (D 7) (R 7) [36,40,66,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36624 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 42 70 152 145 355 323 451 323), lower := (rows 37 42 70 152 145 32 64 128 256), losses := [] }

theorem u36624 : Upper (D 7) (R 7) [36,40,66,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36625 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 42 70 152 146 353 321 449 321), lower := (rows 37 42 70 152 146 32 64 128 256), losses := [] }

theorem u36625 : Upper (D 7) (R 7) [36,40,66,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36626 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 42 70 152 208 291 323 387 259), lower := (rows 37 42 70 152 208 32 64 128 256), losses := [] }

theorem u36626 : Upper (D 7) (R 7) [36,40,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36627 : Route 9 := (fun mask => (mask,id))

def c36627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36627 : Upper (D 7) (R 7) [36,40,66,144,257] 13 := by
  apply FastRouting.sound _ _ [36,40,66,144,257] 13 (by decide) (choices 1) [1,2,64,128] r36627 c36627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22358
  · exact u22359
  · exact u22360
  · exact u22361

def r36628 : Route 9 := (fun mask => (mask,id))

def c36628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36628 : Upper (D 7) (R 7) [36,40,66,144,258] 13 := by
  apply FastRouting.sound _ _ [36,40,66,144,258] 13 (by decide) (choices 1) [1,64,128] r36628 c36628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22362
  · exact u22363
  · exact u22364

def r36629 : Route 9 := (fun mask => (mask,id))

def c36629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36629 : Upper (D 7) (R 7) [36,40,66,144,320] 13 := by
  apply FastRouting.sound _ _ [36,40,66,144,320] 13 (by decide) (choices 1) [1,2,128] r36629 c36629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22365
  · exact u22366
  · exact u22367

def b36630 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 42 70 152 400 99 67 195 323), lower := (rows 37 42 70 152 400 32 64 128 256), losses := [] }

theorem u36630 : Upper (D 7) (R 7) [36,40,66,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36631 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 4, region := 460, targets := 32 }], pairs := [(0,6),(2,5),(3,5),(4,6)], upper := (rows 37 42 70 200 19 433 465 401 401), lower := (rows 37 42 70 200 19 32 64 128 256), losses := [] }

theorem u36631 : Upper (D 7) (R 7) [36,40,66,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36632 : Route 9 := (fun mask => (mask,id))

def c36632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36632 : Upper (D 7) (R 7) [36,40,66,192,129] 13 := by
  apply FastRouting.sound _ _ [36,40,66,192,129] 13 (by decide) (choices 1) [1,2,16,256] r36632 c36632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22368
  · exact u22369
  · exact u22370
  · exact u22371

def b36633 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 37 42 70 200 146 305 337 401 273), lower := (rows 37 42 70 200 146 32 64 128 256), losses := [] }

theorem u36633 : Upper (D 7) (R 7) [36,40,66,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36634 : Route 9 := (fun mask => (mask,id))

def c36634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36634 : Upper (D 7) (R 7) [36,40,66,192,257] 13 := by
  apply FastRouting.sound _ _ [36,40,66,192,257] 13 (by decide) (choices 1) [1,2,16,128] r36634 c36634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22372
  · exact u22373
  · exact u22374
  · exact u22375

def r36635 : Route 9 := (fun mask => (mask,id))

def c36635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36635 : Upper (D 7) (R 7) [36,40,66,192,258] 13 := by
  apply FastRouting.sound _ _ [36,40,66,192,258] 13 (by decide) (choices 1) [1,16,128] r36635 c36635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22376
  · exact u22377
  · exact u22378

def r36636 : Route 9 := (fun mask => (mask,id))

def c36636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36636 : Upper (D 7) (R 7) [36,40,66,192,384] 13 := by
  apply FastRouting.sound _ _ [36,40,66,192,384] 13 (by decide) (choices 1) [1,2,16] r36636 c36636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22379
  · exact u22380
  · exact u22381

def b36637 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 196, targets := 1 },{ cop := 4, region := 456, targets := 2 }], pairs := [(2,0),(2,5),(3,1),(3,5)], upper := (rows 37 42 70 265 19 240 208 208 464), lower := (rows 37 42 70 265 19 32 64 128 256), losses := [] }

theorem u36637 : Upper (D 7) (R 7) [36,40,66,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36638 : Route 9 := (fun mask => (mask,id))

def c36638 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36638 : Upper (D 7) (R 7) [36,40,66,257,65] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257,65] 13 (by decide) (choices 1) [2,16,128] r36638 c36638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22382
  · exact u22383
  · exact u22384

def b36639 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 42 70 265 82 177 209 145 401), lower := (rows 37 42 70 265 82 32 64 128 256), losses := [] }

theorem u36639 : Upper (D 7) (R 7) [36,40,66,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36640 : Route 9 := (fun mask => (mask,id))

def c36640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36640 : Upper (D 7) (R 7) [36,40,66,257,129] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257,129] 13 (by decide) (choices 1) [2,16,64,128] r36640 c36640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22385
  · exact u22386
  · exact u22387
  · exact u22388

def r36641 : Route 9 := (fun mask => (mask,id))

def c36641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36641 : Upper (D 7) (R 7) [36,40,66,257,130] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257,130] 13 (by decide) (choices 1) [1,16,64,128] r36641 c36641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22389
  · exact u22390
  · exact u22391
  · exact u22392

def r36642 : Route 9 := (fun mask => (mask,id))

def c36642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36642 : Upper (D 7) (R 7) [36,40,66,257,192] 13 := by
  apply FastRouting.sound _ _ [36,40,66,257,192] 13 (by decide) (choices 1) [1,2,16,128] r36642 c36642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22393
  · exact u22394
  · exact u22395
  · exact u22396

def b36643 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 42 70 266 81 177 209 145 401), lower := (rows 37 42 70 266 81 32 64 128 256), losses := [] }

theorem u36643 : Upper (D 7) (R 7) [36,40,66,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36644 : Route 9 := (fun mask => (mask,id))

def c36644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36644 : Upper (D 7) (R 7) [36,40,66,258,129] 13 := by
  apply FastRouting.sound _ _ [36,40,66,258,129] 13 (by decide) (choices 1) [1,16,64,128] r36644 c36644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22397
  · exact u22398
  · exact u22399
  · exact u22400

def r36645 : Route 9 := (fun mask => (mask,id))

def c36645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36645 : Upper (D 7) (R 7) [36,40,66,258,192] 13 := by
  apply FastRouting.sound _ _ [36,40,66,258,192] 13 (by decide) (choices 1) [1,16,128] r36645 c36645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22401
  · exact u22402
  · exact u22403

def b36646 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 2, region := 161, targets := 2 },{ cop := 4, region := 456, targets := 2 }], pairs := [(0,1),(2,5),(3,1),(3,5)], upper := (rows 37 42 70 280 19 225 193 193 449), lower := (rows 37 42 70 280 19 32 64 128 256), losses := [] }

theorem u36646 : Upper (D 7) (R 7) [36,40,66,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36647 : Route 9 := (fun mask => (mask,id))

def c36647 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36647 : Upper (D 7) (R 7) [36,40,66,272,65] 13 := by
  apply FastRouting.sound _ _ [36,40,66,272,65] 13 (by decide) (choices 1) [1,2,128] r36647 c36647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22404
  · exact u22405
  · exact u22406

def b36648 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 42 70 280 82 161 193 129 385), lower := (rows 37 42 70 280 82 32 64 128 256), losses := [] }

theorem u36648 : Upper (D 7) (R 7) [36,40,66,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36649 : Route 9 := (fun mask => (mask,id))

def c36649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36649 : Upper (D 7) (R 7) [36,40,66,272,129] 13 := by
  apply FastRouting.sound _ _ [36,40,66,272,129] 13 (by decide) (choices 1) [1,2,64,128] r36649 c36649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22407
  · exact u22408
  · exact u22409
  · exact u22410

def r36650 : Route 9 := (fun mask => (mask,id))

def c36650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36650 : Upper (D 7) (R 7) [36,40,66,272,130] 13 := by
  apply FastRouting.sound _ _ [36,40,66,272,130] 13 (by decide) (choices 1) [1,64,128] r36650 c36650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22411
  · exact u22412
  · exact u22413

def r36651 : Route 9 := (fun mask => (mask,id))

def c36651 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36651 : Upper (D 7) (R 7) [36,40,66,272,192] 13 := by
  apply FastRouting.sound _ _ [36,40,66,272,192] 13 (by decide) (choices 1) [1,2,128] r36651 c36651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22414
  · exact u22415
  · exact u22416

def b36652 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 460, targets := 32 }], pairs := [(0,6),(2,5),(3,5),(4,6)], upper := (rows 37 42 70 328 19 177 209 145 401), lower := (rows 37 42 70 328 19 32 64 128 256), losses := [] }

theorem u36652 : Upper (D 7) (R 7) [36,40,66,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36653 : Route 9 := (fun mask => (mask,id))

def c36653 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36653 : Upper (D 7) (R 7) [36,40,66,320,129] 13 := by
  apply FastRouting.sound _ _ [36,40,66,320,129] 13 (by decide) (choices 1) [1,2,16,128] r36653 c36653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22417
  · exact u22418
  · exact u22419
  · exact u22420

def r36654 : Route 9 := (fun mask => (mask,id))

def c36654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36654 : Upper (D 7) (R 7) [36,40,66,320,130] 13 := by
  apply FastRouting.sound _ _ [36,40,66,320,130] 13 (by decide) (choices 1) [1,16,128] r36654 c36654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22421
  · exact u22422
  · exact u22423

def r36655 : Route 9 := (fun mask => (mask,id))

def c36655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36655 : Upper (D 7) (R 7) [36,40,66,384,3] 13 := by
  apply FastRouting.sound _ _ [36,40,66,384,3] 13 (by decide) (choices 1) [1,16,64,128] r36655 c36655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22424
  · exact u22425
  · exact u22426
  · exact u22427

def r36656 : Route 9 := (fun mask => (mask,id))

def c36656 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36656 : Upper (D 7) (R 7) [36,40,66,384,65] 13 := by
  apply FastRouting.sound _ _ [36,40,66,384,65] 13 (by decide) (choices 1) [1,2,16,128] r36656 c36656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22428
  · exact u22429
  · exact u22430
  · exact u22431

def b36657 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 42 70 392 82 177 209 145 401), lower := (rows 37 42 70 392 82 32 64 128 256), losses := [] }

theorem u36657 : Upper (D 7) (R 7) [36,40,66,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36658 : Route 9 := (fun mask => (mask,id))

def c36658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36658 : Upper (D 7) (R 7) [36,40,66,384,129] 13 := by
  apply FastRouting.sound _ _ [36,40,66,384,129] 13 (by decide) (choices 1) [1,2,16,64] r36658 c36658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22432
  · exact u22433
  · exact u22434
  · exact u22435

def r36659 : Route 9 := (fun mask => (mask,id))

def c36659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36659 : Upper (D 7) (R 7) [36,40,66,384,130] 13 := by
  apply FastRouting.sound _ _ [36,40,66,384,130] 13 (by decide) (choices 1) [1,16,64] r36659 c36659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22436
  · exact u22437
  · exact u22438

#print axioms u36659
end Delivery.IrregularNine14.P07
