import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0655
import IrregularNine14P07C0656
import IrregularNine14P07C0657
import IrregularNine14P07C0658
import IrregularNine14P07C0659

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r43440 : Route 9 := (fun mask => (mask,id))

def c43440 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43440 : Upper (D 7) (R 7) [36,320,9,192] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43440 c43440
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39342
  · exact u39343
  · exact u39344
  · exact u39345
  · exact u39346
  · exact u39347

def b43441 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 322 14 11 241 241 241 241 497), lower := (rows 37 322 14 11 16 32 64 128 256), losses := [] }

theorem u43441 : Upper (D 7) (R 7) [36,320,10,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43442 : Route 9 := (fun mask => (mask,id))

def c43442 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43442 : Upper (D 7) (R 7) [36,320,10,17] 13 := by
  apply FastRouting.sound _ _ [36,320,10,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43442 c43442
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39348
  · exact u39349
  · exact u39350
  · exact u39351
  · exact u39352
  · exact u39353
  · exact u39354
  · exact u39355
  · exact u39356
  · exact u39357

def b43443 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 322 14 26 241 225 225 225 481), lower := (rows 37 322 14 26 16 32 64 128 256), losses := [] }

theorem u43443 : Upper (D 7) (R 7) [36,320,10,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43444 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 14 41 211 243 211 211 467), lower := (rows 37 322 14 41 16 32 64 128 256), losses := [] }

theorem u43444 : Upper (D 7) (R 7) [36,320,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43445 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 14 42 209 241 209 209 465), lower := (rows 37 322 14 42 16 32 64 128 256), losses := [] }

theorem u43445 : Upper (D 7) (R 7) [36,320,10,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43446 : Route 9 := (fun mask => (mask,id))

def c43446 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43446 : Upper (D 7) (R 7) [36,320,10,48] 13 := by
  apply FastRouting.sound _ _ [36,320,10,48] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43446 c43446
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39358
  · exact u39359
  · exact u39360
  · exact u39361
  · exact u39362
  · exact u39363

def r43447 : Route 9 := (fun mask => (mask,id))

def c43447 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43447 : Upper (D 7) (R 7) [36,320,10,65] 13 := by
  apply FastRouting.sound _ _ [36,320,10,65] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43447 c43447
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39364
  · exact u39365
  · exact u39366
  · exact u39367
  · exact u39368
  · exact u39369

def b43448 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 37 322 14 74 177 177 241 177 433), lower := (rows 37 322 14 74 16 32 64 128 256), losses := [] }

theorem u43448 : Upper (D 7) (R 7) [36,320,10,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43449 : Route 9 := (fun mask => (mask,id))

def c43449 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43449 : Upper (D 7) (R 7) [36,320,10,80] 13 := by
  apply FastRouting.sound _ _ [36,320,10,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43449 c43449
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39370
  · exact u39371
  · exact u39372
  · exact u39373
  · exact u39374
  · exact u39375

def b43450 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 37 322 14 104 147 179 211 147 403), lower := (rows 37 322 14 104 16 32 64 128 256), losses := [] }

theorem u43450 : Upper (D 7) (R 7) [36,320,10,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43451 : Route 9 := (fun mask => (mask,id))

def c43451 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43451 : Upper (D 7) (R 7) [36,320,10,129] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43451 c43451
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39376
  · exact u39377
  · exact u39378
  · exact u39379
  · exact u39380
  · exact u39381
  · exact u39382
  · exact u39383
  · exact u39384
  · exact u39385

def b43452 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 322 14 138 241 241 241 241 497), lower := (rows 37 322 14 138 16 32 64 128 256), losses := [] }

theorem u43452 : Upper (D 7) (R 7) [36,320,10,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43453 : Route 9 := (fun mask => (mask,id))

def c43453 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43453 : Upper (D 7) (R 7) [36,320,10,144] 13 := by
  apply FastRouting.sound _ _ [36,320,10,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43453 c43453
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39386
  · exact u39387
  · exact u39388
  · exact u39389
  · exact u39390
  · exact u39391
  · exact u39392
  · exact u39393
  · exact u39394
  · exact u39395

def r43454 : Route 9 := (fun mask => (mask,id))

def c43454 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43454 : Upper (D 7) (R 7) [36,320,10,160] 13 := by
  apply FastRouting.sound _ _ [36,320,10,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43454 c43454
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39396
  · exact u39397
  · exact u39398
  · exact u39399
  · exact u39400
  · exact u39401

def r43455 : Route 9 := (fun mask => (mask,id))

def c43455 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43455 : Upper (D 7) (R 7) [36,320,10,192] 13 := by
  apply FastRouting.sound _ _ [36,320,10,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43455 c43455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39402
  · exact u39403
  · exact u39404
  · exact u39405
  · exact u39406
  · exact u39407

def r43456 : Route 9 := (fun mask => (mask,id))

def c43456 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43456 : Upper (D 7) (R 7) [36,320,24,3] 13 := by
  apply FastRouting.sound _ _ [36,320,24,3] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43456 c43456
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39408
  · exact u39409
  · exact u39410
  · exact u39411
  · exact u39412
  · exact u39413
  · exact u39414
  · exact u39415
  · exact u39416
  · exact u39417

def b43457 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 28 41 211 227 195 195 451), lower := (rows 37 322 28 41 16 32 64 128 256), losses := [] }

theorem u43457 : Upper (D 7) (R 7) [36,320,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43458_3 : Upper (D 7) (R 7) [36,320,24,34,3] 13 :=
  permutation_upper _ _ _ [36,320,24,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39410

def r43458 : Route 9 := (fun mask => (mask,id))

def c43458 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43458 : Upper (D 7) (R 7) [36,320,24,34] 13 := by
  apply FastRouting.sound _ _ [36,320,24,34] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43458 c43458
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43458_3
  · exact u39422
  · exact u39423
  · exact u39424
  · exact u39425
  · exact u39426

theorem m43459_3 : Upper (D 7) (R 7) [36,320,24,65,3] 13 :=
  permutation_upper _ _ _ [36,320,24,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39411

theorem m43459_33 : Upper (D 7) (R 7) [36,320,24,65,33] 13 :=
  permutation_upper _ _ _ [36,320,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39418

theorem m43459_34 : Upper (D 7) (R 7) [36,320,24,65,34] 13 :=
  permutation_upper _ _ _ [36,320,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39422

def r43459 : Route 9 := (fun mask => (mask,id))

def c43459 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43459 : Upper (D 7) (R 7) [36,320,24,65] 13 := by
  apply FastRouting.sound _ _ [36,320,24,65] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43459 c43459
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43459_3
  · exact m43459_33
  · exact m43459_34
  · exact u39427
  · exact u39428
  · exact u39429

def b43460 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 28 74 179 163 227 163 419), lower := (rows 37 322 28 74 16 32 64 128 256), losses := [] }

theorem u43460 : Upper (D 7) (R 7) [36,320,24,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43461_3 : Upper (D 7) (R 7) [36,320,24,96,3] 13 :=
  permutation_upper _ _ _ [36,320,24,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39413

def r43461 : Route 9 := (fun mask => (mask,id))

def c43461 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43461 : Upper (D 7) (R 7) [36,320,24,96] 13 := by
  apply FastRouting.sound _ _ [36,320,24,96] 13 (by decide) (choices 2) [3,129,130] r43461 c43461
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43461_3
  · exact u39433
  · exact u39434

theorem m43462_3 : Upper (D 7) (R 7) [36,320,24,129,3] 13 :=
  permutation_upper _ _ _ [36,320,24,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39414

theorem m43462_33 : Upper (D 7) (R 7) [36,320,24,129,33] 13 :=
  permutation_upper _ _ _ [36,320,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39419

theorem m43462_34 : Upper (D 7) (R 7) [36,320,24,129,34] 13 :=
  permutation_upper _ _ _ [36,320,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39424

theorem m43462_65 : Upper (D 7) (R 7) [36,320,24,129,65] 13 :=
  permutation_upper _ _ _ [36,320,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39427

theorem m43462_66 : Upper (D 7) (R 7) [36,320,24,129,66] 13 :=
  permutation_upper _ _ _ [36,320,24,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39430

theorem m43462_96 : Upper (D 7) (R 7) [36,320,24,129,96] 13 :=
  permutation_upper _ _ _ [36,320,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39433

def r43462 : Route 9 := (fun mask => (mask,id))

def c43462 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43462 : Upper (D 7) (R 7) [36,320,24,129] 13 := by
  apply FastRouting.sound _ _ [36,320,24,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43462 c43462
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43462_3
  · exact m43462_33
  · exact m43462_34
  · exact m43462_65
  · exact m43462_66
  · exact m43462_96
  · exact u39435
  · exact u39436
  · exact u39437
  · exact u39438

theorem m43463_3 : Upper (D 7) (R 7) [36,320,24,130,3] 13 :=
  permutation_upper _ _ _ [36,320,24,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39415

theorem m43463_33 : Upper (D 7) (R 7) [36,320,24,130,33] 13 :=
  permutation_upper _ _ _ [36,320,24,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39420

theorem m43463_34 : Upper (D 7) (R 7) [36,320,24,130,34] 13 :=
  permutation_upper _ _ _ [36,320,24,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39425

theorem m43463_65 : Upper (D 7) (R 7) [36,320,24,130,65] 13 :=
  permutation_upper _ _ _ [36,320,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39428

theorem m43463_66 : Upper (D 7) (R 7) [36,320,24,130,66] 13 :=
  permutation_upper _ _ _ [36,320,24,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39431

theorem m43463_96 : Upper (D 7) (R 7) [36,320,24,130,96] 13 :=
  permutation_upper _ _ _ [36,320,24,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39434

theorem m43463_129 : Upper (D 7) (R 7) [36,320,24,130,129] 13 :=
  permutation_upper _ _ _ [36,320,24,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39436

def r43463 : Route 9 := (fun mask => (mask,id))

def c43463 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43463 : Upper (D 7) (R 7) [36,320,24,130] 13 := by
  apply FastRouting.sound _ _ [36,320,24,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43463 c43463
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43463_3
  · exact m43463_33
  · exact m43463_34
  · exact m43463_65
  · exact m43463_66
  · exact m43463_96
  · exact m43463_129
  · exact u39439
  · exact u39440
  · exact u39441

theorem m43464_3 : Upper (D 7) (R 7) [36,320,24,160,3] 13 :=
  permutation_upper _ _ _ [36,320,24,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39416

theorem m43464_65 : Upper (D 7) (R 7) [36,320,24,160,65] 13 :=
  permutation_upper _ _ _ [36,320,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39429

theorem m43464_66 : Upper (D 7) (R 7) [36,320,24,160,66] 13 :=
  permutation_upper _ _ _ [36,320,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39432

theorem m43464_129 : Upper (D 7) (R 7) [36,320,24,160,129] 13 :=
  permutation_upper _ _ _ [36,320,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39437

theorem m43464_130 : Upper (D 7) (R 7) [36,320,24,160,130] 13 :=
  permutation_upper _ _ _ [36,320,24,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39440

def r43464 : Route 9 := (fun mask => (mask,id))

def c43464 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43464 : Upper (D 7) (R 7) [36,320,24,160] 13 := by
  apply FastRouting.sound _ _ [36,320,24,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43464 c43464
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43464_3
  · exact m43464_65
  · exact m43464_66
  · exact m43464_129
  · exact m43464_130
  · exact u39442

theorem m43465_3 : Upper (D 7) (R 7) [36,320,24,192,3] 13 :=
  permutation_upper _ _ _ [36,320,24,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39417

theorem m43465_33 : Upper (D 7) (R 7) [36,320,24,192,33] 13 :=
  permutation_upper _ _ _ [36,320,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39421

theorem m43465_34 : Upper (D 7) (R 7) [36,320,24,192,34] 13 :=
  permutation_upper _ _ _ [36,320,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39426

theorem m43465_129 : Upper (D 7) (R 7) [36,320,24,192,129] 13 :=
  permutation_upper _ _ _ [36,320,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39438

theorem m43465_130 : Upper (D 7) (R 7) [36,320,24,192,130] 13 :=
  permutation_upper _ _ _ [36,320,24,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39441

theorem m43465_160 : Upper (D 7) (R 7) [36,320,24,192,160] 13 :=
  permutation_upper _ _ _ [36,320,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39442

def r43465 : Route 9 := (fun mask => (mask,id))

def c43465 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43465 : Upper (D 7) (R 7) [36,320,24,192] 13 := by
  apply FastRouting.sound _ _ [36,320,24,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43465 c43465
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43465_3
  · exact m43465_33
  · exact m43465_34
  · exact m43465_129
  · exact m43465_130
  · exact m43465_160

def r43466 : Route 9 := (fun mask => (mask,id))

def c43466 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43466 : Upper (D 7) (R 7) [36,320,65,3] 13 := by
  apply FastRouting.sound _ _ [36,320,65,3] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43466 c43466
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39443
  · exact u39444
  · exact u39445
  · exact u39446
  · exact u39447
  · exact u39448

def r43467 : Route 9 := (fun mask => (mask,id))

def c43467 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43467 : Upper (D 7) (R 7) [36,320,65,17] 13 := by
  apply FastRouting.sound _ _ [36,320,65,17] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43467 c43467
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39449
  · exact u39450
  · exact u39451
  · exact u39452
  · exact u39453
  · exact u39454

theorem m43468_3 : Upper (D 7) (R 7) [36,320,65,18,3] 13 :=
  permutation_upper _ _ _ [36,320,65,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39443

theorem m43468_9 : Upper (D 7) (R 7) [36,320,65,18,9] 13 :=
  permutation_upper _ _ _ [36,320,65,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39449

def r43468 : Route 9 := (fun mask => (mask,id))

def c43468 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43468 : Upper (D 7) (R 7) [36,320,65,18] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43468 c43468
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43468_3
  · exact m43468_9
  · exact u39455
  · exact u39456
  · exact u39457
  · exact u39458
  · exact u39459
  · exact u39460
  · exact u39461
  · exact u39462

def b43469 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 69 41 154 186 218 154 410), lower := (rows 37 322 69 41 16 32 64 128 256), losses := [] }

theorem u43469 : Upper (D 7) (R 7) [36,320,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43470_3 : Upper (D 7) (R 7) [36,320,65,34,3] 13 :=
  permutation_upper _ _ _ [36,320,65,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39444

theorem m43470_9 : Upper (D 7) (R 7) [36,320,65,34,9] 13 :=
  permutation_upper _ _ _ [36,320,65,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39450

theorem m43470_10 : Upper (D 7) (R 7) [36,320,65,34,10] 13 :=
  permutation_upper _ _ _ [36,320,65,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39457

def r43470 : Route 9 := (fun mask => (mask,id))

def c43470 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43470 : Upper (D 7) (R 7) [36,320,65,34] 13 := by
  apply FastRouting.sound _ _ [36,320,65,34] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43470 c43470
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43470_3
  · exact m43470_9
  · exact m43470_10
  · exact u39465
  · exact u39466
  · exact u39467

theorem m43471_3 : Upper (D 7) (R 7) [36,320,65,48,3] 13 :=
  permutation_upper _ _ _ [36,320,65,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39445

theorem m43471_9 : Upper (D 7) (R 7) [36,320,65,48,9] 13 :=
  permutation_upper _ _ _ [36,320,65,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39451

theorem m43471_10 : Upper (D 7) (R 7) [36,320,65,48,10] 13 :=
  permutation_upper _ _ _ [36,320,65,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39458

def r43471 : Route 9 := (fun mask => (mask,id))

def c43471 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43471 : Upper (D 7) (R 7) [36,320,65,48] 13 := by
  apply FastRouting.sound _ _ [36,320,65,48] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43471 c43471
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43471_3
  · exact m43471_9
  · exact m43471_10
  · exact u39468
  · exact u39469
  · exact u39470

theorem m43472_10 : Upper (D 7) (R 7) [36,320,65,129,10] 13 :=
  permutation_upper _ _ _ [36,320,65,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39459

theorem m43472_34 : Upper (D 7) (R 7) [36,320,65,129,34] 13 :=
  permutation_upper _ _ _ [36,320,65,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39465

theorem m43472_40 : Upper (D 7) (R 7) [36,320,65,129,40] 13 :=
  permutation_upper _ _ _ [36,320,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39468

def r43472 : Route 9 := (fun mask => (mask,id))

def c43472 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43472 : Upper (D 7) (R 7) [36,320,65,129] 13 := by
  apply FastRouting.sound _ _ [36,320,65,129] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43472 c43472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43472_10
  · exact m43472_34
  · exact m43472_40
  · exact u39471
  · exact u39472
  · exact u39473

theorem m43473_3 : Upper (D 7) (R 7) [36,320,65,130,3] 13 :=
  permutation_upper _ _ _ [36,320,65,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39446

theorem m43473_9 : Upper (D 7) (R 7) [36,320,65,130,9] 13 :=
  permutation_upper _ _ _ [36,320,65,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39452

theorem m43473_10 : Upper (D 7) (R 7) [36,320,65,130,10] 13 :=
  permutation_upper _ _ _ [36,320,65,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39460

theorem m43473_33 : Upper (D 7) (R 7) [36,320,65,130,33] 13 :=
  permutation_upper _ _ _ [36,320,65,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39463

theorem m43473_34 : Upper (D 7) (R 7) [36,320,65,130,34] 13 :=
  permutation_upper _ _ _ [36,320,65,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39466

theorem m43473_40 : Upper (D 7) (R 7) [36,320,65,130,40] 13 :=
  permutation_upper _ _ _ [36,320,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39469

theorem m43473_129 : Upper (D 7) (R 7) [36,320,65,130,129] 13 :=
  permutation_upper _ _ _ [36,320,65,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39471

def r43473 : Route 9 := (fun mask => (mask,id))

def c43473 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43473 : Upper (D 7) (R 7) [36,320,65,130] 13 := by
  apply FastRouting.sound _ _ [36,320,65,130] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43473 c43473
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43473_3
  · exact m43473_9
  · exact m43473_10
  · exact m43473_33
  · exact m43473_34
  · exact m43473_40
  · exact m43473_129
  · exact u39474
  · exact u39475
  · exact u39476

theorem m43474_3 : Upper (D 7) (R 7) [36,320,65,144,3] 13 :=
  permutation_upper _ _ _ [36,320,65,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39447

theorem m43474_9 : Upper (D 7) (R 7) [36,320,65,144,9] 13 :=
  permutation_upper _ _ _ [36,320,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39453

theorem m43474_10 : Upper (D 7) (R 7) [36,320,65,144,10] 13 :=
  permutation_upper _ _ _ [36,320,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39461

theorem m43474_33 : Upper (D 7) (R 7) [36,320,65,144,33] 13 :=
  permutation_upper _ _ _ [36,320,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39464

theorem m43474_34 : Upper (D 7) (R 7) [36,320,65,144,34] 13 :=
  permutation_upper _ _ _ [36,320,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39467

theorem m43474_40 : Upper (D 7) (R 7) [36,320,65,144,40] 13 :=
  permutation_upper _ _ _ [36,320,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39470

theorem m43474_129 : Upper (D 7) (R 7) [36,320,65,144,129] 13 :=
  permutation_upper _ _ _ [36,320,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39472

theorem m43474_130 : Upper (D 7) (R 7) [36,320,65,144,130] 13 :=
  permutation_upper _ _ _ [36,320,65,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39475

def r43474 : Route 9 := (fun mask => (mask,id))

def c43474 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43474 : Upper (D 7) (R 7) [36,320,65,144] 13 := by
  apply FastRouting.sound _ _ [36,320,65,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43474 c43474
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43474_3
  · exact m43474_9
  · exact m43474_10
  · exact m43474_33
  · exact m43474_34
  · exact m43474_40
  · exact m43474_129
  · exact m43474_130
  · exact u39477
  · exact u39478

theorem m43475_3 : Upper (D 7) (R 7) [36,320,65,160,3] 13 :=
  permutation_upper _ _ _ [36,320,65,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39448

theorem m43475_9 : Upper (D 7) (R 7) [36,320,65,160,9] 13 :=
  permutation_upper _ _ _ [36,320,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39454

theorem m43475_10 : Upper (D 7) (R 7) [36,320,65,160,10] 13 :=
  permutation_upper _ _ _ [36,320,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39462

theorem m43475_129 : Upper (D 7) (R 7) [36,320,65,160,129] 13 :=
  permutation_upper _ _ _ [36,320,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39473

theorem m43475_130 : Upper (D 7) (R 7) [36,320,65,160,130] 13 :=
  permutation_upper _ _ _ [36,320,65,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39476

theorem m43475_136 : Upper (D 7) (R 7) [36,320,65,160,136] 13 :=
  permutation_upper _ _ _ [36,320,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39478

def r43475 : Route 9 := (fun mask => (mask,id))

def c43475 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43475 : Upper (D 7) (R 7) [36,320,65,160] 13 := by
  apply FastRouting.sound _ _ [36,320,65,160] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43475 c43475
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43475_3
  · exact m43475_9
  · exact m43475_10
  · exact m43475_129
  · exact m43475_130
  · exact m43475_136

def r43476 : Route 9 := (fun mask => (mask,id))

def c43476 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43476 : Upper (D 7) (R 7) [36,320,72,3] 13 := by
  apply FastRouting.sound _ _ [36,320,72,3] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43476 c43476
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39479
  · exact u39480
  · exact u39481
  · exact u39482
  · exact u39483
  · exact u39484

def r43477 : Route 9 := (fun mask => (mask,id))

def c43477 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43477 : Upper (D 7) (R 7) [36,320,72,17] 13 := by
  apply FastRouting.sound _ _ [36,320,72,17] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43477 c43477
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39485
  · exact u39486
  · exact u39487
  · exact u39488
  · exact u39489
  · exact u39490

def r43478 : Route 9 := (fun mask => (mask,id))

def c43478 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43478 : Upper (D 7) (R 7) [36,320,72,18] 13 := by
  apply FastRouting.sound _ _ [36,320,72,18] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43478 c43478
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39491
  · exact u39492
  · exact u39493
  · exact u39494
  · exact u39495
  · exact u39496

def b43479 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 76 41 147 179 211 147 403), lower := (rows 37 322 76 41 16 32 64 128 256), losses := [] }

theorem u43479 : Upper (D 7) (R 7) [36,320,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43480 : Route 9 := (fun mask => (mask,id))

def c43480 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43480 : Upper (D 7) (R 7) [36,320,72,34] 13 := by
  apply FastRouting.sound _ _ [36,320,72,34] 13 (by decide) (choices 2) [3,129,130] r43480 c43480
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39497
  · exact u39498
  · exact u39499

def r43481 : Route 9 := (fun mask => (mask,id))

def c43481 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43481 : Upper (D 7) (R 7) [36,320,72,48] 13 := by
  apply FastRouting.sound _ _ [36,320,72,48] 13 (by decide) (choices 2) [3,129,130] r43481 c43481
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39500
  · exact u39501
  · exact u39502

def r43482 : Route 9 := (fun mask => (mask,id))

def c43482 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43482 : Upper (D 7) (R 7) [36,320,72,129] 13 := by
  apply FastRouting.sound _ _ [36,320,72,129] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43482 c43482
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39503
  · exact u39504
  · exact u39505
  · exact u39506
  · exact u39507
  · exact u39508

def r43483 : Route 9 := (fun mask => (mask,id))

def c43483 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43483 : Upper (D 7) (R 7) [36,320,72,130] 13 := by
  apply FastRouting.sound _ _ [36,320,72,130] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43483 c43483
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39509
  · exact u39510
  · exact u39511
  · exact u39512
  · exact u39513
  · exact u39514

def r43484 : Route 9 := (fun mask => (mask,id))

def c43484 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43484 : Upper (D 7) (R 7) [36,320,72,144] 13 := by
  apply FastRouting.sound _ _ [36,320,72,144] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43484 c43484
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39515
  · exact u39516
  · exact u39517
  · exact u39518
  · exact u39519
  · exact u39520

def r43485 : Route 9 := (fun mask => (mask,id))

def c43485 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43485 : Upper (D 7) (R 7) [36,320,72,160] 13 := by
  apply FastRouting.sound _ _ [36,320,72,160] 13 (by decide) (choices 2) [3,129,130] r43485 c43485
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39521
  · exact u39522
  · exact u39523

def r43486 : Route 9 := (fun mask => (mask,id))

def c43486 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43486 : Upper (D 7) (R 7) [36,320,129,3] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r43486 c43486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39524
  · exact u39525
  · exact u39526
  · exact u39527
  · exact u39528
  · exact u39529
  · exact u39530
  · exact u39531
  · exact u39532
  · exact u39533

def r43487 : Route 9 := (fun mask => (mask,id))

def c43487 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43487 : Upper (D 7) (R 7) [36,320,129,17] 13 := by
  apply FastRouting.sound _ _ [36,320,129,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r43487 c43487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39534
  · exact u39535
  · exact u39536
  · exact u39537
  · exact u39538
  · exact u39539
  · exact u39540
  · exact u39541
  · exact u39542
  · exact u39543

theorem m43488_3 : Upper (D 7) (R 7) [36,320,129,18,3] 13 :=
  permutation_upper _ _ _ [36,320,129,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39524

theorem m43488_9 : Upper (D 7) (R 7) [36,320,129,18,9] 13 :=
  permutation_upper _ _ _ [36,320,129,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39534

def r43488 : Route 9 := (fun mask => (mask,id))

def c43488 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43488 : Upper (D 7) (R 7) [36,320,129,18] 13 := by
  apply FastRouting.sound _ _ [36,320,129,18] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r43488 c43488
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43488_3
  · exact m43488_9
  · exact u39544
  · exact u39545
  · exact u39546
  · exact u39547
  · exact u39548
  · exact u39549
  · exact u39550
  · exact u39551
  · exact u39552
  · exact u39553
  · exact u39554
  · exact u39555
  · exact u39556

def b43489 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 133 41 218 250 218 218 474), lower := (rows 37 322 133 41 16 32 64 128 256), losses := [] }

theorem u43489 : Upper (D 7) (R 7) [36,320,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43490_3 : Upper (D 7) (R 7) [36,320,129,34,3] 13 :=
  permutation_upper _ _ _ [36,320,129,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39525

theorem m43490_9 : Upper (D 7) (R 7) [36,320,129,34,9] 13 :=
  permutation_upper _ _ _ [36,320,129,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39535

theorem m43490_10 : Upper (D 7) (R 7) [36,320,129,34,10] 13 :=
  permutation_upper _ _ _ [36,320,129,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39546

def r43490 : Route 9 := (fun mask => (mask,id))

def c43490 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43490 : Upper (D 7) (R 7) [36,320,129,34] 13 := by
  apply FastRouting.sound _ _ [36,320,129,34] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43490 c43490
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43490_3
  · exact m43490_9
  · exact m43490_10
  · exact u39561
  · exact u39562
  · exact u39563
  · exact u39564
  · exact u39565
  · exact u39566
  · exact u39567

theorem m43491_3 : Upper (D 7) (R 7) [36,320,129,48,3] 13 :=
  permutation_upper _ _ _ [36,320,129,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39526

theorem m43491_9 : Upper (D 7) (R 7) [36,320,129,48,9] 13 :=
  permutation_upper _ _ _ [36,320,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39536

theorem m43491_10 : Upper (D 7) (R 7) [36,320,129,48,10] 13 :=
  permutation_upper _ _ _ [36,320,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39547

def r43491 : Route 9 := (fun mask => (mask,id))

def c43491 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43491 : Upper (D 7) (R 7) [36,320,129,48] 13 := by
  apply FastRouting.sound _ _ [36,320,129,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43491 c43491
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43491_3
  · exact m43491_9
  · exact m43491_10
  · exact u39568
  · exact u39569
  · exact u39570
  · exact u39571
  · exact u39572
  · exact u39573
  · exact u39574

theorem m43492_10 : Upper (D 7) (R 7) [36,320,129,65,10] 13 :=
  permutation_upper _ _ _ [36,320,129,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39548

theorem m43492_34 : Upper (D 7) (R 7) [36,320,129,65,34] 13 :=
  permutation_upper _ _ _ [36,320,129,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39561

theorem m43492_40 : Upper (D 7) (R 7) [36,320,129,65,40] 13 :=
  permutation_upper _ _ _ [36,320,129,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39568

def r43492 : Route 9 := (fun mask => (mask,id))

def c43492 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43492 : Upper (D 7) (R 7) [36,320,129,65] 13 := by
  apply FastRouting.sound _ _ [36,320,129,65] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43492 c43492
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43492_10
  · exact m43492_34
  · exact m43492_40
  · exact u39575
  · exact u39576
  · exact u39577

def b43493 : PairBound 9 := { available := 187, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 133 74 187 187 251 187 443), lower := (rows 37 322 133 74 16 32 64 128 256), losses := [] }

theorem u43493 : Upper (D 7) (R 7) [36,320,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43494_3 : Upper (D 7) (R 7) [36,320,129,80,3] 13 :=
  permutation_upper _ _ _ [36,320,129,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39528

theorem m43494_9 : Upper (D 7) (R 7) [36,320,129,80,9] 13 :=
  permutation_upper _ _ _ [36,320,129,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39538

theorem m43494_10 : Upper (D 7) (R 7) [36,320,129,80,10] 13 :=
  permutation_upper _ _ _ [36,320,129,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39550

theorem m43494_33 : Upper (D 7) (R 7) [36,320,129,80,33] 13 :=
  permutation_upper _ _ _ [36,320,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39557

theorem m43494_34 : Upper (D 7) (R 7) [36,320,129,80,34] 13 :=
  permutation_upper _ _ _ [36,320,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39563

theorem m43494_40 : Upper (D 7) (R 7) [36,320,129,80,40] 13 :=
  permutation_upper _ _ _ [36,320,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39570

def r43494 : Route 9 := (fun mask => (mask,id))

def c43494 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43494 : Upper (D 7) (R 7) [36,320,129,80] 13 := by
  apply FastRouting.sound _ _ [36,320,129,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43494 c43494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43494_3
  · exact m43494_9
  · exact m43494_10
  · exact m43494_33
  · exact m43494_34
  · exact m43494_40
  · exact u39580
  · exact u39581
  · exact u39582
  · exact u39583

theorem m43495_3 : Upper (D 7) (R 7) [36,320,129,96,3] 13 :=
  permutation_upper _ _ _ [36,320,129,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39529

theorem m43495_9 : Upper (D 7) (R 7) [36,320,129,96,9] 13 :=
  permutation_upper _ _ _ [36,320,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39539

theorem m43495_10 : Upper (D 7) (R 7) [36,320,129,96,10] 13 :=
  permutation_upper _ _ _ [36,320,129,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39551

def r43495 : Route 9 := (fun mask => (mask,id))

def c43495 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43495 : Upper (D 7) (R 7) [36,320,129,96] 13 := by
  apply FastRouting.sound _ _ [36,320,129,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43495 c43495
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43495_3
  · exact m43495_9
  · exact m43495_10
  · exact u39584
  · exact u39585
  · exact u39586

def b43496 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 37 322 133 137 122 122 122 250 378), lower := (rows 37 322 133 137 16 32 64 128 256), losses := [] }

theorem u43496 : Upper (D 7) (R 7) [36,320,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43497_3 : Upper (D 7) (R 7) [36,320,129,130,3] 13 :=
  permutation_upper _ _ _ [36,320,129,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39530

theorem m43497_9 : Upper (D 7) (R 7) [36,320,129,130,9] 13 :=
  permutation_upper _ _ _ [36,320,129,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39540

theorem m43497_10 : Upper (D 7) (R 7) [36,320,129,130,10] 13 :=
  permutation_upper _ _ _ [36,320,129,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39553

theorem m43497_33 : Upper (D 7) (R 7) [36,320,129,130,33] 13 :=
  permutation_upper _ _ _ [36,320,129,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39558

theorem m43497_34 : Upper (D 7) (R 7) [36,320,129,130,34] 13 :=
  permutation_upper _ _ _ [36,320,129,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39565

theorem m43497_40 : Upper (D 7) (R 7) [36,320,129,130,40] 13 :=
  permutation_upper _ _ _ [36,320,129,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39572

theorem m43497_65 : Upper (D 7) (R 7) [36,320,129,130,65] 13 :=
  permutation_upper _ _ _ [36,320,129,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39575

theorem m43497_66 : Upper (D 7) (R 7) [36,320,129,130,66] 13 :=
  permutation_upper _ _ _ [36,320,129,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39578

theorem m43497_72 : Upper (D 7) (R 7) [36,320,129,130,72] 13 :=
  permutation_upper _ _ _ [36,320,129,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39581

theorem m43497_96 : Upper (D 7) (R 7) [36,320,129,130,96] 13 :=
  permutation_upper _ _ _ [36,320,129,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39585

def r43497 : Route 9 := (fun mask => (mask,id))

def c43497 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43497 : Upper (D 7) (R 7) [36,320,129,130] 13 := by
  apply FastRouting.sound _ _ [36,320,129,130] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r43497 c43497
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43497_3
  · exact m43497_9
  · exact m43497_10
  · exact m43497_33
  · exact m43497_34
  · exact m43497_40
  · exact m43497_65
  · exact m43497_66
  · exact m43497_72
  · exact m43497_96

theorem m43498_3 : Upper (D 7) (R 7) [36,320,129,144,3] 13 :=
  permutation_upper _ _ _ [36,320,129,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39531

theorem m43498_9 : Upper (D 7) (R 7) [36,320,129,144,9] 13 :=
  permutation_upper _ _ _ [36,320,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39541

theorem m43498_10 : Upper (D 7) (R 7) [36,320,129,144,10] 13 :=
  permutation_upper _ _ _ [36,320,129,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39554

theorem m43498_33 : Upper (D 7) (R 7) [36,320,129,144,33] 13 :=
  permutation_upper _ _ _ [36,320,129,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39559

theorem m43498_34 : Upper (D 7) (R 7) [36,320,129,144,34] 13 :=
  permutation_upper _ _ _ [36,320,129,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39566

theorem m43498_40 : Upper (D 7) (R 7) [36,320,129,144,40] 13 :=
  permutation_upper _ _ _ [36,320,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39573

theorem m43498_65 : Upper (D 7) (R 7) [36,320,129,144,65] 13 :=
  permutation_upper _ _ _ [36,320,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39576

theorem m43498_66 : Upper (D 7) (R 7) [36,320,129,144,66] 13 :=
  permutation_upper _ _ _ [36,320,129,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39579

theorem m43498_72 : Upper (D 7) (R 7) [36,320,129,144,72] 13 :=
  permutation_upper _ _ _ [36,320,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39582

theorem m43498_96 : Upper (D 7) (R 7) [36,320,129,144,96] 13 :=
  permutation_upper _ _ _ [36,320,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39586

def r43498 : Route 9 := (fun mask => (mask,id))

def c43498 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43498 : Upper (D 7) (R 7) [36,320,129,144] 13 := by
  apply FastRouting.sound _ _ [36,320,129,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r43498 c43498
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43498_3
  · exact m43498_9
  · exact m43498_10
  · exact m43498_33
  · exact m43498_34
  · exact m43498_40
  · exact m43498_65
  · exact m43498_66
  · exact m43498_72
  · exact m43498_96

def b43499 : PairBound 9 := { available := 91, camps := [{ cop := 3, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 168 91 123 91 219 347), lower := (rows 37 322 133 168 16 32 64 128 256), losses := [] }

theorem u43499 : Upper (D 7) (R 7) [36,320,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u43499
end Delivery.IrregularNine14.P07
