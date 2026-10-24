import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0205
import IrregularNine14P06C0206
import IrregularNine14P06C0207

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30660 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 11 35 100 137 22 372 340 468 340), lower := (rows 11 35 100 137 22 32 64 128 256), losses := [] }

theorem u30660 : Upper (D 6) (R 6) [10,33,96,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30661 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 100 137 82 308 340 404 276), lower := (rows 11 35 100 137 82 32 64 128 256), losses := [] }

theorem u30661 : Upper (D 6) (R 6) [10,33,96,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30662 : PairBound 9 := { available := 278, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 100 137 84 310 342 406 278), lower := (rows 11 35 100 137 84 32 64 128 256), losses := [] }

theorem u30662 : Upper (D 6) (R 6) [10,33,96,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30663 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 100 137 274 116 84 212 340), lower := (rows 11 35 100 137 274 32 64 128 256), losses := [] }

theorem u30663 : Upper (D 6) (R 6) [10,33,96,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30664 : Route 9 := (fun mask => (mask,id))

def c30664 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30664 : Upper (D 6) (R 6) [10,33,96,129,260] 13 := by
  apply FastRouting.sound _ _ [10,33,96,129,260] 13 (by decide) (choices 1) [2,4,16,64] r30664 c30664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12326
  · exact u12327
  · exact u12328
  · exact u12329

def r30665 : Route 9 := (fun mask => (mask,id))

def c30665 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30665 : Upper (D 6) (R 6) [10,33,96,129,320] 13 := by
  apply FastRouting.sound _ _ [10,33,96,129,320] 13 (by decide) (choices 1) [2,4,16] r30665 c30665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12330
  · exact u12331
  · exact u12332

def b30666 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 140 19 372 340 468 340), lower := (rows 11 35 100 140 19 32 64 128 256), losses := [] }

theorem u30666 : Upper (D 6) (R 6) [10,33,96,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30667 : Route 9 := (fun mask => (mask,id))

def c30667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30667 : Upper (D 6) (R 6) [10,33,96,132,5] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,5] 13 (by decide) (choices 1) [2,16,64,256] r30667 c30667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12333
  · exact u12334
  · exact u12335
  · exact u12336

def r30668 : Route 9 := (fun mask => (mask,id))

def c30668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30668 : Upper (D 6) (R 6) [10,33,96,132,6] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,6] 13 (by decide) (choices 1) [1,16,64,256] r30668 c30668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12337
  · exact u12338
  · exact u12339
  · exact u12340

def r30669 : Route 9 := (fun mask => (mask,id))

def c30669 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30669 : Upper (D 6) (R 6) [10,33,96,132,65] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,65] 13 (by decide) (choices 1) [2,4,16,256] r30669 c30669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12341
  · exact u12342
  · exact u12343
  · exact u12344

def r30670 : Route 9 := (fun mask => (mask,id))

def c30670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30670 : Upper (D 6) (R 6) [10,33,96,132,66] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,66] 13 (by decide) (choices 1) [1,4,16,256] r30670 c30670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12345
  · exact u12346
  · exact u12347
  · exact u12348

def b30671 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 100 140 84 307 339 403 275), lower := (rows 11 35 100 140 84 32 64 128 256), losses := [] }

theorem u30671 : Upper (D 6) (R 6) [10,33,96,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30672 : Route 9 := (fun mask => (mask,id))

def c30672 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30672 : Upper (D 6) (R 6) [10,33,96,132,257] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,257] 13 (by decide) (choices 1) [2,4,16,64] r30672 c30672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12349
  · exact u12350
  · exact u12351
  · exact u12352

def r30673 : Route 9 := (fun mask => (mask,id))

def c30673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30673 : Upper (D 6) (R 6) [10,33,96,132,258] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,258] 13 (by decide) (choices 1) [1,4,16,64] r30673 c30673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12353
  · exact u12354
  · exact u12355
  · exact u12356

def r30674 : Route 9 := (fun mask => (mask,id))

def c30674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30674 : Upper (D 6) (R 6) [10,33,96,132,260] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,260] 13 (by decide) (choices 1) [1,2,16,64] r30674 c30674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12357
  · exact u12358
  · exact u12359
  · exact u12360

def r30675 : Route 9 := (fun mask => (mask,id))

def c30675 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30675 : Upper (D 6) (R 6) [10,33,96,132,320] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,320] 13 (by decide) (choices 1) [1,2,4,16] r30675 c30675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12361
  · exact u12362
  · exact u12363
  · exact u12364

def b30676 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 152 19 356 324 452 324), lower := (rows 11 35 100 152 19 32 64 128 256), losses := [] }

theorem u30676 : Upper (D 6) (R 6) [10,33,96,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30677 : Route 9 := (fun mask => (mask,id))

def c30677 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30677 : Upper (D 6) (R 6) [10,33,96,144,5] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,5] 13 (by decide) (choices 1) [2,4,64,256] r30677 c30677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12365
  · exact u12366
  · exact u12367
  · exact u12368

def b30678 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 457, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 35 100 152 22 357 325 453 325), lower := (rows 11 35 100 152 22 32 64 128 256), losses := [] }

theorem u30678 : Upper (D 6) (R 6) [10,33,96,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30679 : Route 9 := (fun mask => (mask,id))

def c30679 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30679 : Upper (D 6) (R 6) [10,33,96,144,65] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,65] 13 (by decide) (choices 1) [2,4,256] r30679 c30679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12369
  · exact u12370
  · exact u12371

def r30680 : Route 9 := (fun mask => (mask,id))

def c30680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30680 : Upper (D 6) (R 6) [10,33,96,144,66] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,66] 13 (by decide) (choices 1) [1,4,256] r30680 c30680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12372
  · exact u12373
  · exact u12374

def b30681 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 100 152 84 295 327 391 263), lower := (rows 11 35 100 152 84 32 64 128 256), losses := [] }

theorem u30681 : Upper (D 6) (R 6) [10,33,96,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30682 : Route 9 := (fun mask => (mask,id))

def c30682 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30682 : Upper (D 6) (R 6) [10,33,96,144,257] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,257] 13 (by decide) (choices 1) [2,4,64] r30682 c30682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12375
  · exact u12376
  · exact u12377

def r30683 : Route 9 := (fun mask => (mask,id))

def c30683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30683 : Upper (D 6) (R 6) [10,33,96,144,258] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,258] 13 (by decide) (choices 1) [1,4,64] r30683 c30683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12378
  · exact u12379
  · exact u12380

def r30684 : Route 9 := (fun mask => (mask,id))

def c30684 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30684 : Upper (D 6) (R 6) [10,33,96,144,260] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,260] 13 (by decide) (choices 1) [1,2,4,64] r30684 c30684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12381
  · exact u12382
  · exact u12383
  · exact u12384

def r30685 : Route 9 := (fun mask => (mask,id))

def c30685 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30685 : Upper (D 6) (R 6) [10,33,96,144,320] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,320] 13 (by decide) (choices 1) [1,2,4] r30685 c30685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12385
  · exact u12386
  · exact u12387

def b30686 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 200 19 308 340 404 276), lower := (rows 11 35 100 200 19 32 64 128 256), losses := [] }

theorem u30686 : Upper (D 6) (R 6) [10,33,96,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30687 : Route 9 := (fun mask => (mask,id))

def c30687 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30687 : Upper (D 6) (R 6) [10,33,96,192,5] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,5] 13 (by decide) (choices 1) [2,4,16,256] r30687 c30687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12388
  · exact u12389
  · exact u12390
  · exact u12391

def r30688 : Route 9 := (fun mask => (mask,id))

def c30688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30688 : Upper (D 6) (R 6) [10,33,96,192,6] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,6] 13 (by decide) (choices 1) [1,4,16,256] r30688 c30688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12392
  · exact u12393
  · exact u12394
  · exact u12395

def r30689 : Route 9 := (fun mask => (mask,id))

def c30689 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30689 : Upper (D 6) (R 6) [10,33,96,192,257] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,257] 13 (by decide) (choices 1) [2,4,16] r30689 c30689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12396
  · exact u12397
  · exact u12398

def r30690 : Route 9 := (fun mask => (mask,id))

def c30690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30690 : Upper (D 6) (R 6) [10,33,96,192,258] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,258] 13 (by decide) (choices 1) [1,4,16] r30690 c30690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12399
  · exact u12400
  · exact u12401

def r30691 : Route 9 := (fun mask => (mask,id))

def c30691 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30691 : Upper (D 6) (R 6) [10,33,96,192,260] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,260] 13 (by decide) (choices 1) [1,2,4,16] r30691 c30691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12402
  · exact u12403
  · exact u12404
  · exact u12405

def b30692 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 392 19 116 84 212 340), lower := (rows 11 35 100 392 19 32 64 128 256), losses := [] }

theorem u30692 : Upper (D 6) (R 6) [10,33,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30693 : Route 9 := (fun mask => (mask,id))

def c30693 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30693 : Upper (D 6) (R 6) [10,33,96,384,5] 13 := by
  apply FastRouting.sound _ _ [10,33,96,384,5] 13 (by decide) (choices 1) [2,4,16,64] r30693 c30693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12406
  · exact u12407
  · exact u12408
  · exact u12409

def r30694 : Route 9 := (fun mask => (mask,id))

def c30694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30694 : Upper (D 6) (R 6) [10,33,96,384,6] 13 := by
  apply FastRouting.sound _ _ [10,33,96,384,6] 13 (by decide) (choices 1) [1,4,16,64] r30694 c30694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12410
  · exact u12411
  · exact u12412
  · exact u12413

def r30695 : Route 9 := (fun mask => (mask,id))

def c30695 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30695 : Upper (D 6) (R 6) [10,33,96,384,65] 13 := by
  apply FastRouting.sound _ _ [10,33,96,384,65] 13 (by decide) (choices 1) [2,4,16] r30695 c30695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12414
  · exact u12415
  · exact u12416

def r30696 : Route 9 := (fun mask => (mask,id))

def c30696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30696 : Upper (D 6) (R 6) [10,33,96,384,66] 13 := by
  apply FastRouting.sound _ _ [10,33,96,384,66] 13 (by decide) (choices 1) [1,4,16] r30696 c30696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12417
  · exact u12418
  · exact u12419

def b30697 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 100 392 84 55 87 151 279), lower := (rows 11 35 100 392 84 32 64 128 256), losses := [] }

theorem u30697 : Upper (D 6) (R 6) [10,33,96,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30698 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 133 28 22 352 352 480 352), lower := (rows 11 35 133 28 22 32 64 128 256), losses := [] }

theorem u30698 : Upper (D 6) (R 6) [10,33,129,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30699 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 133 28 50 356 324 452 324), lower := (rows 11 35 133 28 50 32 64 128 256), losses := [] }

theorem u30699 : Upper (D 6) (R 6) [10,33,129,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30700 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 133 28 52 354 322 450 322), lower := (rows 11 35 133 28 52 32 64 128 256), losses := [] }

theorem u30700 : Upper (D 6) (R 6) [10,33,129,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30701 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 35 133 28 82 356 356 484 356), lower := (rows 11 35 133 28 82 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 44 76 140 268), good := (rows 506 50 508 508 82 32 64 128 256) }] }

theorem u30701 : Upper (D 6) (R 6) [10,33,129,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30702 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 133 28 84 354 354 482 354), lower := (rows 11 35 133 28 84 32 64 128 256), losses := [] }

theorem u30702 : Upper (D 6) (R 6) [10,33,129,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30703 : Route 9 := (fun mask => (mask,id))

def c30703 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30703 : Upper (D 6) (R 6) [10,33,129,20,96] 13 := by
  apply FastRouting.sound _ _ [10,33,129,20,96] 13 (by decide) (choices 1) [2,4,64,256] r30703 c30703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12420
  · exact u12421
  · exact u12422
  · exact u12423

def b30704 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 35 133 28 274 100 100 228 356), lower := (rows 11 35 133 28 274 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 44 76 140 268), good := (rows 506 50 508 508 274 32 64 128 256) }] }

theorem u30704 : Upper (D 6) (R 6) [10,33,129,20,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30705 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 133 28 276 98 98 226 354), lower := (rows 11 35 133 28 276 32 64 128 256), losses := [] }

theorem u30705 : Upper (D 6) (R 6) [10,33,129,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30706 : Route 9 := (fun mask => (mask,id))

def c30706 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30706 : Upper (D 6) (R 6) [10,33,129,20,288] 13 := by
  apply FastRouting.sound _ _ [10,33,129,20,288] 13 (by decide) (choices 1) [2,4,64] r30706 c30706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12424
  · exact u12425
  · exact u12426

def r30707 : Route 9 := (fun mask => (mask,id))

def c30707 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30707 : Upper (D 6) (R 6) [10,33,129,20,320] 13 := by
  apply FastRouting.sound _ _ [10,33,129,20,320] 13 (by decide) (choices 1) [2,4,64] r30707 c30707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12427
  · exact u12428
  · exact u12429

def r30708 : Route 9 := (fun mask => (mask,id))

def c30708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30708 : Upper (D 6) (R 6) [10,33,129,68,6] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,6] 13 (by decide) (choices 1) [16,64,256] r30708 c30708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12430
  · exact u12431
  · exact u12432

def b30709 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 133 76 50 372 340 468 340), lower := (rows 11 35 133 76 50 32 64 128 256), losses := [] }

theorem u30709 : Upper (D 6) (R 6) [10,33,129,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30710 : Route 9 := (fun mask => (mask,id))

def c30710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30710 : Upper (D 6) (R 6) [10,33,129,68,36] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,36] 13 (by decide) (choices 1) [2,16,64,256] r30710 c30710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12433
  · exact u12434
  · exact u12435
  · exact u12436

def r30711 : Route 9 := (fun mask => (mask,id))

def c30711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30711 : Upper (D 6) (R 6) [10,33,129,68,66] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,66] 13 (by decide) (choices 1) [4,16,256] r30711 c30711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12437
  · exact u12438
  · exact u12439

def b30712 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 133 76 84 306 370 434 306), lower := (rows 11 35 133 76 84 32 64 128 256), losses := [] }

theorem u30712 : Upper (D 6) (R 6) [10,33,129,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30713 : Route 9 := (fun mask => (mask,id))

def c30713 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30713 : Upper (D 6) (R 6) [10,33,129,68,96] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,96] 13 (by decide) (choices 1) [2,4,16,256] r30713 c30713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12440
  · exact u12441
  · exact u12442
  · exact u12443

def r30714 : Route 9 := (fun mask => (mask,id))

def c30714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30714 : Upper (D 6) (R 6) [10,33,129,68,258] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,258] 13 (by decide) (choices 1) [4,16,64] r30714 c30714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12444
  · exact u12445
  · exact u12446

def r30715 : Route 9 := (fun mask => (mask,id))

def c30715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30715 : Upper (D 6) (R 6) [10,33,129,68,260] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,260] 13 (by decide) (choices 1) [2,16,64] r30715 c30715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12447
  · exact u12448
  · exact u12449

def r30716 : Route 9 := (fun mask => (mask,id))

def c30716 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30716 : Upper (D 6) (R 6) [10,33,129,68,288] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,288] 13 (by decide) (choices 1) [2,4,16,64] r30716 c30716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12450
  · exact u12451
  · exact u12452
  · exact u12453

def r30717 : Route 9 := (fun mask => (mask,id))

def c30717 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30717 : Upper (D 6) (R 6) [10,33,129,68,320] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68,320] 13 (by decide) (choices 1) [2,4,16] r30717 c30717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12454
  · exact u12455
  · exact u12456

def b30718 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 35 133 88 22 356 356 484 356), lower := (rows 11 35 133 88 22 32 64 128 256), losses := [] }

theorem u30718 : Upper (D 6) (R 6) [10,33,129,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30719 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 133 88 50 356 324 452 324), lower := (rows 11 35 133 88 50 32 64 128 256), losses := [] }

theorem u30719 : Upper (D 6) (R 6) [10,33,129,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30719
end Delivery.IrregularNine14.P06
