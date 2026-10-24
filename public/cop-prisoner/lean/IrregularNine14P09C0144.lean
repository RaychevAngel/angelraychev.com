import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0106
import IrregularNine14P09C0107
import IrregularNine14P09C0108

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8640 : Route 9 := (fun mask => (mask,id))

def c8640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8640 : Upper (D 9) (R 9) [96,36,129,144,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,258] 13 (by decide) (choices 1) [1,8,64,256] r8640 c8640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6388
  · exact u6389
  · exact u6390
  · exact u6391

def r8641 : Route 9 := (fun mask => (mask,id))

def c8641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8641 : Upper (D 9) (R 9) [96,36,129,144,264] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,264] 13 (by decide) (choices 1) [1,2,64,256] r8641 c8641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6392
  · exact u6393
  · exact u6394
  · exact u6395

def r8642 : Route 9 := (fun mask => (mask,id))

def c8642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8642 : Upper (D 9) (R 9) [96,36,129,144,320] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,320] 13 (by decide) (choices 1) [1,2,8,256] r8642 c8642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6396
  · exact u6397
  · exact u6398
  · exact u6399

def r8643 : Route 9 := (fun mask => (mask,id))

def c8643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8643 : Upper (D 9) (R 9) [96,36,129,192,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,257] 13 (by decide) (choices 1) [2,8,16,256] r8643 c8643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6400
  · exact u6401
  · exact u6402
  · exact u6403

def r8644 : Route 9 := (fun mask => (mask,id))

def c8644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8644 : Upper (D 9) (R 9) [96,36,129,192,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,258] 13 (by decide) (choices 1) [1,8,16,256] r8644 c8644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6404
  · exact u6405
  · exact u6406
  · exact u6407

def r8645 : Route 9 := (fun mask => (mask,id))

def c8645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8645 : Upper (D 9) (R 9) [96,36,129,192,264] 13 := by
  apply FastRouting.sound _ _ [96,36,129,192,264] 13 (by decide) (choices 1) [1,2,16,256] r8645 c8645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6408
  · exact u6409
  · exact u6410
  · exact u6411

def r8646 : Route 9 := (fun mask => (mask,id))

def c8646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u8646 : Upper (D 9) (R 9) [96,36,129,257,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,257,258] 13 (by decide) (choices 1) [8,16,64,128] r8646 c8646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6412
  · exact u6413
  · exact u6414
  · exact u6415

def b8647 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 97 38 133 265 280 242 210 210 466), lower := (rows 97 38 133 265 280 32 64 128 256), losses := [] }

theorem u8647 : Upper (D 9) (R 9) [96,36,129,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8647 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8648 : Route 9 := (fun mask => (mask,id))

def c8648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8648 : Upper (D 9) (R 9) [96,36,129,257,320] 13 := by
  apply FastRouting.sound _ _ [96,36,129,257,320] 13 (by decide) (choices 1) [2,8,16,128] r8648 c8648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6416
  · exact u6417
  · exact u6418
  · exact u6419

def r8649 : Route 9 := (fun mask => (mask,id))

def c8649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8649 : Upper (D 9) (R 9) [96,36,129,257,384] 13 := by
  apply FastRouting.sound _ _ [96,36,129,257,384] 13 (by decide) (choices 1) [2,8,16,64] r8649 c8649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6420
  · exact u6421
  · exact u6422
  · exact u6423

def b8650 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 97 38 133 266 280 241 209 209 465), lower := (rows 97 38 133 266 280 32 64 128 256), losses := [] }

theorem u8650 : Upper (D 9) (R 9) [96,36,129,258,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8650 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8651 : Route 9 := (fun mask => (mask,id))

def c8651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8651 : Upper (D 9) (R 9) [96,36,129,258,320] 13 := by
  apply FastRouting.sound _ _ [96,36,129,258,320] 13 (by decide) (choices 1) [1,8,16,128] r8651 c8651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6424
  · exact u6425
  · exact u6426
  · exact u6427

def r8652 : Route 9 := (fun mask => (mask,id))

def c8652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8652 : Upper (D 9) (R 9) [96,36,129,258,384] 13 := by
  apply FastRouting.sound _ _ [96,36,129,258,384] 13 (by decide) (choices 1) [1,8,16,64] r8652 c8652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6428
  · exact u6429
  · exact u6430
  · exact u6431

def b8653 : PairBound 9 := { available := 195, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 97 38 133 280 280 227 195 195 451), lower := (rows 97 38 133 280 280 32 64 128 256), losses := [] }

theorem u8653 : Upper (D 9) (R 9) [96,36,129,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8653 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8654 : PairBound 9 := { available := 139, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 38 133 280 336 171 203 139 395), lower := (rows 97 38 133 280 336 32 64 128 256), losses := [] }

theorem u8654 : Upper (D 9) (R 9) [96,36,129,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8654 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8655 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 38 133 280 400 107 75 203 331), lower := (rows 97 38 133 280 400 32 64 128 256), losses := [] }

theorem u8655 : Upper (D 9) (R 9) [96,36,129,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8655 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8656 : Route 9 := (fun mask => (mask,id))

def c8656 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8656 : Upper (D 9) (R 9) [96,36,129,320,384] 13 := by
  apply FastRouting.sound _ _ [96,36,129,320,384] 13 (by decide) (choices 1) [1,2,8,16] r8656 c8656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6432
  · exact u6433
  · exact u6434
  · exact u6435

def b8657 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 38 134 88 152 289 321 385 257), lower := (rows 97 38 134 88 152 32 64 128 256), losses := [] }

theorem u8657 : Upper (D 9) (R 9) [96,36,130,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8657 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8658 : Route 9 := (fun mask => (mask,id))

def c8658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8658 : Upper (D 9) (R 9) [96,36,130,80,264] 13 := by
  apply FastRouting.sound _ _ [96,36,130,80,264] 13 (by decide) (choices 1) [1,128,256] r8658 c8658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6436
  · exact u6437
  · exact u6438

def r8659 : Route 9 := (fun mask => (mask,id))

def c8659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8659 : Upper (D 9) (R 9) [96,36,130,80,384] 13 := by
  apply FastRouting.sound _ _ [96,36,130,80,384] 13 (by decide) (choices 1) [1,8,256] r8659 c8659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6439
  · exact u6440
  · exact u6441

def r8660 : Route 9 := (fun mask => (mask,id))

def c8660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u8660 : Upper (D 9) (R 9) [96,36,130,129,257] 13 := by
  apply FastRouting.sound _ _ [96,36,130,129,257] 13 (by decide) (choices 1) [8,16,64,256] r8660 c8660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6442
  · exact u6443
  · exact u6444
  · exact u6445

def r8661 : Route 9 := (fun mask => (mask,id))

def c8661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8661 : Upper (D 9) (R 9) [96,36,130,129,264] 13 := by
  apply FastRouting.sound _ _ [96,36,130,129,264] 13 (by decide) (choices 1) [1,16,64,256] r8661 c8661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6446
  · exact u6447
  · exact u6448
  · exact u6449

def r8662 : Route 9 := (fun mask => (mask,id))

def c8662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8662 : Upper (D 9) (R 9) [96,36,130,129,320] 13 := by
  apply FastRouting.sound _ _ [96,36,130,129,320] 13 (by decide) (choices 1) [1,8,16,256] r8662 c8662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6450
  · exact u6451
  · exact u6452
  · exact u6453

def r8663 : Route 9 := (fun mask => (mask,id))

def c8663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8663 : Upper (D 9) (R 9) [96,36,130,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,130,144,257] 13 (by decide) (choices 1) [1,8,64,256] r8663 c8663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6454
  · exact u6455
  · exact u6456
  · exact u6457

def b8664 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 152 280 353 321 449 321), lower := (rows 97 38 134 152 280 32 64 128 256), losses := [] }

theorem u8664 : Upper (D 9) (R 9) [96,36,130,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8664 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8665 : Route 9 := (fun mask => (mask,id))

def c8665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8665 : Upper (D 9) (R 9) [96,36,130,144,320] 13 := by
  apply FastRouting.sound _ _ [96,36,130,144,320] 13 (by decide) (choices 1) [1,8,256] r8665 c8665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6458
  · exact u6459
  · exact u6460

def r8666 : Route 9 := (fun mask => (mask,id))

def c8666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8666 : Upper (D 9) (R 9) [96,36,130,192,257] 13 := by
  apply FastRouting.sound _ _ [96,36,130,192,257] 13 (by decide) (choices 1) [1,8,16,256] r8666 c8666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6461
  · exact u6462
  · exact u6463
  · exact u6464

def r8667 : Route 9 := (fun mask => (mask,id))

def c8667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8667 : Upper (D 9) (R 9) [96,36,130,192,264] 13 := by
  apply FastRouting.sound _ _ [96,36,130,192,264] 13 (by decide) (choices 1) [1,16,256] r8667 c8667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6465
  · exact u6466
  · exact u6467

def b8668 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 16, targets := 192 },{ cop := 4, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 97 38 134 265 273 248 216 216 472), lower := (rows 97 38 134 265 273 32 64 128 256), losses := [] }

theorem u8668 : Upper (D 9) (R 9) [96,36,130,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8668 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8669 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 193 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(1,8),(4,0),(4,6),(4,7)], upper := (rows 97 38 134 265 280 241 209 209 465), lower := (rows 97 38 134 265 280 32 64 128 256), losses := [] }

theorem u8669 : Upper (D 9) (R 9) [96,36,130,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8669 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8670 : Route 9 := (fun mask => (mask,id))

def c8670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8670 : Upper (D 9) (R 9) [96,36,130,257,320] 13 := by
  apply FastRouting.sound _ _ [96,36,130,257,320] 13 (by decide) (choices 1) [1,8,16,128] r8670 c8670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6468
  · exact u6469
  · exact u6470
  · exact u6471

def r8671 : Route 9 := (fun mask => (mask,id))

def c8671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8671 : Upper (D 9) (R 9) [96,36,130,257,384] 13 := by
  apply FastRouting.sound _ _ [96,36,130,257,384] 13 (by decide) (choices 1) [1,8,16,64] r8671 c8671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6472
  · exact u6473
  · exact u6474
  · exact u6475

def b8672 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 97 38 134 280 280 225 193 193 449), lower := (rows 97 38 134 280 280 32 64 128 256), losses := [] }

theorem u8672 : Upper (D 9) (R 9) [96,36,130,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8672 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8673 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 225, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 38 134 280 336 169 201 137 393), lower := (rows 97 38 134 280 336 32 64 128 256), losses := [] }

theorem u8673 : Upper (D 9) (R 9) [96,36,130,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8673 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8674 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 231, targets := 256 },{ cop := 4, region := 8, targets := 33 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,5)], upper := (rows 97 38 134 280 400 105 73 201 329), lower := (rows 97 38 134 280 400 32 64 128 256), losses := [] }

theorem u8674 : Upper (D 9) (R 9) [96,36,130,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8674 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8675 : Route 9 := (fun mask => (mask,id))

def c8675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8675 : Upper (D 9) (R 9) [96,36,130,320,384] 13 := by
  apply FastRouting.sound _ _ [96,36,130,320,384] 13 (by decide) (choices 1) [1,8,16] r8675 c8675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6476
  · exact u6477
  · exact u6478

def r8676 : Route 9 := (fun mask => (mask,id))

def c8676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8676 : Upper (D 9) (R 9) [96,36,136,80,130] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,130] 13 (by decide) (choices 1) [1,256] r8676 c8676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6479
  · exact u6480

def r8677 : Route 9 := (fun mask => (mask,id))

def c8677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8677 : Upper (D 9) (R 9) [96,36,136,80,258] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,258] 13 (by decide) (choices 1) [1,128,256] r8677 c8677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6481
  · exact u6482
  · exact u6483

def r8678 : Route 9 := (fun mask => (mask,id))

def c8678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8678 : Upper (D 9) (R 9) [96,36,136,80,384] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,384] 13 (by decide) (choices 1) [1,2,256] r8678 c8678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6484
  · exact u6485
  · exact u6486

def b8679 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 137 273 370 338 466 338), lower := (rows 97 38 140 137 273 32 64 128 256), losses := [] }

theorem u8679 : Upper (D 9) (R 9) [96,36,136,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8679 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8680 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 137 274 369 337 465 337), lower := (rows 97 38 140 137 274 32 64 128 256), losses := [] }

theorem u8680 : Upper (D 9) (R 9) [96,36,136,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8680 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8681 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 137 336 307 339 403 275), lower := (rows 97 38 140 137 336 32 64 128 256), losses := [] }

theorem u8681 : Upper (D 9) (R 9) [96,36,136,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8681 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8682 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 138 273 369 337 465 337), lower := (rows 97 38 140 138 273 32 64 128 256), losses := [] }

theorem u8682 : Upper (D 9) (R 9) [96,36,136,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8682 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8683 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 138 336 305 337 401 273), lower := (rows 97 38 140 138 336 32 64 128 256), losses := [] }

theorem u8683 : Upper (D 9) (R 9) [96,36,136,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8683 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8684 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 152 273 355 323 451 323), lower := (rows 97 38 140 152 273 32 64 128 256), losses := [] }

theorem u8684 : Upper (D 9) (R 9) [96,36,136,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8684 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8685 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 152 274 353 321 449 321), lower := (rows 97 38 140 152 274 32 64 128 256), losses := [] }

theorem u8685 : Upper (D 9) (R 9) [96,36,136,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8685 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8686 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 152 336 291 323 387 259), lower := (rows 97 38 140 152 336 32 64 128 256), losses := [] }

theorem u8686 : Upper (D 9) (R 9) [96,36,136,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8686 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8687 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 200 273 307 339 403 275), lower := (rows 97 38 140 200 273 32 64 128 256), losses := [] }

theorem u8687 : Upper (D 9) (R 9) [96,36,136,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8687 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8688 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 200 274 305 337 401 273), lower := (rows 97 38 140 200 274 32 64 128 256), losses := [] }

theorem u8688 : Upper (D 9) (R 9) [96,36,136,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8688 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8689 : Route 9 := (fun mask => (mask,id))

def c8689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8689 : Upper (D 9) (R 9) [96,36,136,257,129] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,129] 13 (by decide) (choices 1) [2,16,64,256] r8689 c8689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6487
  · exact u6488
  · exact u6489
  · exact u6490

def r8690 : Route 9 := (fun mask => (mask,id))

def c8690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8690 : Upper (D 9) (R 9) [96,36,136,257,130] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,130] 13 (by decide) (choices 1) [1,16,64,256] r8690 c8690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6491
  · exact u6492
  · exact u6493
  · exact u6494

def r8691 : Route 9 := (fun mask => (mask,id))

def c8691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8691 : Upper (D 9) (R 9) [96,36,136,257,192] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,192] 13 (by decide) (choices 1) [1,2,16,256] r8691 c8691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6495
  · exact u6496
  · exact u6497
  · exact u6498

def b8692 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 97 38 140 265 273 242 210 210 466), lower := (rows 97 38 140 265 273 32 64 128 256), losses := [] }

theorem u8692 : Upper (D 9) (R 9) [96,36,136,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8692 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8693 : Route 9 := (fun mask => (mask,id))

def c8693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8693 : Upper (D 9) (R 9) [96,36,136,257,258] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,258] 13 (by decide) (choices 1) [1,16,64,128] r8693 c8693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6499
  · exact u6500
  · exact u6501
  · exact u6502

def r8694 : Route 9 := (fun mask => (mask,id))

def c8694 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8694 : Upper (D 9) (R 9) [96,36,136,257,320] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,320] 13 (by decide) (choices 1) [1,2,16,128] r8694 c8694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6503
  · exact u6504
  · exact u6505
  · exact u6506

def r8695 : Route 9 := (fun mask => (mask,id))

def c8695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8695 : Upper (D 9) (R 9) [96,36,136,257,384] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,384] 13 (by decide) (choices 1) [1,2,16,64] r8695 c8695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6507
  · exact u6508
  · exact u6509
  · exact u6510

def r8696 : Route 9 := (fun mask => (mask,id))

def c8696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8696 : Upper (D 9) (R 9) [96,36,136,258,129] 13 := by
  apply FastRouting.sound _ _ [96,36,136,258,129] 13 (by decide) (choices 1) [1,16,64,256] r8696 c8696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6511
  · exact u6512
  · exact u6513
  · exact u6514

def r8697 : Route 9 := (fun mask => (mask,id))

def c8697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8697 : Upper (D 9) (R 9) [96,36,136,258,192] 13 := by
  apply FastRouting.sound _ _ [96,36,136,258,192] 13 (by decide) (choices 1) [1,16,256] r8697 c8697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6515
  · exact u6516
  · exact u6517

def r8698 : Route 9 := (fun mask => (mask,id))

def c8698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8698 : Upper (D 9) (R 9) [96,36,136,258,257] 13 := by
  apply FastRouting.sound _ _ [96,36,136,258,257] 13 (by decide) (choices 1) [1,16,64,128] r8698 c8698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6518
  · exact u6519
  · exact u6520
  · exact u6521

def r8699 : Route 9 := (fun mask => (mask,id))

def c8699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8699 : Upper (D 9) (R 9) [96,36,136,258,320] 13 := by
  apply FastRouting.sound _ _ [96,36,136,258,320] 13 (by decide) (choices 1) [1,16,128] r8699 c8699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6522
  · exact u6523
  · exact u6524

#print axioms u8699
end Delivery.IrregularNine14.P09
