import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0373
import IrregularNine14P07C0374
import IrregularNine14P07C0375

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36660 : Route 9 := (fun mask => (mask,id))

def c36660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36660 : Upper (D 7) (R 7) [36,40,66,384,192] 13 := by
  apply FastRouting.sound _ _ [36,40,66,384,192] 13 (by decide) (choices 1) [1,2,16] r36660 c36660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22439
  · exact u22440
  · exact u22441

def r36661 : Route 9 := (fun mask => (mask,id))

def c36661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36661 : Upper (D 7) (R 7) [36,40,80,192,3] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,3] 13 (by decide) (choices 1) [1,2,128,256] r36661 c36661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22442
  · exact u22443
  · exact u22444
  · exact u22445

def r36662 : Route 9 := (fun mask => (mask,id))

def c36662 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36662 : Upper (D 7) (R 7) [36,40,80,192,129] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,129] 13 (by decide) (choices 1) [1,2,256] r36662 c36662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22446
  · exact u22447
  · exact u22448

def r36663 : Route 9 := (fun mask => (mask,id))

def c36663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36663 : Upper (D 7) (R 7) [36,40,80,192,130] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,130] 13 (by decide) (choices 1) [1,2,256] r36663 c36663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22449
  · exact u22450
  · exact u22451

def r36664 : Route 9 := (fun mask => (mask,id))

def c36664 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36664 : Upper (D 7) (R 7) [36,40,80,192,257] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,257] 13 (by decide) (choices 1) [1,2,128] r36664 c36664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22452
  · exact u22453
  · exact u22454

def r36665 : Route 9 := (fun mask => (mask,id))

def c36665 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36665 : Upper (D 7) (R 7) [36,40,80,192,258] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,258] 13 (by decide) (choices 1) [1,2,128] r36665 c36665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22455
  · exact u22456
  · exact u22457

def r36666 : Route 9 := (fun mask => (mask,id))

def c36666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36666 : Upper (D 7) (R 7) [36,40,80,192,384] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,384] 13 (by decide) (choices 1) [1,2] r36666 c36666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22458
  · exact u22459

def b36667 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 3, region := 226, targets := 1 },{ cop := 4, region := 196, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(3,5)], upper := (rows 37 42 84 265 19 226 194 194 450), lower := (rows 37 42 84 265 19 32 64 128 256), losses := [] }

theorem u36667 : Upper (D 7) (R 7) [36,40,80,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36668 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 265 81 162 194 130 386), lower := (rows 37 42 84 265 81 32 64 128 256), losses := [] }

theorem u36668 : Upper (D 7) (R 7) [36,40,80,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36669 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 265 82 163 195 131 387), lower := (rows 37 42 84 265 82 32 64 128 256), losses := [] }

theorem u36669 : Upper (D 7) (R 7) [36,40,80,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36670 : Route 9 := (fun mask => (mask,id))

def c36670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36670 : Upper (D 7) (R 7) [36,40,80,257,129] 13 := by
  apply FastRouting.sound _ _ [36,40,80,257,129] 13 (by decide) (choices 1) [2,64,128] r36670 c36670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22460
  · exact u22461
  · exact u22462

def r36671 : Route 9 := (fun mask => (mask,id))

def c36671 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36671 : Upper (D 7) (R 7) [36,40,80,257,130] 13 := by
  apply FastRouting.sound _ _ [36,40,80,257,130] 13 (by decide) (choices 1) [1,2,64,128] r36671 c36671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22463
  · exact u22464
  · exact u22465
  · exact u22466

def b36672 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 265 208 163 195 131 387), lower := (rows 37 42 84 265 208 32 64 128 256), losses := [] }

theorem u36672 : Upper (D 7) (R 7) [36,40,80,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36673 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 4, region := 460, targets := 32 }], pairs := [(0,1),(2,1),(2,5),(3,5)], upper := (rows 37 42 84 266 19 225 193 193 449), lower := (rows 37 42 84 266 19 32 64 128 256), losses := [] }

theorem u36673 : Upper (D 7) (R 7) [36,40,80,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36674 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 266 81 163 195 131 387), lower := (rows 37 42 84 266 81 32 64 128 256), losses := [] }

theorem u36674 : Upper (D 7) (R 7) [36,40,80,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36675 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 4, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 37 42 84 266 82 161 193 129 385), lower := (rows 37 42 84 266 82 32 64 128 256), losses := [] }

theorem u36675 : Upper (D 7) (R 7) [36,40,80,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36676 : Route 9 := (fun mask => (mask,id))

def c36676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36676 : Upper (D 7) (R 7) [36,40,80,258,129] 13 := by
  apply FastRouting.sound _ _ [36,40,80,258,129] 13 (by decide) (choices 1) [1,2,64,128] r36676 c36676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22467
  · exact u22468
  · exact u22469
  · exact u22470

def r36677 : Route 9 := (fun mask => (mask,id))

def c36677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36677 : Upper (D 7) (R 7) [36,40,80,258,130] 13 := by
  apply FastRouting.sound _ _ [36,40,80,258,130] 13 (by decide) (choices 1) [1,64,128] r36677 c36677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22471
  · exact u22472
  · exact u22473

def b36678 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 266 208 163 195 131 387), lower := (rows 37 42 84 266 208 32 64 128 256), losses := [] }

theorem u36678 : Upper (D 7) (R 7) [36,40,80,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36679 : Route 9 := (fun mask => (mask,id))

def c36679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36679 : Upper (D 7) (R 7) [36,40,80,320,3] 13 := by
  apply FastRouting.sound _ _ [36,40,80,320,3] 13 (by decide) (choices 1) [1,2,128] r36679 c36679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22474
  · exact u22475
  · exact u22476

def r36680 : Route 9 := (fun mask => (mask,id))

def c36680 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36680 : Upper (D 7) (R 7) [36,40,80,320,129] 13 := by
  apply FastRouting.sound _ _ [36,40,80,320,129] 13 (by decide) (choices 1) [1,2,128] r36680 c36680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22477
  · exact u22478
  · exact u22479

def r36681 : Route 9 := (fun mask => (mask,id))

def c36681 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36681 : Upper (D 7) (R 7) [36,40,80,320,130] 13 := by
  apply FastRouting.sound _ _ [36,40,80,320,130] 13 (by decide) (choices 1) [1,2,128] r36681 c36681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22480
  · exact u22481
  · exact u22482

def r36682 : Route 9 := (fun mask => (mask,id))

def c36682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36682 : Upper (D 7) (R 7) [36,40,80,384,3] 13 := by
  apply FastRouting.sound _ _ [36,40,80,384,3] 13 (by decide) (choices 1) [1,2,64,128] r36682 c36682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22483
  · exact u22484
  · exact u22485
  · exact u22486

def b36683 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 392 81 163 195 131 387), lower := (rows 37 42 84 392 81 32 64 128 256), losses := [] }

theorem u36683 : Upper (D 7) (R 7) [36,40,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36684 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 392 82 163 195 131 387), lower := (rows 37 42 84 392 82 32 64 128 256), losses := [] }

theorem u36684 : Upper (D 7) (R 7) [36,40,80,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36685 : Route 9 := (fun mask => (mask,id))

def c36685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36685 : Upper (D 7) (R 7) [36,40,80,384,129] 13 := by
  apply FastRouting.sound _ _ [36,40,80,384,129] 13 (by decide) (choices 1) [1,2,64] r36685 c36685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22487
  · exact u22488
  · exact u22489

def r36686 : Route 9 := (fun mask => (mask,id))

def c36686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36686 : Upper (D 7) (R 7) [36,40,80,384,130] 13 := by
  apply FastRouting.sound _ _ [36,40,80,384,130] 13 (by decide) (choices 1) [1,2,64] r36686 c36686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22490
  · exact u22491
  · exact u22492

def b36687 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 392 208 35 67 131 259), lower := (rows 37 42 84 392 208 32 64 128 256), losses := [] }

theorem u36687 : Upper (D 7) (R 7) [36,40,80,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36688 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c36688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u36688 : Upper (D 7) (R 7) [36,40,192,257,3] 13 := by
  apply FastRouting.sound _ _ [36,40,192,257,3] 13 (by decide) (choices 1) [2,16,64] r36688 c36688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22493
  · exact u22494
  · exact u22495

def r36689 : Route 9 := (fun mask => (mask,id))

def c36689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36689 : Upper (D 7) (R 7) [36,40,192,257,65] 13 := by
  apply FastRouting.sound _ _ [36,40,192,257,65] 13 (by decide) (choices 1) [2,16,128] r36689 c36689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22496
  · exact u22497
  · exact u22498

def r36690 : Route 9 := (fun mask => (mask,id))

def c36690 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36690 : Upper (D 7) (R 7) [36,40,192,257,66] 13 := by
  apply FastRouting.sound _ _ [36,40,192,257,66] 13 (by decide) (choices 1) [1,2,16,128] r36690 c36690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22499
  · exact u22500
  · exact u22501
  · exact u22502

def b36691 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 42 196 265 208 51 83 147 275), lower := (rows 37 42 196 265 208 32 64 128 256), losses := [] }

theorem u36691 : Upper (D 7) (R 7) [36,40,192,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36692 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 4, region := 460, targets := 32 }], pairs := [(0,1),(2,1),(2,5),(3,5)], upper := (rows 37 42 196 266 19 241 209 209 465), lower := (rows 37 42 196 266 19 32 64 128 256), losses := [] }

theorem u36692 : Upper (D 7) (R 7) [36,40,192,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36693 : Route 9 := (fun mask => (mask,id))

def c36693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36693 : Upper (D 7) (R 7) [36,40,192,258,65] 13 := by
  apply FastRouting.sound _ _ [36,40,192,258,65] 13 (by decide) (choices 1) [1,2,16,128] r36693 c36693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22503
  · exact u22504
  · exact u22505
  · exact u22506

def r36694 : Route 9 := (fun mask => (mask,id))

def c36694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36694 : Upper (D 7) (R 7) [36,40,192,258,66] 13 := by
  apply FastRouting.sound _ _ [36,40,192,258,66] 13 (by decide) (choices 1) [1,16,128] r36694 c36694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22507
  · exact u22508
  · exact u22509

def b36695 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 42 196 266 208 51 83 147 275), lower := (rows 37 42 196 266 208 32 64 128 256), losses := [] }

theorem u36695 : Upper (D 7) (R 7) [36,40,192,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36696 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c36696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36696 : Upper (D 7) (R 7) [36,40,192,272,3] 13 := by
  apply FastRouting.sound _ _ [36,40,192,272,3] 13 (by decide) (choices 1) [1,2,64] r36696 c36696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22510
  · exact u22511
  · exact u22512

def r36697 : Route 9 := (fun mask => (mask,id))

def c36697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36697 : Upper (D 7) (R 7) [36,40,192,272,65] 13 := by
  apply FastRouting.sound _ _ [36,40,192,272,65] 13 (by decide) (choices 1) [1,2,128] r36697 c36697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22513
  · exact u22514
  · exact u22515

def r36698 : Route 9 := (fun mask => (mask,id))

def c36698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36698 : Upper (D 7) (R 7) [36,40,192,272,66] 13 := by
  apply FastRouting.sound _ _ [36,40,192,272,66] 13 (by decide) (choices 1) [1,2,128] r36698 c36698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22516
  · exact u22517
  · exact u22518

def b36699 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 42 196 280 208 35 67 131 259), lower := (rows 37 42 196 280 208 32 64 128 256), losses := [] }

theorem u36699 : Upper (D 7) (R 7) [36,40,192,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36700 : Route 9 := (fun mask => (mask,id))

def c36700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36700 : Upper (D 7) (R 7) [36,40,192,320,3] 13 := by
  apply FastRouting.sound _ _ [36,40,192,320,3] 13 (by decide) (choices 1) [1,2,16,128] r36700 c36700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22519
  · exact u22520
  · exact u22521
  · exact u22522

def r36701 : Route 9 := (fun mask => (mask,id))

def c36701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36701 : Upper (D 7) (R 7) [36,40,192,320,129] 13 := by
  apply FastRouting.sound _ _ [36,40,192,320,129] 13 (by decide) (choices 1) [1,2,16] r36701 c36701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22523
  · exact u22524
  · exact u22525

def r36702 : Route 9 := (fun mask => (mask,id))

def c36702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36702 : Upper (D 7) (R 7) [36,40,192,320,130] 13 := by
  apply FastRouting.sound _ _ [36,40,192,320,130] 13 (by decide) (choices 1) [1,2,16] r36702 c36702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22526
  · exact u22527
  · exact u22528

def b36703 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 25 50 480 448 448 448), lower := (rows 37 74 7 25 50 32 64 128 256), losses := [] }

theorem u36703 : Upper (D 7) (R 7) [36,72,3,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36704 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 1, region := 16, targets := 32 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 37 74 7 25 82 416 480 416 416), lower := (rows 37 74 7 25 82 32 64 128 256), losses := [] }

theorem u36704 : Upper (D 7) (R 7) [36,72,3,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36705 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 25 112 418 450 386 386), lower := (rows 37 74 7 25 112 32 64 128 256), losses := [] }

theorem u36705 : Upper (D 7) (R 7) [36,72,3,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36706 : Route 9 := (fun mask => (mask,id))

def c36706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u36706 : Upper (D 7) (R 7) [36,72,3,17,130] 13 := by
  apply FastRouting.sound _ _ [36,72,3,17,130] 13 (by decide) (choices 1) [64,128,256] r36706 c36706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22529
  · exact u22530
  · exact u22531

def b36707 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 74 7 25 176 482 450 450 450), lower := (rows 37 74 7 25 176 32 64 128 256), losses := [] }

theorem u36707 : Upper (D 7) (R 7) [36,72,3,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36708 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 74 7 25 208 418 482 418 418), lower := (rows 37 74 7 25 208 32 64 128 256), losses := [] }

theorem u36708 : Upper (D 7) (R 7) [36,72,3,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36709 : Route 9 := (fun mask => (mask,id))

def c36709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36709 : Upper (D 7) (R 7) [36,72,3,17,258] 13 := by
  apply FastRouting.sound _ _ [36,72,3,17,258] 13 (by decide) (choices 1) [64,128] r36709 c36709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22532
  · exact u22533

def b36710 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 74 7 25 304 226 194 194 450), lower := (rows 37 74 7 25 304 32 64 128 256), losses := [] }

theorem u36710 : Upper (D 7) (R 7) [36,72,3,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36711 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 74 7 25 336 162 226 162 418), lower := (rows 37 74 7 25 336 32 64 128 256), losses := [] }

theorem u36711 : Upper (D 7) (R 7) [36,72,3,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36712 : Route 9 := (fun mask => (mask,id))

def c36712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36712 : Upper (D 7) (R 7) [36,72,3,17,384] 13 := by
  apply FastRouting.sound _ _ [36,72,3,17,384] 13 (by decide) (choices 1) [2,64,128] r36712 c36712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22534
  · exact u22535
  · exact u22536

def b36713 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 74 7 26 49 480 448 448 448), lower := (rows 37 74 7 26 49 32 64 128 256), losses := [] }

theorem u36713 : Upper (D 7) (R 7) [36,72,3,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36714 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 14, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 37 74 7 26 81 416 480 416 416), lower := (rows 37 74 7 26 81 32 64 128 256), losses := [] }

theorem u36714 : Upper (D 7) (R 7) [36,72,3,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36715 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 7 26 112 417 449 385 385), lower := (rows 37 74 7 26 112 32 64 128 256), losses := [] }

theorem u36715 : Upper (D 7) (R 7) [36,72,3,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36716 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 7 26 145 480 480 480 480), lower := (rows 37 74 7 26 145 32 64 128 256), losses := [] }

theorem u36716 : Upper (D 7) (R 7) [36,72,3,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36717 : Route 9 := (fun mask => (mask,id))

def c36717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u36717 : Upper (D 7) (R 7) [36,72,3,18,160] 13 := by
  apply FastRouting.sound _ _ [36,72,3,18,160] 13 (by decide) (choices 1) [1,64,128,256] r36717 c36717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22537
  · exact u22538
  · exact u22539
  · exact u22540

def b36718 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 10, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 7 26 208 417 481 417 417), lower := (rows 37 74 7 26 208 32 64 128 256), losses := [] }

theorem u36718 : Upper (D 7) (R 7) [36,72,3,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36719 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 7 26 273 224 224 224 480), lower := (rows 37 74 7 26 273 32 64 128 256), losses := [] }

theorem u36719 : Upper (D 7) (R 7) [36,72,3,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u36719
end Delivery.IrregularNine14.P07
