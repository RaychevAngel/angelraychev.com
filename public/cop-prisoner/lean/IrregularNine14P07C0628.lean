import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0407
import IrregularNine14P07C0408
import IrregularNine14P07C0409

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37680 : Route 9 := (fun mask => (mask,id))

def c37680 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37680 : Upper (D 7) (R 7) [36,96,192,130,257] 13 := by
  apply FastRouting.sound _ _ [36,96,192,130,257] 13 (by decide) (choices 1) [1,2,8,16] r37680 c37680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24462
  · exact u24463
  · exact u24464
  · exact u24465

def r37681 : Route 9 := (fun mask => (mask,id))

def c37681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37681 : Upper (D 7) (R 7) [36,96,192,130,258] 13 := by
  apply FastRouting.sound _ _ [36,96,192,130,258] 13 (by decide) (choices 1) [1,8,16] r37681 c37681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24466
  · exact u24467
  · exact u24468

def r37682 : Route 9 := (fun mask => (mask,id))

def c37682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37682 : Upper (D 7) (R 7) [36,96,192,130,264] 13 := by
  apply FastRouting.sound _ _ [36,96,192,130,264] 13 (by decide) (choices 1) [1,2,16] r37682 c37682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24469
  · exact u24470
  · exact u24471

def r37683 : Route 9 := (fun mask => (mask,id))

def c37683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37683 : Upper (D 7) (R 7) [36,96,192,144,257] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,257] 13 (by decide) (choices 1) [1,2,8] r37683 c37683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24472
  · exact u24473
  · exact u24474

def r37684 : Route 9 := (fun mask => (mask,id))

def c37684 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37684 : Upper (D 7) (R 7) [36,96,192,144,258] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,258] 13 (by decide) (choices 1) [1,2,8] r37684 c37684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24475
  · exact u24476
  · exact u24477

def r37685 : Route 9 := (fun mask => (mask,id))

def c37685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37685 : Upper (D 7) (R 7) [36,96,192,144,264] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,264] 13 (by decide) (choices 1) [1,2] r37685 c37685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24478
  · exact u24479

def b37686 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 261 11 26 240 208 208 464), lower := (rows 37 98 261 11 26 32 64 128 256), losses := [] }

theorem u37686 : Upper (D 7) (R 7) [36,96,257,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37687 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 261 11 88 178 210 146 402), lower := (rows 37 98 261 11 88 32 64 128 256), losses := [] }

theorem u37687 : Upper (D 7) (R 7) [36,96,257,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37688 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 261 11 146 248 216 216 472), lower := (rows 37 98 261 11 146 32 64 128 256), losses := [] }

theorem u37688 : Upper (D 7) (R 7) [36,96,257,3,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37689 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 261 11 152 242 210 210 466), lower := (rows 37 98 261 11 152 32 64 128 256), losses := [] }

theorem u37689 : Upper (D 7) (R 7) [36,96,257,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37690 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 261 11 208 186 218 154 410), lower := (rows 37 98 261 11 208 32 64 128 256), losses := [] }

theorem u37690 : Upper (D 7) (R 7) [36,96,257,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37691 : Route 9 := (fun mask => (mask,id))

def c37691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37691 : Upper (D 7) (R 7) [36,96,257,17,10] 13 := by
  apply FastRouting.sound _ _ [36,96,257,17,10] 13 (by decide) (choices 1) [2,64,128] r37691 c37691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24480
  · exact u24481
  · exact u24482

def b37692 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 261 25 82 170 202 138 394), lower := (rows 37 98 261 25 82 32 64 128 256), losses := [] }

theorem u37692 : Upper (D 7) (R 7) [36,96,257,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37693 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 98 261 25 88 162 194 130 386), lower := (rows 37 98 261 25 88 32 64 128 256), losses := [] }

theorem u37693 : Upper (D 7) (R 7) [36,96,257,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37694 : Route 9 := (fun mask => (mask,id))

def c37694 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37694 : Upper (D 7) (R 7) [36,96,257,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,257,17,130] 13 (by decide) (choices 1) [2,8,64,128] r37694 c37694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24483
  · exact u24484
  · exact u24485
  · exact u24486

def r37695 : Route 9 := (fun mask => (mask,id))

def c37695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37695 : Upper (D 7) (R 7) [36,96,257,17,136] 13 := by
  apply FastRouting.sound _ _ [36,96,257,17,136] 13 (by decide) (choices 1) [2,64,128] r37695 c37695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24487
  · exact u24488
  · exact u24489

def r37696 : Route 9 := (fun mask => (mask,id))

def c37696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37696 : Upper (D 7) (R 7) [36,96,257,17,192] 13 := by
  apply FastRouting.sound _ _ [36,96,257,17,192] 13 (by decide) (choices 1) [2,8,128] r37696 c37696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24490
  · exact u24491
  · exact u24492

def b37697 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 261 26 26 225 193 193 449), lower := (rows 37 98 261 26 26 32 64 128 256), losses := [] }

theorem u37697 : Upper (D 7) (R 7) [36,96,257,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37698 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 170, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 98 261 26 81 170 202 138 394), lower := (rows 37 98 261 26 81 32 64 128 256), losses := [] }

theorem u37698 : Upper (D 7) (R 7) [36,96,257,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37699 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 261 26 82 169 201 137 393), lower := (rows 37 98 261 26 82 32 64 128 256), losses := [] }

theorem u37699 : Upper (D 7) (R 7) [36,96,257,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37700 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 261 26 88 163 195 131 387), lower := (rows 37 98 261 26 88 32 64 128 256), losses := [] }

theorem u37700 : Upper (D 7) (R 7) [36,96,257,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37701 : Route 9 := (fun mask => (mask,id))

def c37701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37701 : Upper (D 7) (R 7) [36,96,257,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,257,18,129] 13 (by decide) (choices 1) [2,8,64,128] r37701 c37701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24493
  · exact u24494
  · exact u24495
  · exact u24496

def b37702 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 261 26 146 233 201 201 457), lower := (rows 37 98 261 26 146 32 64 128 256), losses := [] }

theorem u37702 : Upper (D 7) (R 7) [36,96,257,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37703 : Route 9 := (fun mask => (mask,id))

def c37703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37703 : Upper (D 7) (R 7) [36,96,257,18,136] 13 := by
  apply FastRouting.sound _ _ [36,96,257,18,136] 13 (by decide) (choices 1) [1,2,64,128] r37703 c37703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24497
  · exact u24498
  · exact u24499
  · exact u24500

def r37704 : Route 9 := (fun mask => (mask,id))

def c37704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37704 : Upper (D 7) (R 7) [36,96,257,18,192] 13 := by
  apply FastRouting.sound _ _ [36,96,257,18,192] 13 (by decide) (choices 1) [1,2,8,128] r37704 c37704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24501
  · exact u24502
  · exact u24503
  · exact u24504

def r37705 : Route 9 := (fun mask => (mask,id))

def c37705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37705 : Upper (D 7) (R 7) [36,96,257,65,130] 13 := by
  apply FastRouting.sound _ _ [36,96,257,65,130] 13 (by decide) (choices 1) [2,8,16,128] r37705 c37705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24505
  · exact u24506
  · exact u24507
  · exact u24508

def r37706 : Route 9 := (fun mask => (mask,id))

def c37706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37706 : Upper (D 7) (R 7) [36,96,257,65,136] 13 := by
  apply FastRouting.sound _ _ [36,96,257,65,136] 13 (by decide) (choices 1) [2,16,128] r37706 c37706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24509
  · exact u24510
  · exact u24511

def b37707 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 261 74 145 186 218 154 410), lower := (rows 37 98 261 74 145 32 64 128 256), losses := [] }

theorem u37707 : Upper (D 7) (R 7) [36,96,257,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37708 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 261 74 146 185 217 153 409), lower := (rows 37 98 261 74 146 32 64 128 256), losses := [] }

theorem u37708 : Upper (D 7) (R 7) [36,96,257,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37709 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 261 74 152 179 211 147 403), lower := (rows 37 98 261 74 152 32 64 128 256), losses := [] }

theorem u37709 : Upper (D 7) (R 7) [36,96,257,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37710 : Route 9 := (fun mask => (mask,id))

def c37710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37710 : Upper (D 7) (R 7) [36,96,257,80,129] 13 := by
  apply FastRouting.sound _ _ [36,96,257,80,129] 13 (by decide) (choices 1) [2,8,128] r37710 c37710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24512
  · exact u24513
  · exact u24514

def r37711 : Route 9 := (fun mask => (mask,id))

def c37711 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37711 : Upper (D 7) (R 7) [36,96,257,80,130] 13 := by
  apply FastRouting.sound _ _ [36,96,257,80,130] 13 (by decide) (choices 1) [1,2,8,128] r37711 c37711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24515
  · exact u24516
  · exact u24517
  · exact u24518

def r37712 : Route 9 := (fun mask => (mask,id))

def c37712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37712 : Upper (D 7) (R 7) [36,96,257,80,136] 13 := by
  apply FastRouting.sound _ _ [36,96,257,80,136] 13 (by decide) (choices 1) [1,2,128] r37712 c37712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24519
  · exact u24520
  · exact u24521

def r37713 : Route 9 := (fun mask => (mask,id))

def c37713 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37713 : Upper (D 7) (R 7) [36,96,257,129,130] 13 := by
  apply FastRouting.sound _ _ [36,96,257,129,130] 13 (by decide) (choices 1) [2,8,16,64] r37713 c37713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24522
  · exact u24523
  · exact u24524
  · exact u24525

def b37714 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(4,1),(4,5),(4,6)], upper := (rows 37 98 261 137 152 114 82 210 338), lower := (rows 37 98 261 137 152 32 64 128 256), losses := [] }

theorem u37714 : Upper (D 7) (R 7) [36,96,257,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37715 : Route 9 := (fun mask => (mask,id))

def c37715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37715 : Upper (D 7) (R 7) [36,96,257,129,192] 13 := by
  apply FastRouting.sound _ _ [36,96,257,129,192] 13 (by decide) (choices 1) [2,8,16] r37715 c37715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24526
  · exact u24527
  · exact u24528

def b37716 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 98 261 138 146 121 89 217 345), lower := (rows 37 98 261 138 146 32 64 128 256), losses := [] }

theorem u37716 : Upper (D 7) (R 7) [36,96,257,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37717 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 98 261 138 152 115 83 211 339), lower := (rows 37 98 261 138 152 32 64 128 256), losses := [] }

theorem u37717 : Upper (D 7) (R 7) [36,96,257,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37718 : Route 9 := (fun mask => (mask,id))

def c37718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37718 : Upper (D 7) (R 7) [36,96,257,130,192] 13 := by
  apply FastRouting.sound _ _ [36,96,257,130,192] 13 (by decide) (choices 1) [1,2,8,16] r37718 c37718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24529
  · exact u24530
  · exact u24531
  · exact u24532

def b37719 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 261 152 152 99 67 195 323), lower := (rows 37 98 261 152 152 32 64 128 256), losses := [] }

theorem u37719 : Upper (D 7) (R 7) [36,96,257,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37720 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 261 152 208 43 75 139 267), lower := (rows 37 98 261 152 208 32 64 128 256), losses := [] }

theorem u37720 : Upper (D 7) (R 7) [36,96,257,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37721 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 98 262 11 25 240 208 208 464), lower := (rows 37 98 262 11 25 32 64 128 256), losses := [] }

theorem u37721 : Upper (D 7) (R 7) [36,96,258,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37722 : Route 9 := (fun mask => (mask,id))

def c37722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37722 : Upper (D 7) (R 7) [36,96,258,3,65] 13 := by
  apply FastRouting.sound _ _ [36,96,258,3,65] 13 (by decide) (choices 1) [8,16,128] r37722 c37722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24533
  · exact u24534
  · exact u24535

def r37723 : Route 9 := (fun mask => (mask,id))

def c37723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37723 : Upper (D 7) (R 7) [36,96,258,3,72] 13 := by
  apply FastRouting.sound _ _ [36,96,258,3,72] 13 (by decide) (choices 1) [1,16,128] r37723 c37723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24536
  · exact u24537
  · exact u24538

def r37724 : Route 9 := (fun mask => (mask,id))

def c37724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u37724 : Upper (D 7) (R 7) [36,96,258,3,129] 13 := by
  apply FastRouting.sound _ _ [36,96,258,3,129] 13 (by decide) (choices 1) [8,16,64,128] r37724 c37724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24539
  · exact u24540
  · exact u24541
  · exact u24542

def r37725 : Route 9 := (fun mask => (mask,id))

def c37725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37725 : Upper (D 7) (R 7) [36,96,258,3,136] 13 := by
  apply FastRouting.sound _ _ [36,96,258,3,136] 13 (by decide) (choices 1) [1,16,64,128] r37725 c37725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24543
  · exact u24544
  · exact u24545
  · exact u24546

def r37726 : Route 9 := (fun mask => (mask,id))

def c37726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37726 : Upper (D 7) (R 7) [36,96,258,3,192] 13 := by
  apply FastRouting.sound _ _ [36,96,258,3,192] 13 (by decide) (choices 1) [1,8,16,128] r37726 c37726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24547
  · exact u24548
  · exact u24549
  · exact u24550

def b37727 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 262 25 25 226 194 194 450), lower := (rows 37 98 262 25 25 32 64 128 256), losses := [] }

theorem u37727 : Upper (D 7) (R 7) [36,96,258,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37728 : Route 9 := (fun mask => (mask,id))

def c37728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37728 : Upper (D 7) (R 7) [36,96,258,17,10] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,10] 13 (by decide) (choices 1) [1,64,128] r37728 c37728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24551
  · exact u24552
  · exact u24553

def b37729 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 262 25 81 170 202 138 394), lower := (rows 37 98 262 25 81 32 64 128 256), losses := [] }

theorem u37729 : Upper (D 7) (R 7) [36,96,258,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37730 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 262 25 82 169 201 137 393), lower := (rows 37 98 262 25 82 32 64 128 256), losses := [] }

theorem u37730 : Upper (D 7) (R 7) [36,96,258,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37731 : Route 9 := (fun mask => (mask,id))

def c37731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37731 : Upper (D 7) (R 7) [36,96,258,17,72] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,72] 13 (by decide) (choices 1) [1,2,128] r37731 c37731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24554
  · exact u24555
  · exact u24556

def b37732 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 262 25 145 234 202 202 458), lower := (rows 37 98 262 25 145 32 64 128 256), losses := [] }

theorem u37732 : Upper (D 7) (R 7) [36,96,258,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37733 : Route 9 := (fun mask => (mask,id))

def c37733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37733 : Upper (D 7) (R 7) [36,96,258,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,130] 13 (by decide) (choices 1) [1,8,64,128] r37733 c37733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24557
  · exact u24558
  · exact u24559
  · exact u24560

def r37734 : Route 9 := (fun mask => (mask,id))

def c37734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37734 : Upper (D 7) (R 7) [36,96,258,17,136] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,136] 13 (by decide) (choices 1) [1,2,64,128] r37734 c37734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24561
  · exact u24562
  · exact u24563
  · exact u24564

def r37735 : Route 9 := (fun mask => (mask,id))

def c37735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37735 : Upper (D 7) (R 7) [36,96,258,17,192] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,192] 13 (by decide) (choices 1) [1,2,8,128] r37735 c37735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24565
  · exact u24566
  · exact u24567
  · exact u24568

def r37736 : Route 9 := (fun mask => (mask,id))

def c37736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37736 : Upper (D 7) (R 7) [36,96,258,18,65] 13 := by
  apply FastRouting.sound _ _ [36,96,258,18,65] 13 (by decide) (choices 1) [1,8,128] r37736 c37736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24569
  · exact u24570
  · exact u24571

def b37737 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 262 26 88 161 193 129 385), lower := (rows 37 98 262 26 88 32 64 128 256), losses := [] }

theorem u37737 : Upper (D 7) (R 7) [36,96,258,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37738 : Route 9 := (fun mask => (mask,id))

def c37738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37738 : Upper (D 7) (R 7) [36,96,258,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,258,18,129] 13 (by decide) (choices 1) [1,8,64,128] r37738 c37738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24572
  · exact u24573
  · exact u24574
  · exact u24575

def r37739 : Route 9 := (fun mask => (mask,id))

def c37739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37739 : Upper (D 7) (R 7) [36,96,258,18,136] 13 := by
  apply FastRouting.sound _ _ [36,96,258,18,136] 13 (by decide) (choices 1) [1,64,128] r37739 c37739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24576
  · exact u24577
  · exact u24578

#print axioms u37739
end Delivery.IrregularNine14.P07
