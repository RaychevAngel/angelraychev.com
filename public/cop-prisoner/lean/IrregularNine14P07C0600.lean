import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0357
import IrregularNine14P07C0358

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36000 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 35 262 76 168 19 241 209 209 465), lower := (rows 35 262 76 168 19 32 64 128 256), losses := [] }

theorem u36000 : Upper (D 7) (R 7) [34,260,72,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36001 : Route 9 := (fun mask => (mask,id))

def c36001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36001 : Upper (D 7) (R 7) [34,260,72,160,65] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,65] 13 (by decide) (choices 1) [1,2,16,128] r36001 c36001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21446
  · exact u21447
  · exact u21448
  · exact u21449

def r36002 : Route 9 := (fun mask => (mask,id))

def c36002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36002 : Upper (D 7) (R 7) [34,260,72,160,66] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,66] 13 (by decide) (choices 1) [1,16,128] r36002 c36002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21450
  · exact u21451
  · exact u21452

def r36003 : Route 9 := (fun mask => (mask,id))

def c36003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36003 : Upper (D 7) (R 7) [34,260,72,160,129] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,129] 13 (by decide) (choices 1) [1,2,16,64] r36003 c36003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21453
  · exact u21454
  · exact u21455
  · exact u21456

def r36004 : Route 9 := (fun mask => (mask,id))

def c36004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36004 : Upper (D 7) (R 7) [34,260,72,160,130] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,130] 13 (by decide) (choices 1) [1,16,64] r36004 c36004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21457
  · exact u21458
  · exact u21459

def r36005 : Route 9 := (fun mask => (mask,id))

def c36005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36005 : Upper (D 7) (R 7) [34,260,72,160,192] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,192] 13 (by decide) (choices 1) [1,2,16] r36005 c36005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21460
  · exact u21461
  · exact u21462

def b36006 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 100 11 25 240 208 208 464), lower := (rows 35 262 100 11 25 32 64 128 256), losses := [] }

theorem u36006 : Upper (D 7) (R 7) [34,260,96,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36007 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 100 11 81 184 216 152 408), lower := (rows 35 262 100 11 81 32 64 128 256), losses := [] }

theorem u36007 : Upper (D 7) (R 7) [34,260,96,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36008 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 100 11 88 177 209 145 401), lower := (rows 35 262 100 11 88 32 64 128 256), losses := [] }

theorem u36008 : Upper (D 7) (R 7) [34,260,96,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36009 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 100 11 145 248 216 216 472), lower := (rows 35 262 100 11 145 32 64 128 256), losses := [] }

theorem u36009 : Upper (D 7) (R 7) [34,260,96,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36010 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 100 11 152 241 209 209 465), lower := (rows 35 262 100 11 152 32 64 128 256), losses := [] }

theorem u36010 : Upper (D 7) (R 7) [34,260,96,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36011 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 100 11 208 185 217 153 409), lower := (rows 35 262 100 11 208 32 64 128 256), losses := [] }

theorem u36011 : Upper (D 7) (R 7) [34,260,96,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36012 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 262 100 25 25 226 194 194 450), lower := (rows 35 262 100 25 25 32 64 128 256), losses := [] }

theorem u36012 : Upper (D 7) (R 7) [34,260,96,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36013 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 100 25 26 225 193 193 449), lower := (rows 35 262 100 25 26 32 64 128 256), losses := [] }

theorem u36013 : Upper (D 7) (R 7) [34,260,96,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36014 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 100 25 81 170 202 138 394), lower := (rows 35 262 100 25 81 32 64 128 256), losses := [] }

theorem u36014 : Upper (D 7) (R 7) [34,260,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36015 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(3,5),(3,6),(4,5)], upper := (rows 35 262 100 25 82 169 201 137 393), lower := (rows 35 262 100 25 82 32 64 128 256), losses := [] }

theorem u36015 : Upper (D 7) (R 7) [34,260,96,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36016 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 35 262 100 25 88 163 195 131 387), lower := (rows 35 262 100 25 88 32 64 128 256), losses := [] }

theorem u36016 : Upper (D 7) (R 7) [34,260,96,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36017 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 100 25 145 234 202 202 458), lower := (rows 35 262 100 25 145 32 64 128 256), losses := [] }

theorem u36017 : Upper (D 7) (R 7) [34,260,96,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36018 : Route 9 := (fun mask => (mask,id))

def c36018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36018 : Upper (D 7) (R 7) [34,260,96,17,130] 13 := by
  apply FastRouting.sound _ _ [34,260,96,17,130] 13 (by decide) (choices 1) [1,8,64,128] r36018 c36018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21463
  · exact u21464
  · exact u21465
  · exact u21466

def r36019 : Route 9 := (fun mask => (mask,id))

def c36019 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36019 : Upper (D 7) (R 7) [34,260,96,17,136] 13 := by
  apply FastRouting.sound _ _ [34,260,96,17,136] 13 (by decide) (choices 1) [1,2,64,128] r36019 c36019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21467
  · exact u21468
  · exact u21469
  · exact u21470

def r36020 : Route 9 := (fun mask => (mask,id))

def c36020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36020 : Upper (D 7) (R 7) [34,260,96,17,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,17,192] 13 (by decide) (choices 1) [1,2,8,128] r36020 c36020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21471
  · exact u21472
  · exact u21473
  · exact u21474

def r36021 : Route 9 := (fun mask => (mask,id))

def c36021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36021 : Upper (D 7) (R 7) [34,260,96,18,65] 13 := by
  apply FastRouting.sound _ _ [34,260,96,18,65] 13 (by decide) (choices 1) [1,8,128] r36021 c36021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21475
  · exact u21476
  · exact u21477

def b36022 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 35 262 100 26 88 161 193 129 385), lower := (rows 35 262 100 26 88 32 64 128 256), losses := [] }

theorem u36022 : Upper (D 7) (R 7) [34,260,96,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36023 : Route 9 := (fun mask => (mask,id))

def c36023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36023 : Upper (D 7) (R 7) [34,260,96,18,129] 13 := by
  apply FastRouting.sound _ _ [34,260,96,18,129] 13 (by decide) (choices 1) [1,8,64,128] r36023 c36023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21478
  · exact u21479
  · exact u21480
  · exact u21481

def r36024 : Route 9 := (fun mask => (mask,id))

def c36024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36024 : Upper (D 7) (R 7) [34,260,96,18,136] 13 := by
  apply FastRouting.sound _ _ [34,260,96,18,136] 13 (by decide) (choices 1) [1,64,128] r36024 c36024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21482
  · exact u21483
  · exact u21484

def r36025 : Route 9 := (fun mask => (mask,id))

def c36025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36025 : Upper (D 7) (R 7) [34,260,96,18,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,18,192] 13 (by decide) (choices 1) [1,8,128] r36025 c36025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21485
  · exact u21486
  · exact u21487

def r36026 : Route 9 := (fun mask => (mask,id))

def c36026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36026 : Upper (D 7) (R 7) [34,260,96,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,96,65,129] 13 (by decide) (choices 1) [2,8,16,128] r36026 c36026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21488
  · exact u21489
  · exact u21490
  · exact u21491

def r36027 : Route 9 := (fun mask => (mask,id))

def c36027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36027 : Upper (D 7) (R 7) [34,260,96,65,130] 13 := by
  apply FastRouting.sound _ _ [34,260,96,65,130] 13 (by decide) (choices 1) [1,8,16,128] r36027 c36027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21492
  · exact u21493
  · exact u21494
  · exact u21495

def r36028 : Route 9 := (fun mask => (mask,id))

def c36028 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36028 : Upper (D 7) (R 7) [34,260,96,65,136] 13 := by
  apply FastRouting.sound _ _ [34,260,96,65,136] 13 (by decide) (choices 1) [1,2,16,128] r36028 c36028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21496
  · exact u21497
  · exact u21498
  · exact u21499

def b36029 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 262 100 74 145 185 217 153 409), lower := (rows 35 262 100 74 145 32 64 128 256), losses := [] }

theorem u36029 : Upper (D 7) (R 7) [34,260,96,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36030 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 262 100 74 152 177 209 145 401), lower := (rows 35 262 100 74 152 32 64 128 256), losses := [] }

theorem u36030 : Upper (D 7) (R 7) [34,260,96,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36031 : Route 9 := (fun mask => (mask,id))

def c36031 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36031 : Upper (D 7) (R 7) [34,260,96,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,96,80,129] 13 (by decide) (choices 1) [1,2,8,128] r36031 c36031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21500
  · exact u21501
  · exact u21502
  · exact u21503

def r36032 : Route 9 := (fun mask => (mask,id))

def c36032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36032 : Upper (D 7) (R 7) [34,260,96,80,130] 13 := by
  apply FastRouting.sound _ _ [34,260,96,80,130] 13 (by decide) (choices 1) [1,8,128] r36032 c36032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21504
  · exact u21505
  · exact u21506

def b36033 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 35 262 100 88 152 163 195 131 387), lower := (rows 35 262 100 88 152 32 64 128 256), losses := [] }

theorem u36033 : Upper (D 7) (R 7) [34,260,96,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36034 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 262 100 137 145 122 90 218 346), lower := (rows 35 262 100 137 145 32 64 128 256), losses := [] }

theorem u36034 : Upper (D 7) (R 7) [34,260,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36035 : Route 9 := (fun mask => (mask,id))

def c36035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36035 : Upper (D 7) (R 7) [34,260,96,129,130] 13 := by
  apply FastRouting.sound _ _ [34,260,96,129,130] 13 (by decide) (choices 1) [1,8,16,64] r36035 c36035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21507
  · exact u21508
  · exact u21509
  · exact u21510

def b36036 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 262 100 137 152 115 83 211 339), lower := (rows 35 262 100 137 152 32 64 128 256), losses := [] }

theorem u36036 : Upper (D 7) (R 7) [34,260,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36037 : Route 9 := (fun mask => (mask,id))

def c36037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36037 : Upper (D 7) (R 7) [34,260,96,129,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,129,192] 13 (by decide) (choices 1) [1,2,8,16] r36037 c36037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21511
  · exact u21512
  · exact u21513
  · exact u21514

def b36038 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 262 100 138 152 113 81 209 337), lower := (rows 35 262 100 138 152 32 64 128 256), losses := [] }

theorem u36038 : Upper (D 7) (R 7) [34,260,96,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36039 : Route 9 := (fun mask => (mask,id))

def c36039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36039 : Upper (D 7) (R 7) [34,260,96,130,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,130,192] 13 (by decide) (choices 1) [1,8,16] r36039 c36039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21515
  · exact u21516
  · exact u21517

def b36040 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 100 152 152 99 67 195 323), lower := (rows 35 262 100 152 152 32 64 128 256), losses := [] }

theorem u36040 : Upper (D 7) (R 7) [34,260,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36041 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 100 152 208 43 75 139 267), lower := (rows 35 262 100 152 208 32 64 128 256), losses := [] }

theorem u36041 : Upper (D 7) (R 7) [34,260,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36042 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 196 11 25 240 240 240 496), lower := (rows 35 262 196 11 25 32 64 128 256), losses := [] }

theorem u36042 : Upper (D 7) (R 7) [34,260,192,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36043 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 196 11 56 241 209 209 465), lower := (rows 35 262 196 11 56 32 64 128 256), losses := [] }

theorem u36043 : Upper (D 7) (R 7) [34,260,192,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36044 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 196 11 81 184 248 184 440), lower := (rows 35 262 196 11 81 32 64 128 256), losses := [] }

theorem u36044 : Upper (D 7) (R 7) [34,260,192,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36045 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 196 11 88 177 241 177 433), lower := (rows 35 262 196 11 88 32 64 128 256), losses := [] }

theorem u36045 : Upper (D 7) (R 7) [34,260,192,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36046 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 196 11 112 185 217 153 409), lower := (rows 35 262 196 11 112 32 64 128 256), losses := [] }

theorem u36046 : Upper (D 7) (R 7) [34,260,192,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36047 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 196 25 25 226 226 226 482), lower := (rows 35 262 196 25 25 32 64 128 256), losses := [] }

theorem u36047 : Upper (D 7) (R 7) [34,260,192,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36048 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 196 25 26 225 225 225 481), lower := (rows 35 262 196 25 26 32 64 128 256), losses := [] }

theorem u36048 : Upper (D 7) (R 7) [34,260,192,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36049 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 262 196 25 49 234 202 202 458), lower := (rows 35 262 196 25 49 32 64 128 256), losses := [] }

theorem u36049 : Upper (D 7) (R 7) [34,260,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36050 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 196 25 50 233 201 201 457), lower := (rows 35 262 196 25 50 32 64 128 256), losses := [] }

theorem u36050 : Upper (D 7) (R 7) [34,260,192,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36051 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 262 196 25 56 227 195 195 451), lower := (rows 35 262 196 25 56 32 64 128 256), losses := [] }

theorem u36051 : Upper (D 7) (R 7) [34,260,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36052 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 196 25 81 170 234 170 426), lower := (rows 35 262 196 25 81 32 64 128 256), losses := [] }

theorem u36052 : Upper (D 7) (R 7) [34,260,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36053 : Route 9 := (fun mask => (mask,id))

def c36053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36053 : Upper (D 7) (R 7) [34,260,192,17,66] 13 := by
  apply FastRouting.sound _ _ [34,260,192,17,66] 13 (by decide) (choices 1) [1,8,128] r36053 c36053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21518
  · exact u21519
  · exact u21520

def r36054 : Route 9 := (fun mask => (mask,id))

def c36054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36054 : Upper (D 7) (R 7) [34,260,192,17,72] 13 := by
  apply FastRouting.sound _ _ [34,260,192,17,72] 13 (by decide) (choices 1) [1,2,128] r36054 c36054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21521
  · exact u21522
  · exact u21523

def r36055 : Route 9 := (fun mask => (mask,id))

def c36055 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36055 : Upper (D 7) (R 7) [34,260,192,17,96] 13 := by
  apply FastRouting.sound _ _ [34,260,192,17,96] 13 (by decide) (choices 1) [1,2,8,128] r36055 c36055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21524
  · exact u21525
  · exact u21526
  · exact u21527

def b36056 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 35 262 196 25 208 43 107 171 299), lower := (rows 35 262 196 25 208 32 64 128 256), losses := [] }

theorem u36056 : Upper (D 7) (R 7) [34,260,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36057 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 196 26 49 233 201 201 457), lower := (rows 35 262 196 26 49 32 64 128 256), losses := [] }

theorem u36057 : Upper (D 7) (R 7) [34,260,192,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36058 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 196 26 56 225 193 193 449), lower := (rows 35 262 196 26 56 32 64 128 256), losses := [] }

theorem u36058 : Upper (D 7) (R 7) [34,260,192,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36059 : Route 9 := (fun mask => (mask,id))

def c36059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36059 : Upper (D 7) (R 7) [34,260,192,18,65] 13 := by
  apply FastRouting.sound _ _ [34,260,192,18,65] 13 (by decide) (choices 1) [1,8,128] r36059 c36059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21528
  · exact u21529
  · exact u21530

#print axioms u36059
end Delivery.IrregularNine14.P07
