import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0019
import IrregularNine14P10C0024
import IrregularNine14P10C0025
import IrregularNine14P10C0026
import IrregularNine14P10C0027

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m2640_40 : Upper (D 10) (R 10) [6,65,144,160,40] 13 :=
  permutation_upper _ _ _ [6,65,136,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1451

theorem m2640_72 : Upper (D 10) (R 10) [6,65,144,160,72] 13 :=
  permutation_upper _ _ _ [6,65,136,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1456

theorem m2640_96 : Upper (D 10) (R 10) [6,65,144,160,96] 13 :=
  permutation_upper _ _ _ [6,65,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1459

theorem m2640_264 : Upper (D 10) (R 10) [6,65,144,160,264] 13 :=
  permutation_upper _ _ _ [6,65,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1466

theorem m2640_288 : Upper (D 10) (R 10) [6,65,144,160,288] 13 :=
  permutation_upper _ _ _ [6,65,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1472

theorem m2640_320 : Upper (D 10) (R 10) [6,65,144,160,320] 13 :=
  permutation_upper _ _ _ [6,65,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1477

def r2640 : Route 9 := (fun mask => (mask,id))

def c2640 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2640 : Upper (D 10) (R 10) [6,65,144,160] 13 := by
  apply FastRouting.sound _ _ [6,65,144,160] 13 (by decide) (choices 2) [40,72,96,264,288,320] r2640 c2640
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2640_40
  · exact m2640_72
  · exact m2640_96
  · exact m2640_264
  · exact m2640_288
  · exact m2640_320

def b2641 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 148 200 312 296 360 424 296), lower := (rows 7 67 148 200 16 32 64 128 256), losses := [] }

theorem u2641 : Upper (D 10) (R 10) [6,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2641 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2642_40 : Upper (D 10) (R 10) [6,65,144,288,40] 13 :=
  permutation_upper _ _ _ [6,65,136,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1453

theorem m2642_72 : Upper (D 10) (R 10) [6,65,144,288,72] 13 :=
  permutation_upper _ _ _ [6,65,136,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1457

theorem m2642_96 : Upper (D 10) (R 10) [6,65,144,288,96] 13 :=
  permutation_upper _ _ _ [6,65,136,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1460

theorem m2642_136 : Upper (D 10) (R 10) [6,65,144,288,136] 13 :=
  permutation_upper _ _ _ [6,65,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1462

theorem m2642_160 : Upper (D 10) (R 10) [6,65,144,288,160] 13 :=
  permutation_upper _ _ _ [6,65,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1463

theorem m2642_192 : Upper (D 10) (R 10) [6,65,144,288,192] 13 :=
  permutation_upper _ _ _ [6,65,136,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1464

theorem m2642_264 : Upper (D 10) (R 10) [6,65,144,288,264] 13 :=
  permutation_upper _ _ _ [6,65,136,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1468

theorem m2642_288 : Upper (D 10) (R 10) [6,65,144,288,288] 13 :=
  permutation_upper _ _ _ [6,65,136,288,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1474

theorem m2642_320 : Upper (D 10) (R 10) [6,65,144,288,320] 13 :=
  permutation_upper _ _ _ [6,65,136,320,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1478

theorem m2642_384 : Upper (D 10) (R 10) [6,65,144,288,384] 13 :=
  permutation_upper _ _ _ [6,65,136,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1480

def r2642 : Route 9 := (fun mask => (mask,id))

def c2642 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2642 : Upper (D 10) (R 10) [6,65,144,288] 13 := by
  apply FastRouting.sound _ _ [6,65,144,288] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2642 c2642
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2642_40
  · exact m2642_72
  · exact m2642_96
  · exact m2642_136
  · exact m2642_160
  · exact m2642_192
  · exact m2642_264
  · exact m2642_288
  · exact m2642_320
  · exact m2642_384

def b2643 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 148 328 440 424 488 424 424), lower := (rows 7 67 148 328 16 32 64 128 256), losses := [] }

theorem u2643 : Upper (D 10) (R 10) [6,65,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2643 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2644_40 : Upper (D 10) (R 10) [6,65,144,384,40] 13 :=
  permutation_upper _ _ _ [6,65,136,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1455

theorem m2644_72 : Upper (D 10) (R 10) [6,65,144,384,72] 13 :=
  permutation_upper _ _ _ [6,65,136,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1458

theorem m2644_96 : Upper (D 10) (R 10) [6,65,144,384,96] 13 :=
  permutation_upper _ _ _ [6,65,136,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1461

theorem m2644_264 : Upper (D 10) (R 10) [6,65,144,384,264] 13 :=
  permutation_upper _ _ _ [6,65,136,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1470

theorem m2644_288 : Upper (D 10) (R 10) [6,65,144,384,288] 13 :=
  permutation_upper _ _ _ [6,65,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1476

theorem m2644_320 : Upper (D 10) (R 10) [6,65,144,384,320] 13 :=
  permutation_upper _ _ _ [6,65,136,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1479

def r2644 : Route 9 := (fun mask => (mask,id))

def c2644 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2644 : Upper (D 10) (R 10) [6,65,144,384] 13 := by
  apply FastRouting.sound _ _ [6,65,144,384] 13 (by decide) (choices 2) [40,72,96,264,288,320] r2644 c2644
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2644_40
  · exact m2644_72
  · exact m2644_96
  · exact m2644_264
  · exact m2644_288
  · exact m2644_320

def r2645 : Route 9 := (fun mask => (mask,id))

def c2645 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2645 : Upper (D 10) (R 10) [6,65,160,48] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2645 c2645
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1481
  · exact u1482
  · exact u1483
  · exact u1484
  · exact u1485
  · exact u1486
  · exact u1487
  · exact u1488
  · exact u1489
  · exact u1490

def b2646 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 88 440 424 488 424 424), lower := (rows 7 67 164 88 16 32 64 128 256), losses := [] }

theorem u2646 : Upper (D 10) (R 10) [6,65,160,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2646 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2647 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 104 440 440 504 440 440), lower := (rows 7 67 164 104 16 32 64 128 256), losses := [] }

theorem u2647 : Upper (D 10) (R 10) [6,65,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2647 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2648_40 : Upper (D 10) (R 10) [6,65,160,144,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1484

theorem m2648_72 : Upper (D 10) (R 10) [6,65,160,144,72] 13 :=
  permutation_upper _ _ _ [6,65,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1491

theorem m2648_96 : Upper (D 10) (R 10) [6,65,160,144,96] 13 :=
  permutation_upper _ _ _ [6,65,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1495

def r2648 : Route 9 := (fun mask => (mask,id))

def c2648 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2648 : Upper (D 10) (R 10) [6,65,160,144] 13 := by
  apply FastRouting.sound _ _ [6,65,160,144] 13 (by decide) (choices 2) [40,72,96,264,288,320] r2648 c2648
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2648_40
  · exact m2648_72
  · exact m2648_96
  · exact u1499
  · exact u1500
  · exact u1501

def b2649 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 67 164 168 376 376 376 504 376), lower := (rows 7 67 164 168 16 32 64 128 256), losses := [] }

theorem u2649 : Upper (D 10) (R 10) [6,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2649 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2650 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 200 312 312 376 440 312), lower := (rows 7 67 164 200 16 32 64 128 256), losses := [] }

theorem u2650 : Upper (D 10) (R 10) [6,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2650 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2651_40 : Upper (D 10) (R 10) [6,65,160,272,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1487

theorem m2651_72 : Upper (D 10) (R 10) [6,65,160,272,72] 13 :=
  permutation_upper _ _ _ [6,65,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1492

theorem m2651_96 : Upper (D 10) (R 10) [6,65,160,272,96] 13 :=
  permutation_upper _ _ _ [6,65,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1496

theorem m2651_136 : Upper (D 10) (R 10) [6,65,160,272,136] 13 :=
  permutation_upper _ _ _ [6,65,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1499

theorem m2651_160 : Upper (D 10) (R 10) [6,65,160,272,160] 13 :=
  permutation_upper _ _ _ [6,65,160,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1502

theorem m2651_192 : Upper (D 10) (R 10) [6,65,160,272,192] 13 :=
  permutation_upper _ _ _ [6,65,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1504

def r2651 : Route 9 := (fun mask => (mask,id))

def c2651 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2651 : Upper (D 10) (R 10) [6,65,160,272] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2651 c2651
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2651_40
  · exact m2651_72
  · exact m2651_96
  · exact m2651_136
  · exact m2651_160
  · exact m2651_192
  · exact u1506
  · exact u1507
  · exact u1508
  · exact u1509

theorem m2652_40 : Upper (D 10) (R 10) [6,65,160,288,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1488

theorem m2652_72 : Upper (D 10) (R 10) [6,65,160,288,72] 13 :=
  permutation_upper _ _ _ [6,65,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1493

theorem m2652_96 : Upper (D 10) (R 10) [6,65,160,288,96] 13 :=
  permutation_upper _ _ _ [6,65,160,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1497

theorem m2652_136 : Upper (D 10) (R 10) [6,65,160,288,136] 13 :=
  permutation_upper _ _ _ [6,65,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1500

theorem m2652_160 : Upper (D 10) (R 10) [6,65,160,288,160] 13 :=
  permutation_upper _ _ _ [6,65,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1503

theorem m2652_192 : Upper (D 10) (R 10) [6,65,160,288,192] 13 :=
  permutation_upper _ _ _ [6,65,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1505

theorem m2652_264 : Upper (D 10) (R 10) [6,65,160,288,264] 13 :=
  permutation_upper _ _ _ [6,65,160,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1507

def r2652 : Route 9 := (fun mask => (mask,id))

def c2652 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2652 : Upper (D 10) (R 10) [6,65,160,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,288] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2652 c2652
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2652_40
  · exact m2652_72
  · exact m2652_96
  · exact m2652_136
  · exact m2652_160
  · exact m2652_192
  · exact m2652_264
  · exact u1510
  · exact u1511
  · exact u1512

def b2653 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 328 440 440 504 440 440), lower := (rows 7 67 164 328 16 32 64 128 256), losses := [] }

theorem u2653 : Upper (D 10) (R 10) [6,65,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2653 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2654_40 : Upper (D 10) (R 10) [6,65,160,384,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1490

theorem m2654_72 : Upper (D 10) (R 10) [6,65,160,384,72] 13 :=
  permutation_upper _ _ _ [6,65,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1494

theorem m2654_96 : Upper (D 10) (R 10) [6,65,160,384,96] 13 :=
  permutation_upper _ _ _ [6,65,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1498

theorem m2654_264 : Upper (D 10) (R 10) [6,65,160,384,264] 13 :=
  permutation_upper _ _ _ [6,65,160,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1509

theorem m2654_288 : Upper (D 10) (R 10) [6,65,160,384,288] 13 :=
  permutation_upper _ _ _ [6,65,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1512

theorem m2654_320 : Upper (D 10) (R 10) [6,65,160,384,320] 13 :=
  permutation_upper _ _ _ [6,65,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1513

def r2654 : Route 9 := (fun mask => (mask,id))

def c2654 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2654 : Upper (D 10) (R 10) [6,65,160,384] 13 := by
  apply FastRouting.sound _ _ [6,65,160,384] 13 (by decide) (choices 2) [40,72,96,264,288,320] r2654 c2654
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2654_40
  · exact m2654_72
  · exact m2654_96
  · exact m2654_264
  · exact m2654_288
  · exact m2654_320

def b2655 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 196 168 312 312 376 440 312), lower := (rows 7 67 196 168 16 32 64 128 256), losses := [] }

theorem u2655 : Upper (D 10) (R 10) [6,65,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2655 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2656 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 196 296 440 440 504 440 440), lower := (rows 7 67 196 296 16 32 64 128 256), losses := [] }

theorem u2656 : Upper (D 10) (R 10) [6,65,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2656 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2657 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 196 392 312 312 376 440 312), lower := (rows 7 67 196 392 16 32 64 128 256), losses := [] }

theorem u2657 : Upper (D 10) (R 10) [6,65,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2657 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2658 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2658 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2658 : Upper (D 10) (R 10) [6,65,384,48] 13 := by
  apply FastRouting.sound _ _ [6,65,384,48] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r2658 c2658
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1522
  · exact u1523
  · exact u1524
  · exact u1525
  · exact u1526
  · exact u1527
  · exact u1528

def b2659 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 388 88 440 424 488 424 424), lower := (rows 7 67 388 88 16 32 64 128 256), losses := [] }

theorem u2659 : Upper (D 10) (R 10) [6,65,384,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2659 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2660 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 388 104 440 440 504 440 440), lower := (rows 7 67 388 104 16 32 64 128 256), losses := [] }

theorem u2660 : Upper (D 10) (R 10) [6,65,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2660 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2661_40 : Upper (D 10) (R 10) [6,65,384,144,40] 13 :=
  permutation_upper _ _ _ [6,65,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1525

theorem m2661_72 : Upper (D 10) (R 10) [6,65,384,144,72] 13 :=
  permutation_upper _ _ _ [6,65,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1529

theorem m2661_96 : Upper (D 10) (R 10) [6,65,384,144,96] 13 :=
  permutation_upper _ _ _ [6,65,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1531

def r2661 : Route 9 := (fun mask => (mask,id))

def c2661 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2661 : Upper (D 10) (R 10) [6,65,384,144] 13 := by
  apply FastRouting.sound _ _ [6,65,384,144] 13 (by decide) (choices 2) [40,72,96,264,288,320] r2661 c2661
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2661_40
  · exact m2661_72
  · exact m2661_96
  · exact u1533
  · exact u1534
  · exact u1535

theorem m2662_40 : Upper (D 10) (R 10) [6,65,384,160,40] 13 :=
  permutation_upper _ _ _ [6,65,384,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1526

theorem m2662_72 : Upper (D 10) (R 10) [6,65,384,160,72] 13 :=
  permutation_upper _ _ _ [6,65,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1530

theorem m2662_96 : Upper (D 10) (R 10) [6,65,384,160,96] 13 :=
  permutation_upper _ _ _ [6,65,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1532

theorem m2662_264 : Upper (D 10) (R 10) [6,65,384,160,264] 13 :=
  permutation_upper _ _ _ [6,65,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1534

def r2662 : Route 9 := (fun mask => (mask,id))

def c2662 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2662 : Upper (D 10) (R 10) [6,65,384,160] 13 := by
  apply FastRouting.sound _ _ [6,65,384,160] 13 (by decide) (choices 2) [40,72,96,264,288,320] r2662 c2662
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2662_40
  · exact m2662_72
  · exact m2662_96
  · exact m2662_264
  · exact u1536
  · exact u1537

def b2663 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 388 200 312 312 376 440 312), lower := (rows 7 67 388 200 16 32 64 128 256), losses := [] }

theorem u2663 : Upper (D 10) (R 10) [6,65,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2663 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2664 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 67 388 392 120 120 120 248 376), lower := (rows 7 67 388 392 16 32 64 128 256), losses := [] }

theorem u2664 : Upper (D 10) (R 10) [6,65,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2664 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2665 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 41 432 416 480 416 416), lower := (rows 7 74 84 41 16 32 64 128 256), losses := [] }

theorem u2665 : Upper (D 10) (R 10) [6,72,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2665 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2666 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 137 432 416 480 416 416), lower := (rows 7 74 84 137 16 32 64 128 256), losses := [] }

theorem u2666 : Upper (D 10) (R 10) [6,72,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2666 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2667 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 168 433 417 481 417 417), lower := (rows 7 74 84 168 16 32 64 128 256), losses := [] }

theorem u2667 : Upper (D 10) (R 10) [6,72,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2667 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2668 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 392 433 417 481 417 417), lower := (rows 7 74 84 392 16 32 64 128 256), losses := [] }

theorem u2668 : Upper (D 10) (R 10) [6,72,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2668 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2669 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 25 432 416 480 416 416), lower := (rows 7 74 100 25 16 32 64 128 256), losses := [] }

theorem u2669 : Upper (D 10) (R 10) [6,72,96,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2669 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2670 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 74 100 41 432 432 496 432 432), lower := (rows 7 74 100 41 16 32 64 128 256), losses := [] }

theorem u2670 : Upper (D 10) (R 10) [6,72,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2670 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2671 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 137 432 432 496 432 432), lower := (rows 7 74 100 137 16 32 64 128 256), losses := [] }

theorem u2671 : Upper (D 10) (R 10) [6,72,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2671 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2672 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 168 433 433 497 433 433), lower := (rows 7 74 100 168 16 32 64 128 256), losses := [] }

theorem u2672 : Upper (D 10) (R 10) [6,72,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2672 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2673 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 392 433 433 497 433 433), lower := (rows 7 74 100 392 16 32 64 128 256), losses := [] }

theorem u2673 : Upper (D 10) (R 10) [6,72,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2673 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2674 : Route 9 := (fun mask => (mask,id))

def c2674 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2674 : Upper (D 10) (R 10) [6,72,144,33] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2674 c2674
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1563
  · exact u1564
  · exact u1565
  · exact u1566
  · exact u1567
  · exact u1568

def b2675 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 148 73 432 416 480 416 416), lower := (rows 7 74 148 73 16 32 64 128 256), losses := [] }

theorem u2675 : Upper (D 10) (R 10) [6,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2675 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2676 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 148 104 433 417 481 417 417), lower := (rows 7 74 148 104 16 32 64 128 256), losses := [] }

theorem u2676 : Upper (D 10) (R 10) [6,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2676 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2677 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 148 137 368 352 352 480 352), lower := (rows 7 74 148 137 16 32 64 128 256), losses := [] }

theorem u2677 : Upper (D 10) (R 10) [6,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2677 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2678_33 : Upper (D 10) (R 10) [6,72,144,160,33] 13 :=
  permutation_upper _ _ _ [6,72,144,33,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1563

theorem m2678_65 : Upper (D 10) (R 10) [6,72,144,160,65] 13 :=
  permutation_upper _ _ _ [6,72,144,129,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1572

def r2678 : Route 9 := (fun mask => (mask,id))

def c2678 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2678 : Upper (D 10) (R 10) [6,72,144,160] 13 := by
  apply FastRouting.sound _ _ [6,72,144,160] 13 (by decide) (choices 2) [33,65,96,257,288,320] r2678 c2678
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2678_33
  · exact m2678_65
  · exact u1575
  · exact u1576
  · exact u1577
  · exact u1578

def b2679 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 148 200 305 289 353 417 289), lower := (rows 7 74 148 200 16 32 64 128 256), losses := [] }

theorem u2679 : Upper (D 10) (R 10) [6,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2679 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2680_96 : Upper (D 10) (R 10) [6,72,144,257,96] 13 :=
  permutation_upper _ _ _ [6,72,144,160,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1576

theorem m2680_160 : Upper (D 10) (R 10) [6,72,144,257,160] 13 :=
  permutation_upper _ _ _ [6,72,144,96,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1570

theorem m2680_192 : Upper (D 10) (R 10) [6,72,144,257,192] 13 :=
  permutation_upper _ _ _ [6,72,144,192,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1579

def r2680 : Route 9 := (fun mask => (mask,id))

def c2680 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2680 : Upper (D 10) (R 10) [6,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,72,144,257] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2680 c2680
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2680_96
  · exact m2680_160
  · exact m2680_192
  · exact u1581
  · exact u1582
  · exact u1583

theorem m2681_33 : Upper (D 10) (R 10) [6,72,144,288,33] 13 :=
  permutation_upper _ _ _ [6,72,144,33,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1566

theorem m2681_65 : Upper (D 10) (R 10) [6,72,144,288,65] 13 :=
  permutation_upper _ _ _ [6,72,144,129,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1573

theorem m2681_96 : Upper (D 10) (R 10) [6,72,144,288,96] 13 :=
  permutation_upper _ _ _ [6,72,144,160,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1577

theorem m2681_129 : Upper (D 10) (R 10) [6,72,144,288,129] 13 :=
  permutation_upper _ _ _ [6,72,144,65,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1569

theorem m2681_160 : Upper (D 10) (R 10) [6,72,144,288,160] 13 :=
  permutation_upper _ _ _ [6,72,144,96,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1571

theorem m2681_192 : Upper (D 10) (R 10) [6,72,144,288,192] 13 :=
  permutation_upper _ _ _ [6,72,144,192,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1580

theorem m2681_257 : Upper (D 10) (R 10) [6,72,144,288,257] 13 :=
  permutation_upper _ _ _ [6,72,144,257,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1581

def r2681 : Route 9 := (fun mask => (mask,id))

def c2681 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2681 : Upper (D 10) (R 10) [6,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r2681 c2681
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2681_33
  · exact m2681_65
  · exact m2681_96
  · exact m2681_129
  · exact m2681_160
  · exact m2681_192
  · exact m2681_257
  · exact u1584
  · exact u1585
  · exact u1586

def b2682 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 148 328 433 417 481 417 417), lower := (rows 7 74 148 328 16 32 64 128 256), losses := [] }

theorem u2682 : Upper (D 10) (R 10) [6,72,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2682 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2683_33 : Upper (D 10) (R 10) [6,72,144,384,33] 13 :=
  permutation_upper _ _ _ [6,72,144,33,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1567

theorem m2683_65 : Upper (D 10) (R 10) [6,72,144,384,65] 13 :=
  permutation_upper _ _ _ [6,72,144,129,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1574

theorem m2683_96 : Upper (D 10) (R 10) [6,72,144,384,96] 13 :=
  permutation_upper _ _ _ [6,72,144,160,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1578

theorem m2683_257 : Upper (D 10) (R 10) [6,72,144,384,257] 13 :=
  permutation_upper _ _ _ [6,72,144,257,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1582

theorem m2683_288 : Upper (D 10) (R 10) [6,72,144,384,288] 13 :=
  permutation_upper _ _ _ [6,72,144,288,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1585

def r2683 : Route 9 := (fun mask => (mask,id))

def c2683 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2683 : Upper (D 10) (R 10) [6,72,144,384] 13 := by
  apply FastRouting.sound _ _ [6,72,144,384] 13 (by decide) (choices 2) [33,65,96,257,288,320] r2683 c2683
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2683_33
  · exact m2683_65
  · exact m2683_96
  · exact m2683_257
  · exact m2683_288
  · exact u1587

theorem m2684_96 : Upper (D 10) (R 10) [6,72,160,17,96] 13 :=
  permutation_upper _ _ _ [6,24,96,65,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1171

theorem m2684_160 : Upper (D 10) (R 10) [6,72,160,17,160] 13 :=
  permutation_upper _ _ _ [6,24,96,96,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1173

theorem m2684_192 : Upper (D 10) (R 10) [6,72,160,17,192] 13 :=
  permutation_upper _ _ _ [6,24,192,65,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1192

theorem m2684_288 : Upper (D 10) (R 10) [6,72,160,17,288] 13 :=
  permutation_upper _ _ _ [6,24,96,129,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1178

theorem m2684_320 : Upper (D 10) (R 10) [6,72,160,17,320] 13 :=
  permutation_upper _ _ _ [6,24,192,65,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1193

theorem m2684_384 : Upper (D 10) (R 10) [6,72,160,17,384] 13 :=
  permutation_upper _ _ _ [6,24,192,96,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1196

def r2684 : Route 9 := (fun mask => (mask,id))

def c2684 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2684 : Upper (D 10) (R 10) [6,72,160,17] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2684 c2684
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2684_96
  · exact m2684_160
  · exact m2684_192
  · exact m2684_288
  · exact m2684_320
  · exact m2684_384

def r2685 : Route 9 := (fun mask => (mask,id))

def c2685 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2685 : Upper (D 10) (R 10) [6,72,160,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2685 c2685
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1588
  · exact u1589
  · exact u1590
  · exact u1591
  · exact u1592
  · exact u1593

def r2686 : Route 9 := (fun mask => (mask,id))

def c2686 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2686 : Upper (D 10) (R 10) [6,72,160,48] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r2686 c2686
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1594
  · exact u1595
  · exact u1596
  · exact u1597
  · exact u1598
  · exact u1599
  · exact u1600
  · exact u1601
  · exact u1602
  · exact u1603

def b2687 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 73 432 432 496 432 432), lower := (rows 7 74 164 73 16 32 64 128 256), losses := [] }

theorem u2687 : Upper (D 10) (R 10) [6,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2687 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2688 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 88 433 417 481 417 417), lower := (rows 7 74 164 88 16 32 64 128 256), losses := [] }

theorem u2688 : Upper (D 10) (R 10) [6,72,160,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2688 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2689 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 104 433 433 497 433 433), lower := (rows 7 74 164 104 16 32 64 128 256), losses := [] }

theorem u2689 : Upper (D 10) (R 10) [6,72,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2689 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2690 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 164 137 368 368 368 496 368), lower := (rows 7 74 164 137 16 32 64 128 256), losses := [] }

theorem u2690 : Upper (D 10) (R 10) [6,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2690 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2691 : Route 9 := (fun mask => (mask,id))

def c2691 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2691 : Upper (D 10) (R 10) [6,72,160,144] 13 := by
  apply FastRouting.sound _ _ [6,72,160,144] 13 (by decide) (choices 2) [33,65,96,257,288,320] r2691 c2691
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1617
  · exact u1618
  · exact u1619
  · exact u1620
  · exact u1621
  · exact u1622

def b2692 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 74 164 168 369 369 369 497 369), lower := (rows 7 74 164 168 16 32 64 128 256), losses := [] }

theorem u2692 : Upper (D 10) (R 10) [6,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2692 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2693 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 200 305 305 369 433 305), lower := (rows 7 74 164 200 16 32 64 128 256), losses := [] }

theorem u2693 : Upper (D 10) (R 10) [6,72,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2693 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2694 : Route 9 := (fun mask => (mask,id))

def c2694 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2694 : Upper (D 10) (R 10) [6,72,160,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2694 c2694
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1631
  · exact u1632
  · exact u1633
  · exact u1634
  · exact u1635
  · exact u1636

def r2695 : Route 9 := (fun mask => (mask,id))

def c2695 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2695 : Upper (D 10) (R 10) [6,72,160,272] 13 := by
  apply FastRouting.sound _ _ [6,72,160,272] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r2695 c2695
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1637
  · exact u1638
  · exact u1639
  · exact u1640
  · exact u1641
  · exact u1642
  · exact u1643
  · exact u1644
  · exact u1645
  · exact u1646

def r2696 : Route 9 := (fun mask => (mask,id))

def c2696 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2696 : Upper (D 10) (R 10) [6,72,160,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r2696 c2696
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1647
  · exact u1648
  · exact u1649
  · exact u1650
  · exact u1651
  · exact u1652
  · exact u1653
  · exact u1654
  · exact u1655
  · exact u1656

def b2697 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 328 433 433 497 433 433), lower := (rows 7 74 164 328 16 32 64 128 256), losses := [] }

theorem u2697 : Upper (D 10) (R 10) [6,72,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2697 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2698 : Route 9 := (fun mask => (mask,id))

def c2698 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2698 : Upper (D 10) (R 10) [6,72,160,384] 13 := by
  apply FastRouting.sound _ _ [6,72,160,384] 13 (by decide) (choices 2) [33,65,96,257,288,320] r2698 c2698
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1661
  · exact u1662
  · exact u1663
  · exact u1664
  · exact u1665
  · exact u1666

def b2699 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 25 432 416 480 416 416), lower := (rows 7 74 196 25 16 32 64 128 256), losses := [] }

theorem u2699 : Upper (D 10) (R 10) [6,72,192,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2699 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2699
end Delivery.IrregularNine14.P10
