import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0018
import IrregularNine14P10C0019
import IrregularNine14P10C0020
import IrregularNine14P10C0021
import IrregularNine14P10C0022
import IrregularNine14P10C0023
import IrregularNine14P10C0024
import IrregularNine14P10C0025
import IrregularNine14P10C0026
import IrregularNine14P10C0027
import IrregularNine14P10C0028

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2820 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 19 67 44 200 436 420 484 420 420), lower := (rows 19 67 44 200 16 32 64 128 256), losses := [] }

theorem u2820 : Upper (D 10) (R 10) [18,65,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2820 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2821_36 : Upper (D 10) (R 10) [18,65,40,384,36] 13 :=
  permutation_upper _ _ _ [6,40,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1291

theorem m2821_68 : Upper (D 10) (R 10) [18,65,40,384,68] 13 :=
  permutation_upper _ _ _ [6,65,72,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1439

theorem m2821_96 : Upper (D 10) (R 10) [18,65,40,384,96] 13 :=
  permutation_upper _ _ _ [6,65,96,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1445

theorem m2821_132 : Upper (D 10) (R 10) [18,65,40,384,132] 13 :=
  permutation_upper _ _ _ [6,65,136,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1455

theorem m2821_160 : Upper (D 10) (R 10) [18,65,40,384,160] 13 :=
  permutation_upper _ _ _ [6,65,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1490

theorem m2821_192 : Upper (D 10) (R 10) [18,65,40,384,192] 13 :=
  permutation_upper _ _ _ [6,65,192,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1516

theorem m2821_384 : Upper (D 10) (R 10) [18,65,40,384,384] 13 :=
  permutation_upper _ _ _ [6,65,384,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1528

def r2821 : Route 9 := (fun mask => match mask with | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2821 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2821 : Upper (D 10) (R 10) [18,65,40,384] 13 := by
  apply FastRouting.sound _ _ [18,65,40,384] 13 (by decide) (choices 2) [36,68,96,132,160,192,384] r2821 c2821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2821_36
  · exact m2821_68
  · exact m2821_96
  · exact m2821_132
  · exact m2821_160
  · exact m2821_192
  · exact m2821_384

def b2822 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 19 67 76 140 432 416 480 416 416), lower := (rows 19 67 76 140 16 32 64 128 256), losses := [] }

theorem u2822 : Upper (D 10) (R 10) [18,65,72,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2822 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2823 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 19 67 76 168 436 420 484 420 420), lower := (rows 19 67 76 168 16 32 64 128 256), losses := [] }

theorem u2823 : Upper (D 10) (R 10) [18,65,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2823 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2824 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 19 67 76 392 436 420 484 420 420), lower := (rows 19 67 76 392 16 32 64 128 256), losses := [] }

theorem u2824 : Upper (D 10) (R 10) [18,65,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2824 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2825 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 19 67 100 140 440 424 488 424 424), lower := (rows 19 67 100 140 16 32 64 128 256), losses := [] }

theorem u2825 : Upper (D 10) (R 10) [18,65,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2825 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2826 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 19 67 100 168 444 428 492 428 428), lower := (rows 19 67 100 168 16 32 64 128 256), losses := [] }

theorem u2826 : Upper (D 10) (R 10) [18,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2826 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2827 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 19 67 100 392 444 428 492 428 428), lower := (rows 19 67 100 392 16 32 64 128 256), losses := [] }

theorem u2827 : Upper (D 10) (R 10) [18,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2827 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2828_96 : Upper (D 10) (R 10) [18,65,136,260,96] 13 :=
  permutation_upper _ _ _ [6,65,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1446

theorem m2828_160 : Upper (D 10) (R 10) [18,65,136,260,160] 13 :=
  permutation_upper _ _ _ [6,65,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1499

theorem m2828_192 : Upper (D 10) (R 10) [18,65,136,260,192] 13 :=
  permutation_upper _ _ _ [6,65,192,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1517

theorem m2828_288 : Upper (D 10) (R 10) [18,65,136,260,288] 13 :=
  permutation_upper _ _ _ [6,65,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1499

theorem m2828_320 : Upper (D 10) (R 10) [18,65,136,260,320] 13 :=
  permutation_upper _ _ _ [6,65,192,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1517

theorem m2828_384 : Upper (D 10) (R 10) [18,65,136,260,384] 13 :=
  permutation_upper _ _ _ [6,65,384,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1533

def r2828 : Route 9 := (fun mask => (mask,id))

def c2828 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2828 : Upper (D 10) (R 10) [18,65,136,260] 13 := by
  apply FastRouting.sound _ _ [18,65,136,260] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2828 c2828
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2828_96
  · exact m2828_160
  · exact m2828_192
  · exact m2828_288
  · exact m2828_320
  · exact m2828_384

theorem m2829_36 : Upper (D 10) (R 10) [18,65,136,288,36] 13 :=
  permutation_upper _ _ _ [6,40,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1299

theorem m2829_68 : Upper (D 10) (R 10) [18,65,136,288,68] 13 :=
  permutation_upper _ _ _ [6,65,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1440

theorem m2829_96 : Upper (D 10) (R 10) [18,65,136,288,96] 13 :=
  permutation_upper _ _ _ [6,65,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1447

theorem m2829_132 : Upper (D 10) (R 10) [18,65,136,288,132] 13 :=
  permutation_upper _ _ _ [6,65,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1462

theorem m2829_160 : Upper (D 10) (R 10) [18,65,136,288,160] 13 :=
  permutation_upper _ _ _ [6,65,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1500

theorem m2829_192 : Upper (D 10) (R 10) [18,65,136,288,192] 13 :=
  permutation_upper _ _ _ [6,65,192,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1518

theorem m2829_260 : Upper (D 10) (R 10) [18,65,136,288,260] 13 :=
  permutation_upper _ _ _ [6,65,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1466

theorem m2829_288 : Upper (D 10) (R 10) [18,65,136,288,288] 13 :=
  permutation_upper _ _ _ [6,65,160,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1502

theorem m2829_320 : Upper (D 10) (R 10) [18,65,136,288,320] 13 :=
  permutation_upper _ _ _ [6,65,192,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1519

theorem m2829_384 : Upper (D 10) (R 10) [18,65,136,288,384] 13 :=
  permutation_upper _ _ _ [6,65,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1534

def r2829 : Route 9 := (fun mask => (mask,id))

def c2829 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2829 : Upper (D 10) (R 10) [18,65,136,288] 13 := by
  apply FastRouting.sound _ _ [18,65,136,288] 13 (by decide) (choices 2) [36,68,96,132,160,192,260,288,320,384] r2829 c2829
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2829_36
  · exact m2829_68
  · exact m2829_96
  · exact m2829_132
  · exact m2829_160
  · exact m2829_192
  · exact m2829_260
  · exact m2829_288
  · exact m2829_320
  · exact m2829_384

def b2830 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 19 67 140 328 436 420 484 420 420), lower := (rows 19 67 140 328 16 32 64 128 256), losses := [] }

theorem u2830 : Upper (D 10) (R 10) [18,65,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2830 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2831 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 19 67 164 200 316 300 364 428 300), lower := (rows 19 67 164 200 16 32 64 128 256), losses := [] }

theorem u2831 : Upper (D 10) (R 10) [18,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2831 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2832_12 : Upper (D 10) (R 10) [18,65,160,288,12] 13 :=
  permutation_upper _ _ _ [6,24,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1162

theorem m2832_36 : Upper (D 10) (R 10) [18,65,160,288,36] 13 :=
  permutation_upper _ _ _ [6,40,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1303

theorem m2832_40 : Upper (D 10) (R 10) [18,65,160,288,40] 13 :=
  permutation_upper _ _ _ [6,40,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1303

theorem m2832_68 : Upper (D 10) (R 10) [18,65,160,288,68] 13 :=
  permutation_upper _ _ _ [6,65,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1441

theorem m2832_72 : Upper (D 10) (R 10) [18,65,160,288,72] 13 :=
  permutation_upper _ _ _ [6,65,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1441

theorem m2832_96 : Upper (D 10) (R 10) [18,65,160,288,96] 13 :=
  permutation_upper _ _ _ [6,65,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1448

theorem m2832_132 : Upper (D 10) (R 10) [18,65,160,288,132] 13 :=
  permutation_upper _ _ _ [6,65,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1463

theorem m2832_136 : Upper (D 10) (R 10) [18,65,160,288,136] 13 :=
  permutation_upper _ _ _ [6,65,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1472

theorem m2832_160 : Upper (D 10) (R 10) [18,65,160,288,160] 13 :=
  permutation_upper _ _ _ [6,65,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1503

theorem m2832_192 : Upper (D 10) (R 10) [18,65,160,288,192] 13 :=
  permutation_upper _ _ _ [6,65,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1520

theorem m2832_260 : Upper (D 10) (R 10) [18,65,160,288,260] 13 :=
  permutation_upper _ _ _ [6,65,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1472

theorem m2832_264 : Upper (D 10) (R 10) [18,65,160,288,264] 13 :=
  permutation_upper _ _ _ [6,65,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1463

theorem m2832_288 : Upper (D 10) (R 10) [18,65,160,288,288] 13 :=
  permutation_upper _ _ _ [6,65,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1503

theorem m2832_320 : Upper (D 10) (R 10) [18,65,160,288,320] 13 :=
  permutation_upper _ _ _ [6,65,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1520

theorem m2832_384 : Upper (D 10) (R 10) [18,65,160,288,384] 13 :=
  permutation_upper _ _ _ [6,65,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1536

def r2832 : Route 9 := (fun mask => (mask,id))

def c2832 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u2832 : Upper (D 10) (R 10) [18,65,160,288] 13 := by
  apply FastRouting.sound _ _ [18,65,160,288] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192,260,264,288,320,384] r2832 c2832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2832_12
  · exact m2832_36
  · exact m2832_40
  · exact m2832_68
  · exact m2832_72
  · exact m2832_96
  · exact m2832_132
  · exact m2832_136
  · exact m2832_160
  · exact m2832_192
  · exact m2832_260
  · exact m2832_264
  · exact m2832_288
  · exact m2832_320
  · exact m2832_384

def b2833 : PairBound 9 := { available := 428, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 19 67 164 328 444 428 492 428 428), lower := (rows 19 67 164 328 16 32 64 128 256), losses := [] }

theorem u2833 : Upper (D 10) (R 10) [18,65,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2833 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2834_12 : Upper (D 10) (R 10) [18,65,160,384,12] 13 :=
  permutation_upper _ _ _ [6,24,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1164

theorem m2834_36 : Upper (D 10) (R 10) [18,65,160,384,36] 13 :=
  permutation_upper _ _ _ [6,40,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1304

theorem m2834_40 : Upper (D 10) (R 10) [18,65,160,384,40] 13 :=
  permutation_upper _ _ _ [6,40,65,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1309

theorem m2834_68 : Upper (D 10) (R 10) [18,65,160,384,68] 13 :=
  permutation_upper _ _ _ [6,65,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1442

theorem m2834_72 : Upper (D 10) (R 10) [18,65,160,384,72] 13 :=
  permutation_upper _ _ _ [6,65,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1443

theorem m2834_96 : Upper (D 10) (R 10) [18,65,160,384,96] 13 :=
  permutation_upper _ _ _ [6,65,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1449

theorem m2834_260 : Upper (D 10) (R 10) [18,65,160,384,260] 13 :=
  permutation_upper _ _ _ [6,65,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1476

theorem m2834_264 : Upper (D 10) (R 10) [18,65,160,384,264] 13 :=
  permutation_upper _ _ _ [6,65,136,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1480

theorem m2834_288 : Upper (D 10) (R 10) [18,65,160,384,288] 13 :=
  permutation_upper _ _ _ [6,65,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1512

theorem m2834_320 : Upper (D 10) (R 10) [18,65,160,384,320] 13 :=
  permutation_upper _ _ _ [6,65,192,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1521

def r2834 : Route 9 := (fun mask => (mask,id))

def c2834 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2834 : Upper (D 10) (R 10) [18,65,160,384] 13 := by
  apply FastRouting.sound _ _ [18,65,160,384] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r2834 c2834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2834_12
  · exact m2834_36
  · exact m2834_40
  · exact m2834_68
  · exact m2834_72
  · exact m2834_96
  · exact m2834_260
  · exact m2834_264
  · exact m2834_288
  · exact m2834_320

def b2835 : PairBound 9 := { available := 300, camps := [{ cop := 2, region := 312, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 19 67 196 392 316 300 364 428 300), lower := (rows 19 67 196 392 16 32 64 128 256), losses := [] }

theorem u2835 : Upper (D 10) (R 10) [18,65,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2835 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2836_40 : Upper (D 10) (R 10) [18,68,33,96,40] 13 :=
  permutation_upper _ _ _ [6,40,80,96,33] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1316

theorem m2836_136 : Upper (D 10) (R 10) [18,68,33,96,136] 13 :=
  permutation_upper _ _ _ [6,72,144,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1563

theorem m2836_160 : Upper (D 10) (R 10) [18,68,33,96,160] 13 :=
  permutation_upper _ _ _ [6,72,160,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1588

theorem m2836_384 : Upper (D 10) (R 10) [18,68,33,96,384] 13 :=
  permutation_upper _ _ _ [6,72,384,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1694

def r2836 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2836 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2836 : Upper (D 10) (R 10) [18,68,33,96] 13 := by
  apply FastRouting.sound _ _ [18,68,33,96] 13 (by decide) (choices 2) [40,136,160,384] r2836 c2836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2836_40
  · exact m2836_136
  · exact m2836_160
  · exact m2836_384

theorem m2837_40 : Upper (D 10) (R 10) [18,68,33,160,40] 13 :=
  permutation_upper _ _ _ [6,40,80,160,33] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1326

theorem m2837_72 : Upper (D 10) (R 10) [18,68,33,160,72] 13 :=
  permutation_upper _ _ _ [6,72,80,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1538

theorem m2837_96 : Upper (D 10) (R 10) [18,68,33,160,96] 13 :=
  permutation_upper _ _ _ [6,72,96,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1545

theorem m2837_136 : Upper (D 10) (R 10) [18,68,33,160,136] 13 :=
  permutation_upper _ _ _ [6,72,144,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1564

theorem m2837_160 : Upper (D 10) (R 10) [18,68,33,160,160] 13 :=
  permutation_upper _ _ _ [6,72,160,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1589

theorem m2837_192 : Upper (D 10) (R 10) [18,68,33,160,192] 13 :=
  permutation_upper _ _ _ [6,72,192,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1667

theorem m2837_264 : Upper (D 10) (R 10) [18,68,33,160,264] 13 :=
  permutation_upper _ _ _ [6,72,144,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1566

theorem m2837_288 : Upper (D 10) (R 10) [18,68,33,160,288] 13 :=
  permutation_upper _ _ _ [6,72,160,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1591

theorem m2837_320 : Upper (D 10) (R 10) [18,68,33,160,320] 13 :=
  permutation_upper _ _ _ [6,72,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1668

theorem m2837_384 : Upper (D 10) (R 10) [18,68,33,160,384] 13 :=
  permutation_upper _ _ _ [6,72,384,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1695

def r2837 : Route 9 := (fun mask => (mask,id))

def c2837 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2837 : Upper (D 10) (R 10) [18,68,33,160] 13 := by
  apply FastRouting.sound _ _ [18,68,33,160] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2837 c2837
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2837_40
  · exact m2837_72
  · exact m2837_96
  · exact m2837_136
  · exact m2837_160
  · exact m2837_192
  · exact m2837_264
  · exact m2837_288
  · exact m2837_320
  · exact m2837_384

theorem m2838_40 : Upper (D 10) (R 10) [18,68,33,192,40] 13 :=
  permutation_upper _ _ _ [6,40,80,192,33] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1332

theorem m2838_136 : Upper (D 10) (R 10) [18,68,33,192,136] 13 :=
  permutation_upper _ _ _ [6,72,144,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1565

theorem m2838_160 : Upper (D 10) (R 10) [18,68,33,192,160] 13 :=
  permutation_upper _ _ _ [6,72,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1590

theorem m2838_264 : Upper (D 10) (R 10) [18,68,33,192,264] 13 :=
  permutation_upper _ _ _ [6,72,144,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1567

theorem m2838_288 : Upper (D 10) (R 10) [18,68,33,192,288] 13 :=
  permutation_upper _ _ _ [6,72,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1592

theorem m2838_384 : Upper (D 10) (R 10) [18,68,33,192,384] 13 :=
  permutation_upper _ _ _ [6,72,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1696

def r2838 : Route 9 := (fun mask => (mask,id))

def c2838 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2838 : Upper (D 10) (R 10) [18,68,33,192] 13 := by
  apply FastRouting.sound _ _ [18,68,33,192] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2838 c2838
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2838_40
  · exact m2838_136
  · exact m2838_160
  · exact m2838_264
  · exact m2838_288
  · exact m2838_384

theorem m2839_40 : Upper (D 10) (R 10) [18,68,33,384,40] 13 :=
  permutation_upper _ _ _ [6,40,80,384,33] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1338

theorem m2839_72 : Upper (D 10) (R 10) [18,68,33,384,72] 13 :=
  permutation_upper _ _ _ [6,72,80,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1539

theorem m2839_96 : Upper (D 10) (R 10) [18,68,33,384,96] 13 :=
  permutation_upper _ _ _ [6,72,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1546

theorem m2839_136 : Upper (D 10) (R 10) [18,68,33,384,136] 13 :=
  permutation_upper _ _ _ [6,72,144,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1568

theorem m2839_160 : Upper (D 10) (R 10) [18,68,33,384,160] 13 :=
  permutation_upper _ _ _ [6,72,160,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1593

theorem m2839_192 : Upper (D 10) (R 10) [18,68,33,384,192] 13 :=
  permutation_upper _ _ _ [6,72,192,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1669

theorem m2839_384 : Upper (D 10) (R 10) [18,68,33,384,384] 13 :=
  permutation_upper _ _ _ [6,72,384,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1697

def r2839 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2839 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2839 : Upper (D 10) (R 10) [18,68,33,384] 13 := by
  apply FastRouting.sound _ _ [18,68,33,384] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r2839 c2839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2839_40
  · exact m2839_72
  · exact m2839_96
  · exact m2839_136
  · exact m2839_160
  · exact m2839_192
  · exact m2839_384

def b2840 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 19 70 44 73 432 416 480 416 416), lower := (rows 19 70 44 73 16 32 64 128 256), losses := [] }

theorem u2840 : Upper (D 10) (R 10) [18,68,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2840 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2841_96 : Upper (D 10) (R 10) [18,68,40,129,96] 13 :=
  permutation_upper _ _ _ [6,72,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1547

theorem m2841_160 : Upper (D 10) (R 10) [18,68,40,129,160] 13 :=
  permutation_upper _ _ _ [6,72,160,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1597

theorem m2841_192 : Upper (D 10) (R 10) [18,68,40,129,192] 13 :=
  permutation_upper _ _ _ [6,72,192,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1670

theorem m2841_288 : Upper (D 10) (R 10) [18,68,40,129,288] 13 :=
  permutation_upper _ _ _ [6,72,160,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1600

theorem m2841_320 : Upper (D 10) (R 10) [18,68,40,129,320] 13 :=
  permutation_upper _ _ _ [6,72,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1671

theorem m2841_384 : Upper (D 10) (R 10) [18,68,40,129,384] 13 :=
  permutation_upper _ _ _ [6,72,384,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1701

def r2841 : Route 9 := (fun mask => (mask,id))

def c2841 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2841 : Upper (D 10) (R 10) [18,68,40,129] 13 := by
  apply FastRouting.sound _ _ [18,68,40,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2841 c2841
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2841_96
  · exact m2841_160
  · exact m2841_192
  · exact m2841_288
  · exact m2841_320
  · exact m2841_384

def b2842 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 19 70 44 200 433 417 481 417 417), lower := (rows 19 70 44 200 16 32 64 128 256), losses := [] }

theorem u2842 : Upper (D 10) (R 10) [18,68,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2842 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2843_33 : Upper (D 10) (R 10) [18,68,40,384,33] 13 :=
  permutation_upper _ _ _ [6,33,72,48,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1217

theorem m2843_65 : Upper (D 10) (R 10) [18,68,40,384,65] 13 :=
  permutation_upper _ _ _ [6,65,72,48,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1439

theorem m2843_96 : Upper (D 10) (R 10) [18,68,40,384,96] 13 :=
  permutation_upper _ _ _ [6,72,96,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1548

theorem m2843_129 : Upper (D 10) (R 10) [18,68,40,384,129] 13 :=
  permutation_upper _ _ _ [6,65,136,48,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1454

theorem m2843_160 : Upper (D 10) (R 10) [18,68,40,384,160] 13 :=
  permutation_upper _ _ _ [6,72,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1603

theorem m2843_192 : Upper (D 10) (R 10) [18,68,40,384,192] 13 :=
  permutation_upper _ _ _ [6,72,192,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1672

theorem m2843_384 : Upper (D 10) (R 10) [18,68,40,384,384] 13 :=
  permutation_upper _ _ _ [6,72,384,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1704

def r2843 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2843 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2843 : Upper (D 10) (R 10) [18,68,40,384] 13 := by
  apply FastRouting.sound _ _ [18,68,40,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r2843 c2843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2843_33
  · exact m2843_65
  · exact m2843_96
  · exact m2843_129
  · exact m2843_160
  · exact m2843_192
  · exact m2843_384

def b2844 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 69 168 440 424 488 424 424), lower := (rows 19 70 69 168 16 32 64 128 256), losses := [] }

theorem u2844 : Upper (D 10) (R 10) [18,68,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2844 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2845 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 69 392 440 424 488 424 424), lower := (rows 19 70 69 392 16 32 64 128 256), losses := [] }

theorem u2845 : Upper (D 10) (R 10) [18,68,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2845 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2846 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 76 41 432 416 480 416 416), lower := (rows 19 70 76 41 16 32 64 128 256), losses := [] }

theorem u2846 : Upper (D 10) (R 10) [18,68,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2846 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2847 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 76 137 432 416 480 416 416), lower := (rows 19 70 76 137 16 32 64 128 256), losses := [] }

theorem u2847 : Upper (D 10) (R 10) [18,68,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2847 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2848 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 76 168 433 417 481 417 417), lower := (rows 19 70 76 168 16 32 64 128 256), losses := [] }

theorem u2848 : Upper (D 10) (R 10) [18,68,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2848 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2849 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 76 392 433 417 481 417 417), lower := (rows 19 70 76 392 16 32 64 128 256), losses := [] }

theorem u2849 : Upper (D 10) (R 10) [18,68,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2849 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2850 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 100 41 440 424 488 424 424), lower := (rows 19 70 100 41 16 32 64 128 256), losses := [] }

theorem u2850 : Upper (D 10) (R 10) [18,68,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2850 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2851 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 100 137 440 424 488 424 424), lower := (rows 19 70 100 137 16 32 64 128 256), losses := [] }

theorem u2851 : Upper (D 10) (R 10) [18,68,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2851 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2852 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 100 168 441 425 489 425 425), lower := (rows 19 70 100 168 16 32 64 128 256), losses := [] }

theorem u2852 : Upper (D 10) (R 10) [18,68,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2852 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2853 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 100 392 441 425 489 425 425), lower := (rows 19 70 100 392 16 32 64 128 256), losses := [] }

theorem u2853 : Upper (D 10) (R 10) [18,68,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2853 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2854_40 : Upper (D 10) (R 10) [18,68,129,96,40] 13 :=
  permutation_upper _ _ _ [6,40,80,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1317

theorem m2854_136 : Upper (D 10) (R 10) [18,68,129,96,136] 13 :=
  permutation_upper _ _ _ [6,72,144,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1572

theorem m2854_160 : Upper (D 10) (R 10) [18,68,129,96,160] 13 :=
  permutation_upper _ _ _ [6,72,160,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1614

theorem m2854_264 : Upper (D 10) (R 10) [18,68,129,96,264] 13 :=
  permutation_upper _ _ _ [6,72,144,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1576

theorem m2854_288 : Upper (D 10) (R 10) [18,68,129,96,288] 13 :=
  permutation_upper _ _ _ [6,72,160,257,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1631

theorem m2854_384 : Upper (D 10) (R 10) [18,68,129,96,384] 13 :=
  permutation_upper _ _ _ [6,72,384,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1710

def r2854 : Route 9 := (fun mask => (mask,id))

def c2854 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2854 : Upper (D 10) (R 10) [18,68,129,96] 13 := by
  apply FastRouting.sound _ _ [18,68,129,96] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2854 c2854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2854_40
  · exact m2854_136
  · exact m2854_160
  · exact m2854_264
  · exact m2854_288
  · exact m2854_384

theorem m2855_40 : Upper (D 10) (R 10) [18,68,129,160,40] 13 :=
  permutation_upper _ _ _ [6,40,80,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1327

theorem m2855_72 : Upper (D 10) (R 10) [18,68,129,160,72] 13 :=
  permutation_upper _ _ _ [6,72,80,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1540

theorem m2855_96 : Upper (D 10) (R 10) [18,68,129,160,96] 13 :=
  permutation_upper _ _ _ [6,72,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1549

theorem m2855_264 : Upper (D 10) (R 10) [18,68,129,160,264] 13 :=
  permutation_upper _ _ _ [6,72,144,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1581

theorem m2855_288 : Upper (D 10) (R 10) [18,68,129,160,288] 13 :=
  permutation_upper _ _ _ [6,72,160,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1634

theorem m2855_320 : Upper (D 10) (R 10) [18,68,129,160,320] 13 :=
  permutation_upper _ _ _ [6,72,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1681

def r2855 : Route 9 := (fun mask => (mask,id))

def c2855 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2855 : Upper (D 10) (R 10) [18,68,129,160] 13 := by
  apply FastRouting.sound _ _ [18,68,129,160] 13 (by decide) (choices 2) [40,72,96,264,288,320] r2855 c2855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2855_40
  · exact m2855_72
  · exact m2855_96
  · exact m2855_264
  · exact m2855_288
  · exact m2855_320

def b2856 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 304, targets := 64 },{ cop := 3, region := 304, targets := 128 }], pairs := [(4,6),(4,7)], upper := (rows 19 70 133 200 312 296 360 424 296), lower := (rows 19 70 133 200 16 32 64 128 256), losses := [] }

theorem u2856 : Upper (D 10) (R 10) [18,68,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2856 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2857_40 : Upper (D 10) (R 10) [18,68,129,288,40] 13 :=
  permutation_upper _ _ _ [6,40,80,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1329

theorem m2857_72 : Upper (D 10) (R 10) [18,68,129,288,72] 13 :=
  permutation_upper _ _ _ [6,72,80,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1541

theorem m2857_96 : Upper (D 10) (R 10) [18,68,129,288,96] 13 :=
  permutation_upper _ _ _ [6,72,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1550

theorem m2857_136 : Upper (D 10) (R 10) [18,68,129,288,136] 13 :=
  permutation_upper _ _ _ [6,72,144,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1573

theorem m2857_160 : Upper (D 10) (R 10) [18,68,129,288,160] 13 :=
  permutation_upper _ _ _ [6,72,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1615

theorem m2857_192 : Upper (D 10) (R 10) [18,68,129,288,192] 13 :=
  permutation_upper _ _ _ [6,72,192,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1673

theorem m2857_264 : Upper (D 10) (R 10) [18,68,129,288,264] 13 :=
  permutation_upper _ _ _ [6,72,144,96,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1570

theorem m2857_288 : Upper (D 10) (R 10) [18,68,129,288,288] 13 :=
  permutation_upper _ _ _ [6,72,160,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1632

theorem m2857_320 : Upper (D 10) (R 10) [18,68,129,288,320] 13 :=
  permutation_upper _ _ _ [6,72,192,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1680

theorem m2857_384 : Upper (D 10) (R 10) [18,68,129,288,384] 13 :=
  permutation_upper _ _ _ [6,72,384,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1711

def r2857 : Route 9 := (fun mask => (mask,id))

def c2857 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2857 : Upper (D 10) (R 10) [18,68,129,288] 13 := by
  apply FastRouting.sound _ _ [18,68,129,288] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2857 c2857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2857_40
  · exact m2857_72
  · exact m2857_96
  · exact m2857_136
  · exact m2857_160
  · exact m2857_192
  · exact m2857_264
  · exact m2857_288
  · exact m2857_320
  · exact m2857_384

theorem m2858_40 : Upper (D 10) (R 10) [18,68,129,320,40] 13 :=
  permutation_upper _ _ _ [6,40,80,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1335

theorem m2858_136 : Upper (D 10) (R 10) [18,68,129,320,136] 13 :=
  permutation_upper _ _ _ [6,72,144,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1574

theorem m2858_160 : Upper (D 10) (R 10) [18,68,129,320,160] 13 :=
  permutation_upper _ _ _ [6,72,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1616

theorem m2858_264 : Upper (D 10) (R 10) [18,68,129,320,264] 13 :=
  permutation_upper _ _ _ [6,72,144,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1579

theorem m2858_288 : Upper (D 10) (R 10) [18,68,129,320,288] 13 :=
  permutation_upper _ _ _ [6,72,160,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1633

theorem m2858_384 : Upper (D 10) (R 10) [18,68,129,320,384] 13 :=
  permutation_upper _ _ _ [6,72,384,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1712

def r2858 : Route 9 := (fun mask => (mask,id))

def c2858 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2858 : Upper (D 10) (R 10) [18,68,129,320] 13 := by
  apply FastRouting.sound _ _ [18,68,129,320] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2858 c2858
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2858_40
  · exact m2858_136
  · exact m2858_160
  · exact m2858_264
  · exact m2858_288
  · exact m2858_384

theorem m2859_40 : Upper (D 10) (R 10) [18,68,129,384,40] 13 :=
  permutation_upper _ _ _ [6,40,80,384,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1341

theorem m2859_72 : Upper (D 10) (R 10) [18,68,129,384,72] 13 :=
  permutation_upper _ _ _ [6,72,80,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1542

theorem m2859_96 : Upper (D 10) (R 10) [18,68,129,384,96] 13 :=
  permutation_upper _ _ _ [6,72,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1551

theorem m2859_264 : Upper (D 10) (R 10) [18,68,129,384,264] 13 :=
  permutation_upper _ _ _ [6,72,144,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1583

theorem m2859_288 : Upper (D 10) (R 10) [18,68,129,384,288] 13 :=
  permutation_upper _ _ _ [6,72,160,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1636

theorem m2859_320 : Upper (D 10) (R 10) [18,68,129,384,320] 13 :=
  permutation_upper _ _ _ [6,72,192,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1682

def r2859 : Route 9 := (fun mask => (mask,id))

def c2859 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2859 : Upper (D 10) (R 10) [18,68,129,384] 13 := by
  apply FastRouting.sound _ _ [18,68,129,384] 13 (by decide) (choices 2) [40,72,96,264,288,320] r2859 c2859
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2859_40
  · exact m2859_72
  · exact m2859_96
  · exact m2859_264
  · exact m2859_288
  · exact m2859_320

theorem m2860_96 : Upper (D 10) (R 10) [18,68,136,33,96] 13 :=
  permutation_upper _ _ _ [6,72,96,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1552

theorem m2860_160 : Upper (D 10) (R 10) [18,68,136,33,160] 13 :=
  permutation_upper _ _ _ [6,72,160,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1617

theorem m2860_192 : Upper (D 10) (R 10) [18,68,136,33,192] 13 :=
  permutation_upper _ _ _ [6,72,192,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1674

theorem m2860_288 : Upper (D 10) (R 10) [18,68,136,33,288] 13 :=
  permutation_upper _ _ _ [6,72,160,272,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1637

theorem m2860_320 : Upper (D 10) (R 10) [18,68,136,33,320] 13 :=
  permutation_upper _ _ _ [6,72,192,272,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1683

theorem m2860_384 : Upper (D 10) (R 10) [18,68,136,33,384] 13 :=
  permutation_upper _ _ _ [6,72,384,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1713

def r2860 : Route 9 := (fun mask => (mask,id))

def c2860 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2860 : Upper (D 10) (R 10) [18,68,136,33] 13 := by
  apply FastRouting.sound _ _ [18,68,136,33] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2860 c2860
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2860_96
  · exact m2860_160
  · exact m2860_192
  · exact m2860_288
  · exact m2860_320
  · exact m2860_384

def b2861 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 19 70 140 73 432 416 480 416 416), lower := (rows 19 70 140 73 16 32 64 128 256), losses := [] }

theorem u2861 : Upper (D 10) (R 10) [18,68,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2861 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2862 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 19 70 140 104 433 417 481 417 417), lower := (rows 19 70 140 104 16 32 64 128 256), losses := [] }

theorem u2862 : Upper (D 10) (R 10) [18,68,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2862 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2863_96 : Upper (D 10) (R 10) [18,68,136,257,96] 13 :=
  permutation_upper _ _ _ [6,72,96,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1553

theorem m2863_160 : Upper (D 10) (R 10) [18,68,136,257,160] 13 :=
  permutation_upper _ _ _ [6,72,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1620

theorem m2863_192 : Upper (D 10) (R 10) [18,68,136,257,192] 13 :=
  permutation_upper _ _ _ [6,72,192,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1675

theorem m2863_288 : Upper (D 10) (R 10) [18,68,136,257,288] 13 :=
  permutation_upper _ _ _ [6,72,160,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1640

theorem m2863_320 : Upper (D 10) (R 10) [18,68,136,257,320] 13 :=
  permutation_upper _ _ _ [6,72,192,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1684

theorem m2863_384 : Upper (D 10) (R 10) [18,68,136,257,384] 13 :=
  permutation_upper _ _ _ [6,72,384,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1716

def r2863 : Route 9 := (fun mask => (mask,id))

def c2863 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2863 : Upper (D 10) (R 10) [18,68,136,257] 13 := by
  apply FastRouting.sound _ _ [18,68,136,257] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2863 c2863
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2863_96
  · exact m2863_160
  · exact m2863_192
  · exact m2863_288
  · exact m2863_320
  · exact m2863_384

theorem m2864_33 : Upper (D 10) (R 10) [18,68,136,288,33] 13 :=
  permutation_upper _ _ _ [6,33,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1225

theorem m2864_65 : Upper (D 10) (R 10) [18,68,136,288,65] 13 :=
  permutation_upper _ _ _ [6,65,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1440

theorem m2864_96 : Upper (D 10) (R 10) [18,68,136,288,96] 13 :=
  permutation_upper _ _ _ [6,72,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1554

theorem m2864_129 : Upper (D 10) (R 10) [18,68,136,288,129] 13 :=
  permutation_upper _ _ _ [6,65,136,80,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1457

theorem m2864_160 : Upper (D 10) (R 10) [18,68,136,288,160] 13 :=
  permutation_upper _ _ _ [6,72,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1621

theorem m2864_192 : Upper (D 10) (R 10) [18,68,136,288,192] 13 :=
  permutation_upper _ _ _ [6,72,192,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1676

theorem m2864_257 : Upper (D 10) (R 10) [18,68,136,288,257] 13 :=
  permutation_upper _ _ _ [6,65,136,272,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1465

theorem m2864_288 : Upper (D 10) (R 10) [18,68,136,288,288] 13 :=
  permutation_upper _ _ _ [6,72,160,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1641

theorem m2864_320 : Upper (D 10) (R 10) [18,68,136,288,320] 13 :=
  permutation_upper _ _ _ [6,72,192,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1685

theorem m2864_384 : Upper (D 10) (R 10) [18,68,136,288,384] 13 :=
  permutation_upper _ _ _ [6,72,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1717

def r2864 : Route 9 := (fun mask => (mask,id))

def c2864 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2864 : Upper (D 10) (R 10) [18,68,136,288] 13 := by
  apply FastRouting.sound _ _ [18,68,136,288] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r2864 c2864
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2864_33
  · exact m2864_65
  · exact m2864_96
  · exact m2864_129
  · exact m2864_160
  · exact m2864_192
  · exact m2864_257
  · exact m2864_288
  · exact m2864_320
  · exact m2864_384

def b2865 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 19 70 140 328 433 417 481 417 417), lower := (rows 19 70 140 328 16 32 64 128 256), losses := [] }

theorem u2865 : Upper (D 10) (R 10) [18,68,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2865 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2866_40 : Upper (D 10) (R 10) [18,68,160,33,40] 13 :=
  permutation_upper _ _ _ [6,40,80,33,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1312

theorem m2866_72 : Upper (D 10) (R 10) [18,68,160,33,72] 13 :=
  permutation_upper _ _ _ [6,72,80,33,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1538

theorem m2866_96 : Upper (D 10) (R 10) [18,68,160,33,96] 13 :=
  permutation_upper _ _ _ [6,72,96,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1555

theorem m2866_136 : Upper (D 10) (R 10) [18,68,160,33,136] 13 :=
  permutation_upper _ _ _ [6,72,144,33,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1563

theorem m2866_160 : Upper (D 10) (R 10) [18,68,160,33,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1623

theorem m2866_192 : Upper (D 10) (R 10) [18,68,160,33,192] 13 :=
  permutation_upper _ _ _ [6,72,192,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1677

theorem m2866_264 : Upper (D 10) (R 10) [18,68,160,33,264] 13 :=
  permutation_upper _ _ _ [6,72,144,33,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1566

theorem m2866_288 : Upper (D 10) (R 10) [18,68,160,33,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1647

theorem m2866_320 : Upper (D 10) (R 10) [18,68,160,33,320] 13 :=
  permutation_upper _ _ _ [6,72,192,288,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1686

theorem m2866_384 : Upper (D 10) (R 10) [18,68,160,33,384] 13 :=
  permutation_upper _ _ _ [6,72,384,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1719

def r2866 : Route 9 := (fun mask => (mask,id))

def c2866 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2866 : Upper (D 10) (R 10) [18,68,160,33] 13 := by
  apply FastRouting.sound _ _ [18,68,160,33] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2866 c2866
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2866_40
  · exact m2866_72
  · exact m2866_96
  · exact m2866_136
  · exact m2866_160
  · exact m2866_192
  · exact m2866_264
  · exact m2866_288
  · exact m2866_320
  · exact m2866_384

def b2867 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 19 70 164 73 440 424 488 424 424), lower := (rows 19 70 164 73 16 32 64 128 256), losses := [] }

theorem u2867 : Upper (D 10) (R 10) [18,68,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2867 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2868_9 : Upper (D 10) (R 10) [18,68,160,96,9] 13 :=
  permutation_upper _ _ _ [6,9,80,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1121

theorem m2868_33 : Upper (D 10) (R 10) [18,68,160,96,33] 13 :=
  permutation_upper _ _ _ [6,33,72,160,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1228

theorem m2868_40 : Upper (D 10) (R 10) [18,68,160,96,40] 13 :=
  permutation_upper _ _ _ [6,40,80,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1318

theorem m2868_129 : Upper (D 10) (R 10) [18,68,160,96,129] 13 :=
  permutation_upper _ _ _ [6,65,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1459

theorem m2868_136 : Upper (D 10) (R 10) [18,68,160,96,136] 13 :=
  permutation_upper _ _ _ [6,72,144,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1575

theorem m2868_160 : Upper (D 10) (R 10) [18,68,160,96,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1624

theorem m2868_257 : Upper (D 10) (R 10) [18,68,160,96,257] 13 :=
  permutation_upper _ _ _ [6,65,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1472

theorem m2868_264 : Upper (D 10) (R 10) [18,68,160,96,264] 13 :=
  permutation_upper _ _ _ [6,72,144,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1577

theorem m2868_288 : Upper (D 10) (R 10) [18,68,160,96,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1649

theorem m2868_384 : Upper (D 10) (R 10) [18,68,160,96,384] 13 :=
  permutation_upper _ _ _ [6,72,384,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1721

def r2868 : Route 9 := (fun mask => (mask,id))

def c2868 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2868 : Upper (D 10) (R 10) [18,68,160,96] 13 := by
  apply FastRouting.sound _ _ [18,68,160,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2868 c2868
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2868_9
  · exact m2868_33
  · exact m2868_40
  · exact m2868_129
  · exact m2868_136
  · exact m2868_160
  · exact m2868_257
  · exact m2868_264
  · exact m2868_288
  · exact m2868_384

theorem m2869_40 : Upper (D 10) (R 10) [18,68,160,129,40] 13 :=
  permutation_upper _ _ _ [6,40,80,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1321

theorem m2869_72 : Upper (D 10) (R 10) [18,68,160,129,72] 13 :=
  permutation_upper _ _ _ [6,72,80,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1540

theorem m2869_96 : Upper (D 10) (R 10) [18,68,160,129,96] 13 :=
  permutation_upper _ _ _ [6,72,96,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1556

theorem m2869_264 : Upper (D 10) (R 10) [18,68,160,129,264] 13 :=
  permutation_upper _ _ _ [6,72,144,257,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1581

theorem m2869_288 : Upper (D 10) (R 10) [18,68,160,129,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1653

theorem m2869_320 : Upper (D 10) (R 10) [18,68,160,129,320] 13 :=
  permutation_upper _ _ _ [6,72,192,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1689

def r2869 : Route 9 := (fun mask => (mask,id))

def c2869 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2869 : Upper (D 10) (R 10) [18,68,160,129] 13 := by
  apply FastRouting.sound _ _ [18,68,160,129] 13 (by decide) (choices 2) [40,72,96,264,288,320] r2869 c2869
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2869_40
  · exact m2869_72
  · exact m2869_96
  · exact m2869_264
  · exact m2869_288
  · exact m2869_320

theorem m2870_9 : Upper (D 10) (R 10) [18,68,160,192,9] 13 :=
  permutation_upper _ _ _ [6,9,80,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1129

theorem m2870_33 : Upper (D 10) (R 10) [18,68,160,192,33] 13 :=
  permutation_upper _ _ _ [6,33,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1230

theorem m2870_40 : Upper (D 10) (R 10) [18,68,160,192,40] 13 :=
  permutation_upper _ _ _ [6,40,80,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1334

theorem m2870_257 : Upper (D 10) (R 10) [18,68,160,192,257] 13 :=
  permutation_upper _ _ _ [6,65,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1476

theorem m2870_264 : Upper (D 10) (R 10) [18,68,160,192,264] 13 :=
  permutation_upper _ _ _ [6,72,144,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1585

theorem m2870_288 : Upper (D 10) (R 10) [18,68,160,192,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1655

def r2870 : Route 9 := (fun mask => (mask,id))

def c2870 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2870 : Upper (D 10) (R 10) [18,68,160,192] 13 := by
  apply FastRouting.sound _ _ [18,68,160,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r2870 c2870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2870_9
  · exact m2870_33
  · exact m2870_40
  · exact m2870_257
  · exact m2870_264
  · exact m2870_288

theorem m2871_40 : Upper (D 10) (R 10) [18,68,160,257,40] 13 :=
  permutation_upper _ _ _ [6,40,80,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1323

theorem m2871_72 : Upper (D 10) (R 10) [18,68,160,257,72] 13 :=
  permutation_upper _ _ _ [6,72,80,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1541

theorem m2871_96 : Upper (D 10) (R 10) [18,68,160,257,96] 13 :=
  permutation_upper _ _ _ [6,72,96,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1557

theorem m2871_136 : Upper (D 10) (R 10) [18,68,160,257,136] 13 :=
  permutation_upper _ _ _ [6,72,144,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1576

theorem m2871_160 : Upper (D 10) (R 10) [18,68,160,257,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1625

theorem m2871_192 : Upper (D 10) (R 10) [18,68,160,257,192] 13 :=
  permutation_upper _ _ _ [6,72,192,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1678

theorem m2871_264 : Upper (D 10) (R 10) [18,68,160,257,264] 13 :=
  permutation_upper _ _ _ [6,72,144,65,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1569

theorem m2871_288 : Upper (D 10) (R 10) [18,68,160,257,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1650

theorem m2871_320 : Upper (D 10) (R 10) [18,68,160,257,320] 13 :=
  permutation_upper _ _ _ [6,72,192,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1687

theorem m2871_384 : Upper (D 10) (R 10) [18,68,160,257,384] 13 :=
  permutation_upper _ _ _ [6,72,384,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1722

def r2871 : Route 9 := (fun mask => (mask,id))

def c2871 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2871 : Upper (D 10) (R 10) [18,68,160,257] 13 := by
  apply FastRouting.sound _ _ [18,68,160,257] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2871 c2871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2871_40
  · exact m2871_72
  · exact m2871_96
  · exact m2871_136
  · exact m2871_160
  · exact m2871_192
  · exact m2871_264
  · exact m2871_288
  · exact m2871_320
  · exact m2871_384

theorem m2872_9 : Upper (D 10) (R 10) [18,68,160,288,9] 13 :=
  permutation_upper _ _ _ [6,9,80,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1126

theorem m2872_33 : Upper (D 10) (R 10) [18,68,160,288,33] 13 :=
  permutation_upper _ _ _ [6,33,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1231

theorem m2872_40 : Upper (D 10) (R 10) [18,68,160,288,40] 13 :=
  permutation_upper _ _ _ [6,40,80,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1330

theorem m2872_65 : Upper (D 10) (R 10) [18,68,160,288,65] 13 :=
  permutation_upper _ _ _ [6,65,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1441

theorem m2872_72 : Upper (D 10) (R 10) [18,68,160,288,72] 13 :=
  permutation_upper _ _ _ [6,72,80,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1543

theorem m2872_96 : Upper (D 10) (R 10) [18,68,160,288,96] 13 :=
  permutation_upper _ _ _ [6,72,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1558

theorem m2872_129 : Upper (D 10) (R 10) [18,68,160,288,129] 13 :=
  permutation_upper _ _ _ [6,65,136,96,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1460

theorem m2872_136 : Upper (D 10) (R 10) [18,68,160,288,136] 13 :=
  permutation_upper _ _ _ [6,72,144,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1577

theorem m2872_160 : Upper (D 10) (R 10) [18,68,160,288,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1626

theorem m2872_192 : Upper (D 10) (R 10) [18,68,160,288,192] 13 :=
  permutation_upper _ _ _ [6,72,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1679

theorem m2872_257 : Upper (D 10) (R 10) [18,68,160,288,257] 13 :=
  permutation_upper _ _ _ [6,65,136,288,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1471

theorem m2872_264 : Upper (D 10) (R 10) [18,68,160,288,264] 13 :=
  permutation_upper _ _ _ [6,72,144,96,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1571

theorem m2872_288 : Upper (D 10) (R 10) [18,68,160,288,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1651

theorem m2872_320 : Upper (D 10) (R 10) [18,68,160,288,320] 13 :=
  permutation_upper _ _ _ [6,72,192,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1688

theorem m2872_384 : Upper (D 10) (R 10) [18,68,160,288,384] 13 :=
  permutation_upper _ _ _ [6,72,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1723

def r2872 : Route 9 := (fun mask => (mask,id))

def c2872 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2872 : Upper (D 10) (R 10) [18,68,160,288] 13 := by
  apply FastRouting.sound _ _ [18,68,160,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r2872 c2872
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2872_9
  · exact m2872_33
  · exact m2872_40
  · exact m2872_65
  · exact m2872_72
  · exact m2872_96
  · exact m2872_129
  · exact m2872_136
  · exact m2872_160
  · exact m2872_192
  · exact m2872_257
  · exact m2872_264
  · exact m2872_288
  · exact m2872_320
  · exact m2872_384

theorem m2873_9 : Upper (D 10) (R 10) [18,68,160,320,9] 13 :=
  permutation_upper _ _ _ [6,9,80,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1130

theorem m2873_33 : Upper (D 10) (R 10) [18,68,160,320,33] 13 :=
  permutation_upper _ _ _ [6,33,72,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1232

theorem m2873_40 : Upper (D 10) (R 10) [18,68,160,320,40] 13 :=
  permutation_upper _ _ _ [6,40,80,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1336

theorem m2873_129 : Upper (D 10) (R 10) [18,68,160,320,129] 13 :=
  permutation_upper _ _ _ [6,65,136,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1461

theorem m2873_136 : Upper (D 10) (R 10) [18,68,160,320,136] 13 :=
  permutation_upper _ _ _ [6,72,144,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1578

theorem m2873_160 : Upper (D 10) (R 10) [18,68,160,320,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1627

theorem m2873_257 : Upper (D 10) (R 10) [18,68,160,320,257] 13 :=
  permutation_upper _ _ _ [6,65,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1473

theorem m2873_264 : Upper (D 10) (R 10) [18,68,160,320,264] 13 :=
  permutation_upper _ _ _ [6,72,144,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1580

theorem m2873_288 : Upper (D 10) (R 10) [18,68,160,320,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1652

theorem m2873_384 : Upper (D 10) (R 10) [18,68,160,320,384] 13 :=
  permutation_upper _ _ _ [6,72,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1724

def r2873 : Route 9 := (fun mask => (mask,id))

def c2873 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2873 : Upper (D 10) (R 10) [18,68,160,320] 13 := by
  apply FastRouting.sound _ _ [18,68,160,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2873 c2873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2873_9
  · exact m2873_33
  · exact m2873_40
  · exact m2873_129
  · exact m2873_136
  · exact m2873_160
  · exact m2873_257
  · exact m2873_264
  · exact m2873_288
  · exact m2873_384

theorem m2874_9 : Upper (D 10) (R 10) [18,68,160,384,9] 13 :=
  permutation_upper _ _ _ [6,9,80,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1133

theorem m2874_33 : Upper (D 10) (R 10) [18,68,160,384,33] 13 :=
  permutation_upper _ _ _ [6,33,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1233

theorem m2874_40 : Upper (D 10) (R 10) [18,68,160,384,40] 13 :=
  permutation_upper _ _ _ [6,40,80,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1342

theorem m2874_65 : Upper (D 10) (R 10) [18,68,160,384,65] 13 :=
  permutation_upper _ _ _ [6,65,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1442

theorem m2874_72 : Upper (D 10) (R 10) [18,68,160,384,72] 13 :=
  permutation_upper _ _ _ [6,72,80,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1544

theorem m2874_96 : Upper (D 10) (R 10) [18,68,160,384,96] 13 :=
  permutation_upper _ _ _ [6,72,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1559

theorem m2874_257 : Upper (D 10) (R 10) [18,68,160,384,257] 13 :=
  permutation_upper _ _ _ [6,65,136,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1475

theorem m2874_264 : Upper (D 10) (R 10) [18,68,160,384,264] 13 :=
  permutation_upper _ _ _ [6,72,144,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1586

theorem m2874_288 : Upper (D 10) (R 10) [18,68,160,384,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1656

theorem m2874_320 : Upper (D 10) (R 10) [18,68,160,384,320] 13 :=
  permutation_upper _ _ _ [6,72,192,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1690

def r2874 : Route 9 := (fun mask => (mask,id))

def c2874 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2874 : Upper (D 10) (R 10) [18,68,160,384] 13 := by
  apply FastRouting.sound _ _ [18,68,160,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r2874 c2874
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2874_9
  · exact m2874_33
  · exact m2874_40
  · exact m2874_65
  · exact m2874_72
  · exact m2874_96
  · exact m2874_257
  · exact m2874_264
  · exact m2874_288
  · exact m2874_320

def b2875 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 196 41 440 424 488 424 424), lower := (rows 19 70 196 41 16 32 64 128 256), losses := [] }

theorem u2875 : Upper (D 10) (R 10) [18,68,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2875 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2876 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 196 137 312 296 360 424 296), lower := (rows 19 70 196 137 16 32 64 128 256), losses := [] }

theorem u2876 : Upper (D 10) (R 10) [18,68,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2876 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2877 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 196 168 313 297 361 425 297), lower := (rows 19 70 196 168 16 32 64 128 256), losses := [] }

theorem u2877 : Upper (D 10) (R 10) [18,68,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2877 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2878 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 196 265 440 424 488 424 424), lower := (rows 19 70 196 265 16 32 64 128 256), losses := [] }

theorem u2878 : Upper (D 10) (R 10) [18,68,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2878 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2879 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 19 70 196 296 441 425 489 425 425), lower := (rows 19 70 196 296 16 32 64 128 256), losses := [] }

theorem u2879 : Upper (D 10) (R 10) [18,68,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2879 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2879
end Delivery.IrregularNine14.P10
