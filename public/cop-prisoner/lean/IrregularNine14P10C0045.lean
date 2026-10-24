import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0019
import IrregularNine14P10C0026
import IrregularNine14P10C0027
import IrregularNine14P10C0028
import IrregularNine14P10C0029

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2700 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 41 432 432 496 432 432), lower := (rows 7 74 196 41 16 32 64 128 256), losses := [] }

theorem u2700 : Upper (D 10) (R 10) [6,72,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2700 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2701 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 11, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 74 196 137 304 304 368 432 304), lower := (rows 7 74 196 137 16 32 64 128 256), losses := [] }

theorem u2701 : Upper (D 10) (R 10) [6,72,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2701 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2702 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 168 305 305 369 433 305), lower := (rows 7 74 196 168 16 32 64 128 256), losses := [] }

theorem u2702 : Upper (D 10) (R 10) [6,72,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2702 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2703 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 265 432 432 496 432 432), lower := (rows 7 74 196 265 16 32 64 128 256), losses := [] }

theorem u2703 : Upper (D 10) (R 10) [6,72,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2703 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2704 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 296 433 433 497 433 433), lower := (rows 7 74 196 296 16 32 64 128 256), losses := [] }

theorem u2704 : Upper (D 10) (R 10) [6,72,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2704 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2705 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 392 305 305 369 433 305), lower := (rows 7 74 196 392 16 32 64 128 256), losses := [] }

theorem u2705 : Upper (D 10) (R 10) [6,72,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2705 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2706_96 : Upper (D 10) (R 10) [6,72,384,17,96] 13 :=
  permutation_upper _ _ _ [6,24,96,65,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1172

theorem m2706_160 : Upper (D 10) (R 10) [6,72,384,17,160] 13 :=
  permutation_upper _ _ _ [6,24,96,129,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1179

theorem m2706_192 : Upper (D 10) (R 10) [6,72,384,17,192] 13 :=
  permutation_upper _ _ _ [6,24,192,65,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1194

theorem m2706_384 : Upper (D 10) (R 10) [6,72,384,17,384] 13 :=
  permutation_upper _ _ _ [6,24,192,192,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1199

def r2706 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2706 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2706 : Upper (D 10) (R 10) [6,72,384,17] 13 := by
  apply FastRouting.sound _ _ [6,72,384,17] 13 (by decide) (choices 2) [96,160,192,384] r2706 c2706
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2706_96
  · exact m2706_160
  · exact m2706_192
  · exact m2706_384

def r2707 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2707 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2707 : Upper (D 10) (R 10) [6,72,384,33] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33] 13 (by decide) (choices 2) [96,160,192,384] r2707 c2707
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1694
  · exact u1695
  · exact u1696
  · exact u1697

def r2708 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2708 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2708 : Upper (D 10) (R 10) [6,72,384,48] 13 := by
  apply FastRouting.sound _ _ [6,72,384,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r2708 c2708
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1698
  · exact u1699
  · exact u1700
  · exact u1701
  · exact u1702
  · exact u1703
  · exact u1704

def b2709 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 73 432 432 496 432 432), lower := (rows 7 74 388 73 16 32 64 128 256), losses := [] }

theorem u2709 : Upper (D 10) (R 10) [6,72,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2709 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2710 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 88 433 417 481 417 417), lower := (rows 7 74 388 88 16 32 64 128 256), losses := [] }

theorem u2710 : Upper (D 10) (R 10) [6,72,384,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2710 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2711 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 104 433 433 497 433 433), lower := (rows 7 74 388 104 16 32 64 128 256), losses := [] }

theorem u2711 : Upper (D 10) (R 10) [6,72,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2711 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2712 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 388 137 368 368 368 496 368), lower := (rows 7 74 388 137 16 32 64 128 256), losses := [] }

theorem u2712 : Upper (D 10) (R 10) [6,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2712 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2713 : Route 9 := (fun mask => (mask,id))

def c2713 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2713 : Upper (D 10) (R 10) [6,72,384,144] 13 := by
  apply FastRouting.sound _ _ [6,72,384,144] 13 (by decide) (choices 2) [33,65,96,257,288,320] r2713 c2713
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1713
  · exact u1714
  · exact u1715
  · exact u1716
  · exact u1717
  · exact u1718

def r2714 : Route 9 := (fun mask => (mask,id))

def c2714 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2714 : Upper (D 10) (R 10) [6,72,384,160] 13 := by
  apply FastRouting.sound _ _ [6,72,384,160] 13 (by decide) (choices 2) [33,65,96,257,288,320] r2714 c2714
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1719
  · exact u1720
  · exact u1721
  · exact u1722
  · exact u1723
  · exact u1724

def b2715 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 200 305 305 369 433 305), lower := (rows 7 74 388 200 16 32 64 128 256), losses := [] }

theorem u2715 : Upper (D 10) (R 10) [6,72,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2715 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2716 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 74 388 392 113 113 113 241 369), lower := (rows 7 74 388 392 16 32 64 128 256), losses := [] }

theorem u2716 : Upper (D 10) (R 10) [6,72,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2716 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2717 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 100 41 440 424 488 424 424), lower := (rows 7 82 100 41 16 32 64 128 256), losses := [] }

theorem u2717 : Upper (D 10) (R 10) [6,80,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2717 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2718 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 100 137 440 424 488 424 424), lower := (rows 7 82 100 137 16 32 64 128 256), losses := [] }

theorem u2718 : Upper (D 10) (R 10) [6,80,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2718 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2719 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 100 168 441 425 489 425 425), lower := (rows 7 82 100 168 16 32 64 128 256), losses := [] }

theorem u2719 : Upper (D 10) (R 10) [6,80,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2719 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2720 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 100 392 441 425 489 425 425), lower := (rows 7 82 100 392 16 32 64 128 256), losses := [] }

theorem u2720 : Upper (D 10) (R 10) [6,80,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2720 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2721_40 : Upper (D 10) (R 10) [6,80,160,33,40] 13 :=
  permutation_upper _ _ _ [6,72,160,48,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1594

theorem m2721_72 : Upper (D 10) (R 10) [6,80,160,33,72] 13 :=
  permutation_upper _ _ _ [6,72,160,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1606

theorem m2721_96 : Upper (D 10) (R 10) [6,80,160,33,96] 13 :=
  permutation_upper _ _ _ [6,72,160,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1610

theorem m2721_136 : Upper (D 10) (R 10) [6,80,160,33,136] 13 :=
  permutation_upper _ _ _ [6,72,160,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1617

theorem m2721_160 : Upper (D 10) (R 10) [6,80,160,33,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1623

theorem m2721_192 : Upper (D 10) (R 10) [6,80,160,33,192] 13 :=
  permutation_upper _ _ _ [6,72,160,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1628

theorem m2721_264 : Upper (D 10) (R 10) [6,80,160,33,264] 13 :=
  permutation_upper _ _ _ [6,72,160,272,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1637

theorem m2721_288 : Upper (D 10) (R 10) [6,80,160,33,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1647

theorem m2721_320 : Upper (D 10) (R 10) [6,80,160,33,320] 13 :=
  permutation_upper _ _ _ [6,72,160,320,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1657

theorem m2721_384 : Upper (D 10) (R 10) [6,80,160,33,384] 13 :=
  permutation_upper _ _ _ [6,72,160,384,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1661

def r2721 : Route 9 := (fun mask => (mask,id))

def c2721 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2721 : Upper (D 10) (R 10) [6,80,160,33] 13 := by
  apply FastRouting.sound _ _ [6,80,160,33] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2721 c2721
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2721_40
  · exact m2721_72
  · exact m2721_96
  · exact m2721_136
  · exact m2721_160
  · exact m2721_192
  · exact m2721_264
  · exact m2721_288
  · exact m2721_320
  · exact m2721_384

def b2722 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 82 164 73 440 424 488 424 424), lower := (rows 7 82 164 73 16 32 64 128 256), losses := [] }

theorem u2722 : Upper (D 10) (R 10) [6,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2722 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2723_9 : Upper (D 10) (R 10) [6,80,160,96,9] 13 :=
  permutation_upper _ _ _ [6,24,96,65,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1171

theorem m2723_33 : Upper (D 10) (R 10) [6,80,160,96,33] 13 :=
  permutation_upper _ _ _ [6,72,160,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1588

theorem m2723_40 : Upper (D 10) (R 10) [6,80,160,96,40] 13 :=
  permutation_upper _ _ _ [6,72,160,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1596

theorem m2723_129 : Upper (D 10) (R 10) [6,80,160,96,129] 13 :=
  permutation_upper _ _ _ [6,72,160,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1614

theorem m2723_136 : Upper (D 10) (R 10) [6,80,160,96,136] 13 :=
  permutation_upper _ _ _ [6,72,160,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1619

theorem m2723_160 : Upper (D 10) (R 10) [6,80,160,96,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1624

theorem m2723_257 : Upper (D 10) (R 10) [6,80,160,96,257] 13 :=
  permutation_upper _ _ _ [6,72,160,257,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1631

theorem m2723_264 : Upper (D 10) (R 10) [6,80,160,96,264] 13 :=
  permutation_upper _ _ _ [6,72,160,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1639

theorem m2723_288 : Upper (D 10) (R 10) [6,80,160,96,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1649

theorem m2723_384 : Upper (D 10) (R 10) [6,80,160,96,384] 13 :=
  permutation_upper _ _ _ [6,72,160,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1663

def r2723 : Route 9 := (fun mask => (mask,id))

def c2723 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2723 : Upper (D 10) (R 10) [6,80,160,96] 13 := by
  apply FastRouting.sound _ _ [6,80,160,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2723 c2723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2723_9
  · exact m2723_33
  · exact m2723_40
  · exact m2723_129
  · exact m2723_136
  · exact m2723_160
  · exact m2723_257
  · exact m2723_264
  · exact m2723_288
  · exact m2723_384

def b2724 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 82 164 137 376 360 360 488 360), lower := (rows 7 82 164 137 16 32 64 128 256), losses := [] }

theorem u2724 : Upper (D 10) (R 10) [6,80,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2724 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2725 : PairBound 9 := { available := 361, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 82 164 168 377 361 361 489 361), lower := (rows 7 82 164 168 16 32 64 128 256), losses := [] }

theorem u2725 : Upper (D 10) (R 10) [6,80,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2725 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2726_9 : Upper (D 10) (R 10) [6,80,160,192,9] 13 :=
  permutation_upper _ _ _ [6,24,192,65,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1192

theorem m2726_33 : Upper (D 10) (R 10) [6,80,160,192,33] 13 :=
  permutation_upper _ _ _ [6,72,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1590

theorem m2726_40 : Upper (D 10) (R 10) [6,80,160,192,40] 13 :=
  permutation_upper _ _ _ [6,72,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1599

theorem m2726_257 : Upper (D 10) (R 10) [6,80,160,192,257] 13 :=
  permutation_upper _ _ _ [6,72,160,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1633

theorem m2726_264 : Upper (D 10) (R 10) [6,80,160,192,264] 13 :=
  permutation_upper _ _ _ [6,72,160,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1642

theorem m2726_288 : Upper (D 10) (R 10) [6,80,160,192,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1652

def r2726 : Route 9 := (fun mask => (mask,id))

def c2726 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2726 : Upper (D 10) (R 10) [6,80,160,192] 13 := by
  apply FastRouting.sound _ _ [6,80,160,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r2726 c2726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2726_9
  · exact m2726_33
  · exact m2726_40
  · exact m2726_257
  · exact m2726_264
  · exact m2726_288

theorem m2727_40 : Upper (D 10) (R 10) [6,80,160,257,40] 13 :=
  permutation_upper _ _ _ [6,72,160,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1600

theorem m2727_72 : Upper (D 10) (R 10) [6,80,160,257,72] 13 :=
  permutation_upper _ _ _ [6,72,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1607

theorem m2727_96 : Upper (D 10) (R 10) [6,80,160,257,96] 13 :=
  permutation_upper _ _ _ [6,72,160,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1611

theorem m2727_136 : Upper (D 10) (R 10) [6,80,160,257,136] 13 :=
  permutation_upper _ _ _ [6,72,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1620

theorem m2727_160 : Upper (D 10) (R 10) [6,80,160,257,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1625

theorem m2727_192 : Upper (D 10) (R 10) [6,80,160,257,192] 13 :=
  permutation_upper _ _ _ [6,72,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1629

theorem m2727_264 : Upper (D 10) (R 10) [6,80,160,257,264] 13 :=
  permutation_upper _ _ _ [6,72,160,272,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1643

theorem m2727_288 : Upper (D 10) (R 10) [6,80,160,257,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1653

theorem m2727_320 : Upper (D 10) (R 10) [6,80,160,257,320] 13 :=
  permutation_upper _ _ _ [6,72,160,320,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1658

theorem m2727_384 : Upper (D 10) (R 10) [6,80,160,257,384] 13 :=
  permutation_upper _ _ _ [6,72,160,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1664

def r2727 : Route 9 := (fun mask => (mask,id))

def c2727 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2727 : Upper (D 10) (R 10) [6,80,160,257] 13 := by
  apply FastRouting.sound _ _ [6,80,160,257] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2727 c2727
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2727_40
  · exact m2727_72
  · exact m2727_96
  · exact m2727_136
  · exact m2727_160
  · exact m2727_192
  · exact m2727_264
  · exact m2727_288
  · exact m2727_320
  · exact m2727_384

theorem m2728_9 : Upper (D 10) (R 10) [6,80,160,288,9] 13 :=
  permutation_upper _ _ _ [6,24,96,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1178

theorem m2728_33 : Upper (D 10) (R 10) [6,80,160,288,33] 13 :=
  permutation_upper _ _ _ [6,72,160,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1591

theorem m2728_40 : Upper (D 10) (R 10) [6,80,160,288,40] 13 :=
  permutation_upper _ _ _ [6,72,160,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1601

theorem m2728_65 : Upper (D 10) (R 10) [6,80,160,288,65] 13 :=
  permutation_upper _ _ _ [6,72,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1604

theorem m2728_72 : Upper (D 10) (R 10) [6,80,160,288,72] 13 :=
  permutation_upper _ _ _ [6,72,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1608

theorem m2728_96 : Upper (D 10) (R 10) [6,80,160,288,96] 13 :=
  permutation_upper _ _ _ [6,72,160,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1612

theorem m2728_129 : Upper (D 10) (R 10) [6,80,160,288,129] 13 :=
  permutation_upper _ _ _ [6,72,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1615

theorem m2728_136 : Upper (D 10) (R 10) [6,80,160,288,136] 13 :=
  permutation_upper _ _ _ [6,72,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1621

theorem m2728_160 : Upper (D 10) (R 10) [6,80,160,288,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1626

theorem m2728_192 : Upper (D 10) (R 10) [6,80,160,288,192] 13 :=
  permutation_upper _ _ _ [6,72,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1630

theorem m2728_257 : Upper (D 10) (R 10) [6,80,160,288,257] 13 :=
  permutation_upper _ _ _ [6,72,160,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1634

theorem m2728_264 : Upper (D 10) (R 10) [6,80,160,288,264] 13 :=
  permutation_upper _ _ _ [6,72,160,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1644

theorem m2728_288 : Upper (D 10) (R 10) [6,80,160,288,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1654

theorem m2728_320 : Upper (D 10) (R 10) [6,80,160,288,320] 13 :=
  permutation_upper _ _ _ [6,72,160,320,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1659

theorem m2728_384 : Upper (D 10) (R 10) [6,80,160,288,384] 13 :=
  permutation_upper _ _ _ [6,72,160,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1665

def r2728 : Route 9 := (fun mask => (mask,id))

def c2728 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2728 : Upper (D 10) (R 10) [6,80,160,288] 13 := by
  apply FastRouting.sound _ _ [6,80,160,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r2728 c2728
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2728_9
  · exact m2728_33
  · exact m2728_40
  · exact m2728_65
  · exact m2728_72
  · exact m2728_96
  · exact m2728_129
  · exact m2728_136
  · exact m2728_160
  · exact m2728_192
  · exact m2728_257
  · exact m2728_264
  · exact m2728_288
  · exact m2728_320
  · exact m2728_384

theorem m2729_9 : Upper (D 10) (R 10) [6,80,160,320,9] 13 :=
  permutation_upper _ _ _ [6,24,192,65,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1193

theorem m2729_33 : Upper (D 10) (R 10) [6,80,160,320,33] 13 :=
  permutation_upper _ _ _ [6,72,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1592

theorem m2729_40 : Upper (D 10) (R 10) [6,80,160,320,40] 13 :=
  permutation_upper _ _ _ [6,72,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1602

theorem m2729_129 : Upper (D 10) (R 10) [6,80,160,320,129] 13 :=
  permutation_upper _ _ _ [6,72,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1616

theorem m2729_136 : Upper (D 10) (R 10) [6,80,160,320,136] 13 :=
  permutation_upper _ _ _ [6,72,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1622

theorem m2729_160 : Upper (D 10) (R 10) [6,80,160,320,160] 13 :=
  permutation_upper _ _ _ [6,72,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1627

theorem m2729_257 : Upper (D 10) (R 10) [6,80,160,320,257] 13 :=
  permutation_upper _ _ _ [6,72,160,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1635

theorem m2729_264 : Upper (D 10) (R 10) [6,80,160,320,264] 13 :=
  permutation_upper _ _ _ [6,72,160,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1645

theorem m2729_288 : Upper (D 10) (R 10) [6,80,160,320,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1655

theorem m2729_384 : Upper (D 10) (R 10) [6,80,160,320,384] 13 :=
  permutation_upper _ _ _ [6,72,160,384,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1666

def r2729 : Route 9 := (fun mask => (mask,id))

def c2729 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2729 : Upper (D 10) (R 10) [6,80,160,320] 13 := by
  apply FastRouting.sound _ _ [6,80,160,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2729 c2729
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2729_9
  · exact m2729_33
  · exact m2729_40
  · exact m2729_129
  · exact m2729_136
  · exact m2729_160
  · exact m2729_257
  · exact m2729_264
  · exact m2729_288
  · exact m2729_384

theorem m2730_9 : Upper (D 10) (R 10) [6,80,160,384,9] 13 :=
  permutation_upper _ _ _ [6,24,192,96,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1196

theorem m2730_33 : Upper (D 10) (R 10) [6,80,160,384,33] 13 :=
  permutation_upper _ _ _ [6,72,160,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1593

theorem m2730_40 : Upper (D 10) (R 10) [6,80,160,384,40] 13 :=
  permutation_upper _ _ _ [6,72,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1603

theorem m2730_65 : Upper (D 10) (R 10) [6,80,160,384,65] 13 :=
  permutation_upper _ _ _ [6,72,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1605

theorem m2730_72 : Upper (D 10) (R 10) [6,80,160,384,72] 13 :=
  permutation_upper _ _ _ [6,72,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1609

theorem m2730_96 : Upper (D 10) (R 10) [6,80,160,384,96] 13 :=
  permutation_upper _ _ _ [6,72,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1613

theorem m2730_257 : Upper (D 10) (R 10) [6,80,160,384,257] 13 :=
  permutation_upper _ _ _ [6,72,160,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1636

theorem m2730_264 : Upper (D 10) (R 10) [6,80,160,384,264] 13 :=
  permutation_upper _ _ _ [6,72,160,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1646

theorem m2730_288 : Upper (D 10) (R 10) [6,80,160,384,288] 13 :=
  permutation_upper _ _ _ [6,72,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1656

theorem m2730_320 : Upper (D 10) (R 10) [6,80,160,384,320] 13 :=
  permutation_upper _ _ _ [6,72,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1660

def r2730 : Route 9 := (fun mask => (mask,id))

def c2730 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2730 : Upper (D 10) (R 10) [6,80,160,384] 13 := by
  apply FastRouting.sound _ _ [6,80,160,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r2730 c2730
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2730_9
  · exact m2730_33
  · exact m2730_40
  · exact m2730_65
  · exact m2730_72
  · exact m2730_96
  · exact m2730_257
  · exact m2730_264
  · exact m2730_288
  · exact m2730_320

def b2731 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 196 41 440 424 488 424 424), lower := (rows 7 82 196 41 16 32 64 128 256), losses := [] }

theorem u2731 : Upper (D 10) (R 10) [6,80,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2731 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2732 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 196 137 312 296 360 424 296), lower := (rows 7 82 196 137 16 32 64 128 256), losses := [] }

theorem u2732 : Upper (D 10) (R 10) [6,80,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2732 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2733 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 196 168 313 297 361 425 297), lower := (rows 7 82 196 168 16 32 64 128 256), losses := [] }

theorem u2733 : Upper (D 10) (R 10) [6,80,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2733 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2734 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 196 265 440 424 488 424 424), lower := (rows 7 82 196 265 16 32 64 128 256), losses := [] }

theorem u2734 : Upper (D 10) (R 10) [6,80,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2734 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2735 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 196 296 441 425 489 425 425), lower := (rows 7 82 196 296 16 32 64 128 256), losses := [] }

theorem u2735 : Upper (D 10) (R 10) [6,80,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2735 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2736 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 82 196 392 313 297 361 425 297), lower := (rows 7 82 196 392 16 32 64 128 256), losses := [] }

theorem u2736 : Upper (D 10) (R 10) [6,80,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2736 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2737_40 : Upper (D 10) (R 10) [6,80,384,33,40] 13 :=
  permutation_upper _ _ _ [6,72,384,48,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1698

theorem m2737_72 : Upper (D 10) (R 10) [6,80,384,33,72] 13 :=
  permutation_upper _ _ _ [6,72,384,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1706

theorem m2737_96 : Upper (D 10) (R 10) [6,80,384,33,96] 13 :=
  permutation_upper _ _ _ [6,72,384,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1708

theorem m2737_136 : Upper (D 10) (R 10) [6,80,384,33,136] 13 :=
  permutation_upper _ _ _ [6,72,384,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1713

theorem m2737_160 : Upper (D 10) (R 10) [6,80,384,33,160] 13 :=
  permutation_upper _ _ _ [6,72,384,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1719

theorem m2737_192 : Upper (D 10) (R 10) [6,80,384,33,192] 13 :=
  permutation_upper _ _ _ [6,72,384,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1725

theorem m2737_384 : Upper (D 10) (R 10) [6,80,384,33,384] 13 :=
  permutation_upper _ _ _ [6,72,384,384,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1727

def r2737 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2737 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2737 : Upper (D 10) (R 10) [6,80,384,33] 13 := by
  apply FastRouting.sound _ _ [6,80,384,33] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r2737 c2737
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2737_40
  · exact m2737_72
  · exact m2737_96
  · exact m2737_136
  · exact m2737_160
  · exact m2737_192
  · exact m2737_384

def b2738 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 82 388 73 440 424 488 424 424), lower := (rows 7 82 388 73 16 32 64 128 256), losses := [] }

theorem u2738 : Upper (D 10) (R 10) [6,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2738 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2739_9 : Upper (D 10) (R 10) [6,80,384,96,9] 13 :=
  permutation_upper _ _ _ [6,24,96,65,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1172

theorem m2739_33 : Upper (D 10) (R 10) [6,80,384,96,33] 13 :=
  permutation_upper _ _ _ [6,72,384,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1694

theorem m2739_40 : Upper (D 10) (R 10) [6,80,384,96,40] 13 :=
  permutation_upper _ _ _ [6,72,384,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1700

theorem m2739_129 : Upper (D 10) (R 10) [6,80,384,96,129] 13 :=
  permutation_upper _ _ _ [6,72,384,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1710

theorem m2739_136 : Upper (D 10) (R 10) [6,80,384,96,136] 13 :=
  permutation_upper _ _ _ [6,72,384,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1715

theorem m2739_160 : Upper (D 10) (R 10) [6,80,384,96,160] 13 :=
  permutation_upper _ _ _ [6,72,384,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1721

theorem m2739_384 : Upper (D 10) (R 10) [6,80,384,96,384] 13 :=
  permutation_upper _ _ _ [6,72,384,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1728

def r2739 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2739 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2739 : Upper (D 10) (R 10) [6,80,384,96] 13 := by
  apply FastRouting.sound _ _ [6,80,384,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,384] r2739 c2739
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2739_9
  · exact m2739_33
  · exact m2739_40
  · exact m2739_129
  · exact m2739_136
  · exact m2739_160
  · exact m2739_384

def b2740 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 82 388 137 376 360 360 488 360), lower := (rows 7 82 388 137 16 32 64 128 256), losses := [] }

theorem u2740 : Upper (D 10) (R 10) [6,80,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2740 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2741_9 : Upper (D 10) (R 10) [6,80,384,160,9] 13 :=
  permutation_upper _ _ _ [6,24,96,129,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1179

theorem m2741_33 : Upper (D 10) (R 10) [6,80,384,160,33] 13 :=
  permutation_upper _ _ _ [6,72,384,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1695

theorem m2741_40 : Upper (D 10) (R 10) [6,80,384,160,40] 13 :=
  permutation_upper _ _ _ [6,72,384,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1702

theorem m2741_65 : Upper (D 10) (R 10) [6,80,384,160,65] 13 :=
  permutation_upper _ _ _ [6,72,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1705

theorem m2741_72 : Upper (D 10) (R 10) [6,80,384,160,72] 13 :=
  permutation_upper _ _ _ [6,72,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1707

theorem m2741_96 : Upper (D 10) (R 10) [6,80,384,160,96] 13 :=
  permutation_upper _ _ _ [6,72,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1709

theorem m2741_257 : Upper (D 10) (R 10) [6,80,384,160,257] 13 :=
  permutation_upper _ _ _ [6,72,384,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1711

theorem m2741_264 : Upper (D 10) (R 10) [6,80,384,160,264] 13 :=
  permutation_upper _ _ _ [6,72,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1717

theorem m2741_288 : Upper (D 10) (R 10) [6,80,384,160,288] 13 :=
  permutation_upper _ _ _ [6,72,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1723

theorem m2741_320 : Upper (D 10) (R 10) [6,80,384,160,320] 13 :=
  permutation_upper _ _ _ [6,72,384,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1726

def r2741 : Route 9 := (fun mask => (mask,id))

def c2741 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u2741 : Upper (D 10) (R 10) [6,80,384,160] 13 := by
  apply FastRouting.sound _ _ [6,80,384,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r2741 c2741
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2741_9
  · exact m2741_33
  · exact m2741_40
  · exact m2741_65
  · exact m2741_72
  · exact m2741_96
  · exact m2741_257
  · exact m2741_264
  · exact m2741_288
  · exact m2741_320

theorem m2742_9 : Upper (D 10) (R 10) [6,80,384,192,9] 13 :=
  permutation_upper _ _ _ [6,24,192,65,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1194

theorem m2742_33 : Upper (D 10) (R 10) [6,80,384,192,33] 13 :=
  permutation_upper _ _ _ [6,72,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1696

theorem m2742_40 : Upper (D 10) (R 10) [6,80,384,192,40] 13 :=
  permutation_upper _ _ _ [6,72,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1703

theorem m2742_257 : Upper (D 10) (R 10) [6,80,384,192,257] 13 :=
  permutation_upper _ _ _ [6,72,384,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1712

theorem m2742_264 : Upper (D 10) (R 10) [6,80,384,192,264] 13 :=
  permutation_upper _ _ _ [6,72,384,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1718

theorem m2742_288 : Upper (D 10) (R 10) [6,80,384,192,288] 13 :=
  permutation_upper _ _ _ [6,72,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1724

def r2742 : Route 9 := (fun mask => (mask,id))

def c2742 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2742 : Upper (D 10) (R 10) [6,80,384,192] 13 := by
  apply FastRouting.sound _ _ [6,80,384,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r2742 c2742
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2742_9
  · exact m2742_33
  · exact m2742_40
  · exact m2742_257
  · exact m2742_264
  · exact m2742_288

def b2743 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 82 388 392 121 105 105 233 361), lower := (rows 7 82 388 392 16 32 64 128 256), losses := [] }

theorem u2743 : Upper (D 10) (R 10) [6,80,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2743 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2744 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 41 408 440 472 408 408), lower := (rows 7 98 100 41 16 32 64 128 256), losses := [] }

theorem u2744 : Upper (D 10) (R 10) [6,96,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2744 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2745 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 137 440 440 504 440 440), lower := (rows 7 98 100 137 16 32 64 128 256), losses := [] }

theorem u2745 : Upper (D 10) (R 10) [6,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2745 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2746 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 168 409 441 473 409 409), lower := (rows 7 98 100 168 16 32 64 128 256), losses := [] }

theorem u2746 : Upper (D 10) (R 10) [6,96,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2746 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2747 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 392 441 441 505 441 441), lower := (rows 7 98 100 392 16 32 64 128 256), losses := [] }

theorem u2747 : Upper (D 10) (R 10) [6,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2747 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2748_40 : Upper (D 10) (R 10) [6,96,160,17,40] 13 :=
  permutation_upper _ _ _ [6,24,33,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1153

theorem m2748_72 : Upper (D 10) (R 10) [6,96,160,17,72] 13 :=
  permutation_upper _ _ _ [6,24,65,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1158

theorem m2748_96 : Upper (D 10) (R 10) [6,96,160,17,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1174

theorem m2748_136 : Upper (D 10) (R 10) [6,96,160,17,136] 13 :=
  permutation_upper _ _ _ [6,24,65,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1158

theorem m2748_160 : Upper (D 10) (R 10) [6,96,160,17,160] 13 :=
  permutation_upper _ _ _ [6,24,96,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1174

theorem m2748_192 : Upper (D 10) (R 10) [6,96,160,17,192] 13 :=
  permutation_upper _ _ _ [6,24,192,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1195

theorem m2748_264 : Upper (D 10) (R 10) [6,96,160,17,264] 13 :=
  permutation_upper _ _ _ [6,24,65,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1162

theorem m2748_288 : Upper (D 10) (R 10) [6,96,160,17,288] 13 :=
  permutation_upper _ _ _ [6,24,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1183

theorem m2748_320 : Upper (D 10) (R 10) [6,96,160,17,320] 13 :=
  permutation_upper _ _ _ [6,24,192,96,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1197

theorem m2748_384 : Upper (D 10) (R 10) [6,96,160,17,384] 13 :=
  permutation_upper _ _ _ [6,24,192,96,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1197

def r2748 : Route 9 := (fun mask => (mask,id))

def c2748 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2748 : Upper (D 10) (R 10) [6,96,160,17] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2748 c2748
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2748_40
  · exact m2748_72
  · exact m2748_96
  · exact m2748_136
  · exact m2748_160
  · exact m2748_192
  · exact m2748_264
  · exact m2748_288
  · exact m2748_320
  · exact m2748_384

theorem m2749_136 : Upper (D 10) (R 10) [6,96,160,33,136] 13 :=
  permutation_upper _ _ _ [6,96,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1741

theorem m2749_384 : Upper (D 10) (R 10) [6,96,160,33,384] 13 :=
  permutation_upper _ _ _ [6,96,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1744

def r2749 : Route 9 := (fun mask => (mask,id))

def c2749 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u2749 : Upper (D 10) (R 10) [6,96,160,33] 13 := by
  apply FastRouting.sound _ _ [6,96,160,33] 13 (by decide) (choices 2) [72,136,192,264,320,384] r2749 c2749
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1741
  · exact m2749_136
  · exact u1742
  · exact u1743
  · exact u1744
  · exact m2749_384

theorem m2750_9 : Upper (D 10) (R 10) [6,96,160,48,9] 13 :=
  permutation_upper _ _ _ [6,24,33,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1153

theorem m2750_129 : Upper (D 10) (R 10) [6,96,160,48,129] 13 :=
  permutation_upper _ _ _ [6,96,160,48,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1745

theorem m2750_136 : Upper (D 10) (R 10) [6,96,160,48,136] 13 :=
  permutation_upper _ _ _ [6,96,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1746

theorem m2750_384 : Upper (D 10) (R 10) [6,96,160,48,384] 13 :=
  permutation_upper _ _ _ [6,96,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1750

def r2750 : Route 9 := (fun mask => (mask,id))

def c2750 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u2750 : Upper (D 10) (R 10) [6,96,160,48] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r2750 c2750
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2750_9
  · exact u1745
  · exact u1746
  · exact m2750_129
  · exact m2750_136
  · exact u1747
  · exact u1748
  · exact u1749
  · exact u1750
  · exact m2750_384

def b2751 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 98 164 73 440 440 504 440 440), lower := (rows 7 98 164 73 16 32 64 128 256), losses := [] }

theorem u2751 : Upper (D 10) (R 10) [6,96,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2751 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2752_9 : Upper (D 10) (R 10) [6,96,160,80,9] 13 :=
  permutation_upper _ _ _ [6,24,65,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1158

theorem m2752_33 : Upper (D 10) (R 10) [6,96,160,80,33] 13 :=
  permutation_upper _ _ _ [6,96,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1741

theorem m2752_40 : Upper (D 10) (R 10) [6,96,160,80,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1746

theorem m2752_129 : Upper (D 10) (R 10) [6,96,160,80,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1751

def r2752 : Route 9 := (fun mask => (mask,id))

def c2752 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2752 : Upper (D 10) (R 10) [6,96,160,80] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2752 c2752
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2752_9
  · exact m2752_33
  · exact m2752_40
  · exact m2752_129
  · exact u1755
  · exact u1756
  · exact u1757
  · exact u1758
  · exact u1759
  · exact u1760

def b2753 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 164 104 409 441 473 409 409), lower := (rows 7 98 164 104 16 32 64 128 256), losses := [] }

theorem u2753 : Upper (D 10) (R 10) [6,96,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2753 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2754_9 : Upper (D 10) (R 10) [6,96,160,192,9] 13 :=
  permutation_upper _ _ _ [6,24,192,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1195

theorem m2754_33 : Upper (D 10) (R 10) [6,96,160,192,33] 13 :=
  permutation_upper _ _ _ [6,96,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1742

theorem m2754_40 : Upper (D 10) (R 10) [6,96,160,192,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1747

def r2754 : Route 9 := (fun mask => (mask,id))

def c2754 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2754 : Upper (D 10) (R 10) [6,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r2754 c2754
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2754_9
  · exact m2754_33
  · exact m2754_40
  · exact u1764
  · exact u1765
  · exact u1766

theorem m2755_40 : Upper (D 10) (R 10) [6,96,160,257,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1748

theorem m2755_72 : Upper (D 10) (R 10) [6,96,160,257,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1757

theorem m2755_96 : Upper (D 10) (R 10) [6,96,160,257,96] 13 :=
  permutation_upper _ _ _ [6,96,160,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1761

theorem m2755_136 : Upper (D 10) (R 10) [6,96,160,257,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1757

theorem m2755_160 : Upper (D 10) (R 10) [6,96,160,257,160] 13 :=
  permutation_upper _ _ _ [6,96,160,96,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1761

theorem m2755_192 : Upper (D 10) (R 10) [6,96,160,257,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1764

theorem m2755_384 : Upper (D 10) (R 10) [6,96,160,257,384] 13 :=
  permutation_upper _ _ _ [6,96,160,257,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1769

def r2755 : Route 9 := (fun mask => (mask,id))

def c2755 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2755 : Upper (D 10) (R 10) [6,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2755 c2755
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2755_40
  · exact m2755_72
  · exact m2755_96
  · exact m2755_136
  · exact m2755_160
  · exact m2755_192
  · exact u1767
  · exact u1768
  · exact u1769
  · exact m2755_384

theorem m2756_9 : Upper (D 10) (R 10) [6,96,160,272,9] 13 :=
  permutation_upper _ _ _ [6,24,65,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1162

theorem m2756_33 : Upper (D 10) (R 10) [6,96,160,272,33] 13 :=
  permutation_upper _ _ _ [6,96,160,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1743

theorem m2756_40 : Upper (D 10) (R 10) [6,96,160,272,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1749

theorem m2756_65 : Upper (D 10) (R 10) [6,96,160,272,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1752

theorem m2756_72 : Upper (D 10) (R 10) [6,96,160,272,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1758

theorem m2756_96 : Upper (D 10) (R 10) [6,96,160,272,96] 13 :=
  permutation_upper _ _ _ [6,96,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1762

theorem m2756_129 : Upper (D 10) (R 10) [6,96,160,272,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1752

theorem m2756_136 : Upper (D 10) (R 10) [6,96,160,272,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1758

theorem m2756_160 : Upper (D 10) (R 10) [6,96,160,272,160] 13 :=
  permutation_upper _ _ _ [6,96,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1762

theorem m2756_192 : Upper (D 10) (R 10) [6,96,160,272,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1765

theorem m2756_257 : Upper (D 10) (R 10) [6,96,160,272,257] 13 :=
  permutation_upper _ _ _ [6,96,160,257,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1767

theorem m2756_384 : Upper (D 10) (R 10) [6,96,160,272,384] 13 :=
  permutation_upper _ _ _ [6,96,160,272,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1772

def r2756 : Route 9 := (fun mask => (mask,id))

def c2756 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2756 : Upper (D 10) (R 10) [6,96,160,272] 13 := by
  apply FastRouting.sound _ _ [6,96,160,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r2756 c2756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2756_9
  · exact m2756_33
  · exact m2756_40
  · exact m2756_65
  · exact m2756_72
  · exact m2756_96
  · exact m2756_129
  · exact m2756_136
  · exact m2756_160
  · exact m2756_192
  · exact m2756_257
  · exact u1770
  · exact u1771
  · exact u1772
  · exact m2756_384

theorem m2757_9 : Upper (D 10) (R 10) [6,96,160,288,9] 13 :=
  permutation_upper _ _ _ [6,24,96,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1183

theorem m2757_65 : Upper (D 10) (R 10) [6,96,160,288,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1753

theorem m2757_72 : Upper (D 10) (R 10) [6,96,160,288,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1759

theorem m2757_129 : Upper (D 10) (R 10) [6,96,160,288,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1753

theorem m2757_136 : Upper (D 10) (R 10) [6,96,160,288,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1759

theorem m2757_192 : Upper (D 10) (R 10) [6,96,160,288,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1766

theorem m2757_257 : Upper (D 10) (R 10) [6,96,160,288,257] 13 :=
  permutation_upper _ _ _ [6,96,160,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1768

theorem m2757_264 : Upper (D 10) (R 10) [6,96,160,288,264] 13 :=
  permutation_upper _ _ _ [6,96,160,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1771

theorem m2757_384 : Upper (D 10) (R 10) [6,96,160,288,384] 13 :=
  permutation_upper _ _ _ [6,96,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1773

def r2757 : Route 9 := (fun mask => (mask,id))

def c2757 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u2757 : Upper (D 10) (R 10) [6,96,160,288] 13 := by
  apply FastRouting.sound _ _ [6,96,160,288] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r2757 c2757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2757_9
  · exact m2757_65
  · exact m2757_72
  · exact m2757_129
  · exact m2757_136
  · exact m2757_192
  · exact m2757_257
  · exact m2757_264
  · exact u1773
  · exact m2757_384

theorem m2758_9 : Upper (D 10) (R 10) [6,96,160,320,9] 13 :=
  permutation_upper _ _ _ [6,24,192,96,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1197

theorem m2758_33 : Upper (D 10) (R 10) [6,96,160,320,33] 13 :=
  permutation_upper _ _ _ [6,96,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1744

theorem m2758_40 : Upper (D 10) (R 10) [6,96,160,320,40] 13 :=
  permutation_upper _ _ _ [6,96,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1750

theorem m2758_129 : Upper (D 10) (R 10) [6,96,160,320,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1754

theorem m2758_136 : Upper (D 10) (R 10) [6,96,160,320,136] 13 :=
  permutation_upper _ _ _ [6,96,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1760

theorem m2758_160 : Upper (D 10) (R 10) [6,96,160,320,160] 13 :=
  permutation_upper _ _ _ [6,96,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1763

theorem m2758_257 : Upper (D 10) (R 10) [6,96,160,320,257] 13 :=
  permutation_upper _ _ _ [6,96,160,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1769

theorem m2758_264 : Upper (D 10) (R 10) [6,96,160,320,264] 13 :=
  permutation_upper _ _ _ [6,96,160,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1772

theorem m2758_288 : Upper (D 10) (R 10) [6,96,160,320,288] 13 :=
  permutation_upper _ _ _ [6,96,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1773

def r2758 : Route 9 := (fun mask => (mask,id))

def c2758 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2758 : Upper (D 10) (R 10) [6,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2758 c2758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2758_9
  · exact m2758_33
  · exact m2758_40
  · exact m2758_129
  · exact m2758_136
  · exact m2758_160
  · exact m2758_257
  · exact m2758_264
  · exact m2758_288
  · exact u1774

def b2759 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 25 440 424 488 424 424), lower := (rows 7 98 196 25 16 32 64 128 256), losses := [] }

theorem u2759 : Upper (D 10) (R 10) [6,96,192,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2759 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2759
end Delivery.IrregularNine14.P10
