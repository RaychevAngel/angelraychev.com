import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0091
import IrregularNine14P08C0092

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15720 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 168 49 305 369 433 305), lower := (rows 193 14 70 168 49 32 64 128 256), losses := [] }

theorem u15720 : Upper (D 8) (R 8) [192,12,66,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15721 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 168 273 49 113 177 305), lower := (rows 193 14 70 168 273 32 64 128 256), losses := [] }

theorem u15721 : Upper (D 8) (R 8) [192,12,66,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15722 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 168 304 49 113 177 305), lower := (rows 193 14 70 168 304 32 64 128 256), losses := [] }

theorem u15722 : Upper (D 8) (R 8) [192,12,66,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15723 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 265 49 176 240 176 432), lower := (rows 193 14 70 265 49 32 64 128 256), losses := [] }

theorem u15723 : Upper (D 8) (R 8) [192,12,66,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15724 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 265 176 49 113 177 305), lower := (rows 193 14 70 265 176 32 64 128 256), losses := [] }

theorem u15724 : Upper (D 8) (R 8) [192,12,66,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15725 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 280 49 161 225 161 417), lower := (rows 193 14 70 280 49 32 64 128 256), losses := [] }

theorem u15725 : Upper (D 8) (R 8) [192,12,66,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15726 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 280 176 33 97 161 289), lower := (rows 193 14 70 280 176 32 64 128 256), losses := [] }

theorem u15726 : Upper (D 8) (R 8) [192,12,66,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15727 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 296 49 177 241 177 433), lower := (rows 193 14 70 296 49 32 64 128 256), losses := [] }

theorem u15727 : Upper (D 8) (R 8) [192,12,66,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15728 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 296 176 49 113 177 305), lower := (rows 193 14 70 296 176 32 64 128 256), losses := [] }

theorem u15728 : Upper (D 8) (R 8) [192,12,66,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15729 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 392 49 49 113 177 305), lower := (rows 193 14 70 392 49 32 64 128 256), losses := [] }

theorem u15729 : Upper (D 8) (R 8) [192,12,66,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15730 : Route 9 := (fun mask => (mask,id))

def c15730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15730 : Upper (D 8) (R 8) [192,12,80,160,33] 13 := by
  apply FastRouting.sound _ _ [192,12,80,160,33] 13 (by decide) (choices 1) [1,2,256] r15730 c15730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5504
  · exact u5505
  · exact u5506

def b15731 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 84 168 50 289 353 417 289), lower := (rows 193 14 84 168 50 32 64 128 256), losses := [] }

theorem u15731 : Upper (D 8) (R 8) [192,12,80,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15732 : Route 9 := (fun mask => (mask,id))

def c15732 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15732 : Upper (D 8) (R 8) [192,12,80,160,257] 13 := by
  apply FastRouting.sound _ _ [192,12,80,160,257] 13 (by decide) (choices 1) [1,2] r15732 c15732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5507
  · exact u5508

def b15733 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 84 168 274 33 97 161 289), lower := (rows 193 14 84 168 274 32 64 128 256), losses := [] }

theorem u15733 : Upper (D 8) (R 8) [192,12,80,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15734 : Route 9 := (fun mask => (mask,id))

def c15734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15734 : Upper (D 8) (R 8) [192,12,80,160,288] 13 := by
  apply FastRouting.sound _ _ [192,12,80,160,288] 13 (by decide) (choices 1) [1,2] r15734 c15734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5509
  · exact u5510

def r15735 : Route 9 := (fun mask => (mask,id))

def c15735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15735 : Upper (D 8) (R 8) [192,12,80,257,33] 13 := by
  apply FastRouting.sound _ _ [192,12,80,257,33] 13 (by decide) (choices 1) [2,128] r15735 c15735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5511
  · exact u5512

def b15736 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 84 265 50 161 225 161 417), lower := (rows 193 14 84 265 50 32 64 128 256), losses := [] }

theorem u15736 : Upper (D 8) (R 8) [192,12,80,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15737 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 84 265 145 34 98 162 290), lower := (rows 193 14 84 265 145 32 64 128 256), losses := [] }

theorem u15737 : Upper (D 8) (R 8) [192,12,80,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15738 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 84 265 146 33 97 161 289), lower := (rows 193 14 84 265 146 32 64 128 256), losses := [] }

theorem u15738 : Upper (D 8) (R 8) [192,12,80,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15739 : Route 9 := (fun mask => (mask,id))

def c15739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15739 : Upper (D 8) (R 8) [192,12,80,257,160] 13 := by
  apply FastRouting.sound _ _ [192,12,80,257,160] 13 (by decide) (choices 1) [1,2] r15739 c15739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5513
  · exact u5514

def b15740 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 84 266 49 161 225 161 417), lower := (rows 193 14 84 266 49 32 64 128 256), losses := [] }

theorem u15740 : Upper (D 8) (R 8) [192,12,80,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15741 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 84 266 176 33 97 161 289), lower := (rows 193 14 84 266 176 32 64 128 256), losses := [] }

theorem u15741 : Upper (D 8) (R 8) [192,12,80,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15742 : Route 9 := (fun mask => (mask,id))

def c15742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15742 : Upper (D 8) (R 8) [192,12,80,288,33] 13 := by
  apply FastRouting.sound _ _ [192,12,80,288,33] 13 (by decide) (choices 1) [1,2,128] r15742 c15742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5515
  · exact u5516
  · exact u5517

def b15743 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 84 296 50 161 225 161 417), lower := (rows 193 14 84 296 50 32 64 128 256), losses := [] }

theorem u15743 : Upper (D 8) (R 8) [192,12,80,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15744 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 84 296 145 35 99 163 291), lower := (rows 193 14 84 296 145 32 64 128 256), losses := [] }

theorem u15744 : Upper (D 8) (R 8) [192,12,80,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15745 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 84 296 146 33 97 161 289), lower := (rows 193 14 84 296 146 32 64 128 256), losses := [] }

theorem u15745 : Upper (D 8) (R 8) [192,12,80,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15746 : Route 9 := (fun mask => (mask,id))

def c15746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15746 : Upper (D 8) (R 8) [192,12,80,288,160] 13 := by
  apply FastRouting.sound _ _ [192,12,80,288,160] 13 (by decide) (choices 1) [1,2] r15746 c15746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5518
  · exact u5519

def r15747 : Route 9 := (fun mask => (mask,id))

def c15747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15747 : Upper (D 8) (R 8) [192,12,80,384,33] 13 := by
  apply FastRouting.sound _ _ [192,12,80,384,33] 13 (by decide) (choices 1) [1,2] r15747 c15747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5520
  · exact u5521

def b15748 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 84 392 50 33 97 161 289), lower := (rows 193 14 84 392 50 32 64 128 256), losses := [] }

theorem u15748 : Upper (D 8) (R 8) [192,12,80,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15749 : Route 9 := (fun mask => (mask,id))

def c15749 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15749 : Upper (D 8) (R 8) [192,12,96,160,33] 13 := by
  apply FastRouting.sound _ _ [192,12,96,160,33] 13 (by decide) (choices 1) [1,2,16,256] r15749 c15749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5522
  · exact u5523
  · exact u5524
  · exact u5525

def b15750 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 193 14 100 168 50 305 337 401 273), lower := (rows 193 14 100 168 50 32 64 128 256), losses := [] }

theorem u15750 : Upper (D 8) (R 8) [192,12,96,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15751 : Route 9 := (fun mask => (mask,id))

def c15751 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15751 : Upper (D 8) (R 8) [192,12,96,160,257] 13 := by
  apply FastRouting.sound _ _ [192,12,96,160,257] 13 (by decide) (choices 1) [1,2,16] r15751 c15751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5526
  · exact u5527
  · exact u5528

def r15752 : Route 9 := (fun mask => (mask,id))

def c15752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15752 : Upper (D 8) (R 8) [192,12,96,160,258] 13 := by
  apply FastRouting.sound _ _ [192,12,96,160,258] 13 (by decide) (choices 1) [1,16] r15752 c15752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5529
  · exact u5530

def r15753 : Route 9 := (fun mask => (mask,id))

def c15753 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15753 : Upper (D 8) (R 8) [192,12,96,160,288] 13 := by
  apply FastRouting.sound _ _ [192,12,96,160,288] 13 (by decide) (choices 1) [1,2,16] r15753 c15753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5531
  · exact u5532
  · exact u5533

def r15754 : Route 9 := (fun mask => (mask,id))

def c15754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15754 : Upper (D 8) (R 8) [192,12,96,257,33] 13 := by
  apply FastRouting.sound _ _ [192,12,96,257,33] 13 (by decide) (choices 1) [2,16,128] r15754 c15754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5534
  · exact u5535
  · exact u5536

def r15755 : Route 9 := (fun mask => (mask,id))

def c15755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15755 : Upper (D 8) (R 8) [192,12,96,257,34] 13 := by
  apply FastRouting.sound _ _ [192,12,96,257,34] 13 (by decide) (choices 1) [1,16,128] r15755 c15755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5537
  · exact u5538
  · exact u5539

def b15756 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 100 265 145 50 114 178 306), lower := (rows 193 14 100 265 145 32 64 128 256), losses := [] }

theorem u15756 : Upper (D 8) (R 8) [192,12,96,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15757 : Route 9 := (fun mask => (mask,id))

def c15757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15757 : Upper (D 8) (R 8) [192,12,96,257,130] 13 := by
  apply FastRouting.sound _ _ [192,12,96,257,130] 13 (by decide) (choices 1) [1,16] r15757 c15757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5540
  · exact u5541

def r15758 : Route 9 := (fun mask => (mask,id))

def c15758 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15758 : Upper (D 8) (R 8) [192,12,96,257,160] 13 := by
  apply FastRouting.sound _ _ [192,12,96,257,160] 13 (by decide) (choices 1) [1,2,16] r15758 c15758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5542
  · exact u5543
  · exact u5544

def b15759 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 100 266 49 177 241 177 433), lower := (rows 193 14 100 266 49 32 64 128 256), losses := [] }

theorem u15759 : Upper (D 8) (R 8) [192,12,96,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15760 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 100 266 176 49 113 177 305), lower := (rows 193 14 100 266 176 32 64 128 256), losses := [] }

theorem u15760 : Upper (D 8) (R 8) [192,12,96,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15761 : Route 9 := (fun mask => (mask,id))

def c15761 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15761 : Upper (D 8) (R 8) [192,12,96,272,33] 13 := by
  apply FastRouting.sound _ _ [192,12,96,272,33] 13 (by decide) (choices 1) [1,2,128] r15761 c15761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5545
  · exact u5546
  · exact u5547

def r15762 : Route 9 := (fun mask => (mask,id))

def c15762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15762 : Upper (D 8) (R 8) [192,12,96,272,34] 13 := by
  apply FastRouting.sound _ _ [192,12,96,272,34] 13 (by decide) (choices 1) [1,128] r15762 c15762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5548
  · exact u5549

def b15763 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 100 280 145 35 99 163 291), lower := (rows 193 14 100 280 145 32 64 128 256), losses := [] }

theorem u15763 : Upper (D 8) (R 8) [192,12,96,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15764 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 193 14 100 280 146 33 97 161 289), lower := (rows 193 14 100 280 146 32 64 128 256), losses := [] }

theorem u15764 : Upper (D 8) (R 8) [192,12,96,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15765 : Route 9 := (fun mask => (mask,id))

def c15765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15765 : Upper (D 8) (R 8) [192,12,96,272,160] 13 := by
  apply FastRouting.sound _ _ [192,12,96,272,160] 13 (by decide) (choices 1) [1,2] r15765 c15765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5550
  · exact u5551

def r15766 : Route 9 := (fun mask => (mask,id))

def c15766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15766 : Upper (D 8) (R 8) [192,12,96,288,33] 13 := by
  apply FastRouting.sound _ _ [192,12,96,288,33] 13 (by decide) (choices 1) [1,2,16,128] r15766 c15766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5552
  · exact u5553
  · exact u5554
  · exact u5555

def b15767 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 193, targets := 32 }], pairs := [(0,5)], upper := (rows 193 14 100 296 50 177 209 145 401), lower := (rows 193 14 100 296 50 32 64 128 256), losses := [] }

theorem u15767 : Upper (D 8) (R 8) [192,12,96,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15768 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 100 296 145 51 115 179 307), lower := (rows 193 14 100 296 145 32 64 128 256), losses := [] }

theorem u15768 : Upper (D 8) (R 8) [192,12,96,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15769 : Route 9 := (fun mask => (mask,id))

def c15769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15769 : Upper (D 8) (R 8) [192,12,96,288,130] 13 := by
  apply FastRouting.sound _ _ [192,12,96,288,130] 13 (by decide) (choices 1) [1,16] r15769 c15769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5556
  · exact u5557

def r15770 : Route 9 := (fun mask => (mask,id))

def c15770 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15770 : Upper (D 8) (R 8) [192,12,96,288,160] 13 := by
  apply FastRouting.sound _ _ [192,12,96,288,160] 13 (by decide) (choices 1) [1,2,16] r15770 c15770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5558
  · exact u5559
  · exact u5560

def r15771 : Route 9 := (fun mask => (mask,id))

def c15771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15771 : Upper (D 8) (R 8) [192,12,96,384,33] 13 := by
  apply FastRouting.sound _ _ [192,12,96,384,33] 13 (by decide) (choices 1) [1,2,16] r15771 c15771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5561
  · exact u5562
  · exact u5563

def r15772 : Route 9 := (fun mask => (mask,id))

def c15772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15772 : Upper (D 8) (R 8) [192,12,96,384,34] 13 := by
  apply FastRouting.sound _ _ [192,12,96,384,34] 13 (by decide) (choices 1) [1,16] r15772 c15772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5564
  · exact u5565

def b15773 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 265 49 50 114 178 306), lower := (rows 193 14 196 265 49 32 64 128 256), losses := [] }

theorem u15773 : Upper (D 8) (R 8) [192,12,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15774 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 265 50 49 113 177 305), lower := (rows 193 14 196 265 50 32 64 128 256), losses := [] }

theorem u15774 : Upper (D 8) (R 8) [192,12,192,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15775 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 266 49 49 113 177 305), lower := (rows 193 14 196 266 49 32 64 128 256), losses := [] }

theorem u15775 : Upper (D 8) (R 8) [192,12,192,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15776 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 280 49 35 99 163 291), lower := (rows 193 14 196 280 49 32 64 128 256), losses := [] }

theorem u15776 : Upper (D 8) (R 8) [192,12,192,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15777 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 280 50 33 97 161 289), lower := (rows 193 14 196 280 50 32 64 128 256), losses := [] }

theorem u15777 : Upper (D 8) (R 8) [192,12,192,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15778 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 296 49 51 115 179 307), lower := (rows 193 14 196 296 49 32 64 128 256), losses := [] }

theorem u15778 : Upper (D 8) (R 8) [192,12,192,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15779 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 196 296 50 49 113 177 305), lower := (rows 193 14 196 296 50 32 64 128 256), losses := [] }

theorem u15779 : Upper (D 8) (R 8) [192,12,192,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15779
end Delivery.IrregularNine14.P08
