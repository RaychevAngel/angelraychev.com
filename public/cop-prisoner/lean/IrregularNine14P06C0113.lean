import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6780 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 40, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 131 262 44 84 96 65 152 280), lower := (rows 35 131 262 44 84 96 65 128 256), losses := [] }

theorem u6780 : Upper (D 6) (R 6) [34,129,258,36,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6781 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 262 44 84 96 72 145 273), lower := (rows 35 131 262 44 84 96 72 128 256), losses := [] }

theorem u6781 : Upper (D 6) (R 6) [34,129,258,36,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6781 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6782 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 262 44 84 96 80 137 265), lower := (rows 35 131 262 44 84 96 80 128 256), losses := [] }

theorem u6782 : Upper (D 6) (R 6) [34,129,258,36,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6782 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6783 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 262 44 88 96 65 148 276), lower := (rows 35 131 262 44 88 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 73 112 112 64 201 329), good := (rows 446 398 262 444 504 504 508 128 256) }] }

theorem u6783 : Upper (D 6) (R 6) [34,129,258,36,72,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6784 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 262 44 88 96 68 145 273), lower := (rows 35 131 262 44 88 96 68 128 256), losses := [] }

theorem u6784 : Upper (D 6) (R 6) [34,129,258,36,72,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6785 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 262 44 88 96 80 133 261), lower := (rows 35 131 262 44 88 96 80 128 256), losses := [] }

theorem u6785 : Upper (D 6) (R 6) [34,129,258,36,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6785 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6786 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 35 131 262 56 81 36 68 200 328), lower := (rows 35 131 262 56 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 100 152 280), good := (rows 98 130 358 504 504 100 100 128 256) },{ target := 1, region := (rows 1 0 4 25 17 100 100 153 281), good := (rows 505 409 356 504 505 100 100 128 256) }] }

theorem u6786 : Upper (D 6) (R 6) [34,129,258,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6787 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 262 56 81 36 72 196 324), lower := (rows 35 131 262 56 81 36 72 128 256), losses := [] }

theorem u6787 : Upper (D 6) (R 6) [34,129,258,48,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6787 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6788 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 262 73 84 48 68 168 296), lower := (rows 35 131 262 73 84 48 68 128 256), losses := [] }

theorem u6788 : Upper (D 6) (R 6) [34,129,258,65,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6788 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6789 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 35 131 262 73 84 48 72 164 292), lower := (rows 35 131 262 73 84 48 72 128 256), losses := [] }

theorem u6789 : Upper (D 6) (R 6) [34,129,258,65,68,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6789 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6790 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 73 84 48 96 140 268), lower := (rows 35 131 262 73 84 48 96 128 256), losses := [] }

theorem u6790 : Upper (D 6) (R 6) [34,129,258,65,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6790 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6791 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 262 73 112 36 68 152 280), lower := (rows 35 131 262 73 112 36 68 128 256), losses := [] }

theorem u6791 : Upper (D 6) (R 6) [34,129,258,65,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6792 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 72, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 262 73 112 36 72 148 276), lower := (rows 35 131 262 73 112 36 72 128 256), losses := [] }

theorem u6792 : Upper (D 6) (R 6) [34,129,258,65,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6792 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6793 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 262 73 112 36 80 140 268), lower := (rows 35 131 262 73 112 36 80 128 256), losses := [] }

theorem u6793 : Upper (D 6) (R 6) [34,129,258,65,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6793 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6794 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 268 13 22 96 80 224 352), lower := (rows 35 131 268 13 22 96 80 128 256), losses := [] }

theorem u6794 : Upper (D 6) (R 6) [34,129,264,5,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6794 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6795 : Route 9 := (fun mask => (mask,id))

def c6795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6795 : Upper (D 6) (R 6) [34,129,264,5,6,64,32] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,6,64,32] 13 (by decide) (choices 1) [16,64] r6795 c6795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u515
  · exact u516

def b6796 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 13 52 96 66 208 336), lower := (rows 35 131 268 13 52 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 28 107 67 136 264), good := (rows 98 226 444 508 52 96 98 128 256) }] }

theorem u6796 : Upper (D 6) (R 6) [34,129,264,5,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6797 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 268 13 52 96 80 194 322), lower := (rows 35 131 268 13 52 96 80 128 256), losses := [] }

theorem u6797 : Upper (D 6) (R 6) [34,129,264,5,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6797 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6798 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 13 82 96 68 176 304), lower := (rows 35 131 268 13 82 96 68 128 256), losses := [] }

theorem u6798 : Upper (D 6) (R 6) [34,129,264,5,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6799 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 13 82 96 80 164 292), lower := (rows 35 131 268 13 82 96 80 128 256), losses := [] }

theorem u6799 : Upper (D 6) (R 6) [34,129,264,5,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6799 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6800 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 115, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 13 82 96 96 148 276), lower := (rows 35 131 268 13 82 96 96 128 256), losses := [] }

theorem u6800 : Upper (D 6) (R 6) [34,129,264,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6801 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 13 84 96 66 176 304), lower := (rows 35 131 268 13 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 123 67 156 284), good := (rows 98 226 444 508 500 96 98 128 256) }] }

theorem u6801 : Upper (D 6) (R 6) [34,129,264,5,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6802 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 13 84 96 80 162 290), lower := (rows 35 131 268 13 84 96 80 128 256), losses := [] }

theorem u6802 : Upper (D 6) (R 6) [34,129,264,5,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6802 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6803 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 268 13 84 96 96 146 274), lower := (rows 35 131 268 13 84 96 96 128 256), losses := [] }

theorem u6803 : Upper (D 6) (R 6) [34,129,264,5,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6804 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 268 14 21 96 80 224 352), lower := (rows 35 131 268 14 21 96 80 128 256), losses := [] }

theorem u6804 : Upper (D 6) (R 6) [34,129,264,6,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6804 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6805 : Route 9 := (fun mask => (mask,id))

def c6805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6805 : Upper (D 6) (R 6) [34,129,264,6,5,64,32] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,5,64,32] 13 (by decide) (choices 1) [16,64] r6805 c6805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u517
  · exact u518

def b6806 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 14 52 96 65 208 336), lower := (rows 35 131 268 14 52 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 11 113 96 64 224 352), good := (rows 446 158 268 14 436 500 508 128 256) }] }

theorem u6806 : Upper (D 6) (R 6) [34,129,264,6,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6807 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 268 14 52 96 80 193 321), lower := (rows 35 131 268 14 52 96 80 128 256), losses := [] }

theorem u6807 : Upper (D 6) (R 6) [34,129,264,6,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6807 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6808 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 14 81 96 68 176 304), lower := (rows 35 131 268 14 81 96 68 128 256), losses := [] }

theorem u6808 : Upper (D 6) (R 6) [34,129,264,6,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6809 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 14 81 96 80 164 292), lower := (rows 35 131 268 14 81 96 80 128 256), losses := [] }

theorem u6809 : Upper (D 6) (R 6) [34,129,264,6,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6809 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6810 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 131 268 14 81 96 96 148 276), lower := (rows 35 131 268 14 81 96 96 128 256), losses := [] }

theorem u6810 : Upper (D 6) (R 6) [34,129,264,6,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6811 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 14 84 96 65 176 304), lower := (rows 35 131 268 14 84 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 71 11 112 112 64 241 369), good := (rows 446 398 268 14 500 500 508 128 256) }] }

theorem u6811 : Upper (D 6) (R 6) [34,129,264,6,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6812 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 14 84 96 80 161 289), lower := (rows 35 131 268 14 84 96 80 128 256), losses := [] }

theorem u6812 : Upper (D 6) (R 6) [34,129,264,6,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6812 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6813 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 268 14 84 96 96 145 273), lower := (rows 35 131 268 14 84 96 96 128 256), losses := [] }

theorem u6813 : Upper (D 6) (R 6) [34,129,264,6,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6814 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 5, region := 131, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 268 25 22 96 68 224 352), lower := (rows 35 131 268 25 22 96 68 128 256), losses := [] }

theorem u6814 : Upper (D 6) (R 6) [34,129,264,17,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6815 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 268 25 22 96 96 196 324), lower := (rows 35 131 268 25 22 96 96 128 256), losses := [] }

theorem u6815 : Upper (D 6) (R 6) [34,129,264,17,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6816 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 131 268 25 52 96 66 196 324), lower := (rows 35 131 268 25 52 96 66 128 256), losses := [] }

theorem u6816 : Upper (D 6) (R 6) [34,129,264,17,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6817 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 131 268 25 52 96 68 194 322), lower := (rows 35 131 268 25 52 96 68 128 256), losses := [] }

theorem u6817 : Upper (D 6) (R 6) [34,129,264,17,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6818 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 25 84 96 66 164 292), lower := (rows 35 131 268 25 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 123 67 156 284), good := (rows 98 226 444 508 500 96 98 128 256) }] }

theorem u6818 : Upper (D 6) (R 6) [34,129,264,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6819 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 25 84 96 68 162 290), lower := (rows 35 131 268 25 84 96 68 128 256), losses := [] }

theorem u6819 : Upper (D 6) (R 6) [34,129,264,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6820 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 131 268 25 84 96 96 134 262), lower := (rows 35 131 268 25 84 96 96 128 256), losses := [] }

theorem u6820 : Upper (D 6) (R 6) [34,129,264,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6821 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 131 268 25 112 36 66 196 324), lower := (rows 35 131 268 25 112 36 66 128 256), losses := [] }

theorem u6821 : Upper (D 6) (R 6) [34,129,264,17,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6822 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 268 25 112 36 68 194 322), lower := (rows 35 131 268 25 112 36 68 128 256), losses := [] }

theorem u6822 : Upper (D 6) (R 6) [34,129,264,17,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6823 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 5, region := 131, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 268 26 21 96 68 224 352), lower := (rows 35 131 268 26 21 96 68 128 256), losses := [] }

theorem u6823 : Upper (D 6) (R 6) [34,129,264,18,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6824 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 268 26 21 96 96 196 324), lower := (rows 35 131 268 26 21 96 96 128 256), losses := [] }

theorem u6824 : Upper (D 6) (R 6) [34,129,264,18,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6825 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 26 52 96 65 196 324), lower := (rows 35 131 268 26 52 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 11 113 96 64 224 352), good := (rows 446 158 268 26 436 500 508 128 256) }] }

theorem u6825 : Upper (D 6) (R 6) [34,129,264,18,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6826 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 5, region := 131, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 268 26 52 96 68 193 321), lower := (rows 35 131 268 26 52 96 68 128 256), losses := [] }

theorem u6826 : Upper (D 6) (R 6) [34,129,264,18,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6827 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 26 84 96 65 164 292), lower := (rows 35 131 268 26 84 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 79 9 112 112 64 249 377), good := (rows 446 398 396 446 500 500 508 128 256) }] }

theorem u6827 : Upper (D 6) (R 6) [34,129,264,18,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6828 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 26 84 96 68 161 289), lower := (rows 35 131 268 26 84 96 68 128 256), losses := [] }

theorem u6828 : Upper (D 6) (R 6) [34,129,264,18,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6829 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 268 26 84 96 96 133 261), lower := (rows 35 131 268 26 84 96 96 128 256), losses := [] }

theorem u6829 : Upper (D 6) (R 6) [34,129,264,18,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6830 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 131 268 26 112 36 65 196 324), lower := (rows 35 131 268 26 112 36 65 128 256), losses := [] }

theorem u6830 : Upper (D 6) (R 6) [34,129,264,18,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6831 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 268 26 112 36 68 193 321), lower := (rows 35 131 268 26 112 36 68 128 256), losses := [] }

theorem u6831 : Upper (D 6) (R 6) [34,129,264,18,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6832 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 28 81 96 66 164 292), lower := (rows 35 131 268 28 81 96 66 128 256), losses := [] }

theorem u6832 : Upper (D 6) (R 6) [34,129,264,20,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6833 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 28 81 96 68 162 290), lower := (rows 35 131 268 28 81 96 68 128 256), losses := [] }

theorem u6833 : Upper (D 6) (R 6) [34,129,264,20,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6834 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 131 268 28 81 96 96 134 262), lower := (rows 35 131 268 28 81 96 96 128 256), losses := [] }

theorem u6834 : Upper (D 6) (R 6) [34,129,264,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6835 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 28 82 96 65 164 292), lower := (rows 35 131 268 28 82 96 65 128 256), losses := [] }

theorem u6835 : Upper (D 6) (R 6) [34,129,264,20,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6836 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 28 82 96 68 161 289), lower := (rows 35 131 268 28 82 96 68 128 256), losses := [] }

theorem u6836 : Upper (D 6) (R 6) [34,129,264,20,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6837 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 115, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 28 82 96 96 133 261), lower := (rows 35 131 268 28 82 96 96 128 256), losses := [] }

theorem u6837 : Upper (D 6) (R 6) [34,129,264,20,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6838 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 44 22 96 65 208 336), lower := (rows 35 131 268 44 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 100 105 17 96 64 192 320), good := (rows 62 154 268 44 22 492 508 128 256) }] }

theorem u6838 : Upper (D 6) (R 6) [34,129,264,36,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6839 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 268 44 22 96 80 193 321), lower := (rows 35 131 268 44 22 96 80 128 256), losses := [] }

theorem u6839 : Upper (D 6) (R 6) [34,129,264,36,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6839 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6839
end Delivery.IrregularNine14.P06
