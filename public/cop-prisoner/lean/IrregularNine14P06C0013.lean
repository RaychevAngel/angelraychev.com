import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0000

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b780 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 104, targets := 2 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 11 148 104 274 33 68 224 352), lower := (rows 7 11 148 104 274 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 6 40 18 32 87 168 296), good := (rows 86 478 212 488 342 488 68 128 256) }] }

theorem u780 : Upper (D 6) (R 6) [6,9,144,96,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 148 104 274 33 96 196 324), lower := (rows 7 11 148 104 274 33 96 128 256), losses := [] }

theorem u781 : Upper (D 6) (R 6) [6,9,144,96,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b782 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 148 104 274 36 96 193 321), lower := (rows 7 11 148 104 274 36 96 128 256), losses := [] }

theorem u782 : Upper (D 6) (R 6) [6,9,144,96,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b783 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 148 104 276 33 66 224 352), lower := (rows 7 11 148 104 276 33 66 128 256), losses := [] }

theorem u783 : Upper (D 6) (R 6) [6,9,144,96,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 148 104 276 33 96 194 322), lower := (rows 7 11 148 104 276 33 96 128 256), losses := [] }

theorem u784 : Upper (D 6) (R 6) [6,9,144,96,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 148 104 276 34 96 193 321), lower := (rows 7 11 148 104 276 34 96 128 256), losses := [] }

theorem u785 : Upper (D 6) (R 6) [6,9,144,96,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 148 104 304 34 65 196 324), lower := (rows 7 11 148 104 304 34 65 128 256), losses := [] }

theorem u786 : Upper (D 6) (R 6) [6,9,144,96,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 7 11 148 104 304 34 68 193 321), lower := (rows 7 11 148 104 304 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 36 56 48 32 125 131 259), good := (rows 453 457 220 124 380 508 68 128 256) }] }

theorem u787 : Upper (D 6) (R 6) [6,9,144,96,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r788 : Route 9 := (fun mask => (mask,id))

def c788 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u788 : Upper (D 6) (R 6) [6,9,144,96,288,4,1] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,288,4,1] 13 (by decide) (choices 1) [2,64] r788 c788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26
  · exact u27

def r789 : Route 9 := (fun mask => (mask,id))

def c789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u789 : Upper (D 6) (R 6) [6,9,144,96,288,4,2] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,288,4,2] 13 (by decide) (choices 1) [1,64] r789 c789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28
  · exact u29

def b790 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 148 266 112 33 68 224 352), lower := (rows 7 11 148 266 112 33 68 128 256), losses := [] }

theorem u790 : Upper (D 6) (R 6) [6,9,144,258,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 148 266 112 36 96 193 321), lower := (rows 7 11 148 266 112 36 96 128 256), losses := [] }

theorem u791 : Upper (D 6) (R 6) [6,9,144,258,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b792 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 11 148 296 52 96 65 194 322), lower := (rows 7 11 148 296 52 96 65 128 256), losses := [] }

theorem u792 : Upper (D 6) (R 6) [6,9,144,288,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b793 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 112, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 11 148 296 52 96 66 193 321), lower := (rows 7 11 148 296 52 96 66 128 256), losses := [] }

theorem u793 : Upper (D 6) (R 6) [6,9,144,288,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 296 81 36 66 224 352), lower := (rows 7 11 148 296 81 36 66 128 256), losses := [] }

theorem u794 : Upper (D 6) (R 6) [6,9,144,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b795 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 360, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 7 11 148 296 81 36 96 194 322), lower := (rows 7 11 148 296 81 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 53 127 131 259), good := (rows 494 490 252 360 508 100 96 128 256) }] }

theorem u795 : Upper (D 6) (R 6) [6,9,144,288,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b796 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 296 81 96 66 164 292), lower := (rows 7 11 148 296 81 96 66 128 256), losses := [] }

theorem u796 : Upper (D 6) (R 6) [6,9,144,288,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 4 },{ cop := 0, region := 360, targets := 1 }], pairs := [(1,2),(3,0),(3,2)], upper := (rows 7 11 148 296 81 96 68 162 290), lower := (rows 7 11 148 296 81 96 68 128 256), losses := [] }

theorem u797 : Upper (D 6) (R 6) [6,9,144,288,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 148 296 81 96 96 134 262), lower := (rows 7 11 148 296 81 96 96 128 256), losses := [] }

theorem u798 : Upper (D 6) (R 6) [6,9,144,288,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b799 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 360, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(4,0),(4,5)], upper := (rows 7 11 148 296 82 33 68 224 352), lower := (rows 7 11 148 296 82 33 68 128 256), losses := [] }

theorem u799 : Upper (D 6) (R 6) [6,9,144,288,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b800 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 132, targets := 3 },{ cop := 4, region := 133, targets := 32 }], pairs := [(0,5),(2,0),(2,1)], upper := (rows 7 11 148 296 82 33 96 196 324), lower := (rows 7 11 148 296 82 33 96 128 256), losses := [] }

theorem u800 : Upper (D 6) (R 6) [6,9,144,288,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b801 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 296 82 36 65 224 352), lower := (rows 7 11 148 296 82 36 65 128 256), losses := [] }

theorem u801 : Upper (D 6) (R 6) [6,9,144,288,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b802 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 133, targets := 32 },{ cop := 0, region := 112, targets := 1 }], pairs := [(0,5),(2,5),(4,0)], upper := (rows 7 11 148 296 82 36 96 193 321), lower := (rows 7 11 148 296 82 36 96 128 256), losses := [] }

theorem u802 : Upper (D 6) (R 6) [6,9,144,288,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b803 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 296 82 96 65 164 292), lower := (rows 7 11 148 296 82 96 65 128 256), losses := [] }

theorem u803 : Upper (D 6) (R 6) [6,9,144,288,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b804 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 360, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(4,0),(4,5)], upper := (rows 7 11 148 296 82 96 68 161 289), lower := (rows 7 11 148 296 82 96 68 128 256), losses := [] }

theorem u804 : Upper (D 6) (R 6) [6,9,144,288,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b805 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 11 148 296 82 96 96 133 261), lower := (rows 7 11 148 296 82 96 96 128 256), losses := [] }

theorem u805 : Upper (D 6) (R 6) [6,9,144,288,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 11 148 296 84 33 66 224 352), lower := (rows 7 11 148 296 84 33 66 128 256), losses := [] }

theorem u806 : Upper (D 6) (R 6) [6,9,144,288,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b807 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 11 148 296 84 33 96 194 322), lower := (rows 7 11 148 296 84 33 96 128 256), losses := [] }

theorem u807 : Upper (D 6) (R 6) [6,9,144,288,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b808 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 34 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 11 148 296 84 34 65 224 352), lower := (rows 7 11 148 296 84 34 65 128 256), losses := [] }

theorem u808 : Upper (D 6) (R 6) [6,9,144,288,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 112, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 11 148 296 84 34 96 193 321), lower := (rows 7 11 148 296 84 34 96 128 256), losses := [] }

theorem u809 : Upper (D 6) (R 6) [6,9,144,288,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b810 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 11 148 296 84 96 65 162 290), lower := (rows 7 11 148 296 84 96 65 128 256), losses := [] }

theorem u810 : Upper (D 6) (R 6) [6,9,144,288,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b811 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 11 148 296 84 96 66 161 289), lower := (rows 7 11 148 296 84 96 66 128 256), losses := [] }

theorem u811 : Upper (D 6) (R 6) [6,9,144,288,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b812 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 148 296 84 96 96 131 259), lower := (rows 7 11 148 296 84 96 96 128 256), losses := [] }

theorem u812 : Upper (D 6) (R 6) [6,9,144,288,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b813 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 296 112 34 65 196 324), lower := (rows 7 11 148 296 112 34 65 128 256), losses := [] }

theorem u813 : Upper (D 6) (R 6) [6,9,144,288,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b814 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 112, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 11 148 296 112 34 68 193 321), lower := (rows 7 11 148 296 112 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 38 40 56 32 127 131 259), good := (rows 453 477 212 380 124 508 68 128 256) }] }

theorem u814 : Upper (D 6) (R 6) [6,9,144,288,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r815 : Route 9 := (fun mask => (mask,id))

def c815 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u815 : Upper (D 6) (R 6) [6,9,144,288,96,4,1] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,96,4,1] 13 (by decide) (choices 1) [2,64] r815 c815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u30
  · exact u31

def r816 : Route 9 := (fun mask => (mask,id))

def c816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u816 : Upper (D 6) (R 6) [6,9,144,288,96,4,2] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,96,4,2] 13 (by decide) (choices 1) [1,64] r816 c816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u32
  · exact u33

def b817 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 26 304 96 65 196 324), lower := (rows 7 11 164 26 304 96 65 128 256), losses := [] }

theorem u817 : Upper (D 6) (R 6) [6,9,160,18,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b818 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 164 26 304 96 68 193 321), lower := (rows 7 11 164 26 304 96 68 128 256), losses := [] }

theorem u818 : Upper (D 6) (R 6) [6,9,160,18,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 26 336 96 65 164 292), lower := (rows 7 11 164 26 336 96 65 128 256), losses := [] }

theorem u819 : Upper (D 6) (R 6) [6,9,160,18,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 164 26 336 96 68 161 289), lower := (rows 7 11 164 26 336 96 68 128 256), losses := [] }

theorem u820 : Upper (D 6) (R 6) [6,9,160,18,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 164 26 336 96 96 133 261), lower := (rows 7 11 164 26 336 96 96 128 256), losses := [] }

theorem u821 : Upper (D 6) (R 6) [6,9,160,18,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b822 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,1),(4,5)], upper := (rows 7 11 164 56 84 288 65 194 322), lower := (rows 7 11 164 56 84 288 65 128 256), losses := [] }

theorem u822 : Upper (D 6) (R 6) [6,9,160,48,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b822 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b823 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 7 11 164 56 84 288 66 193 321), lower := (rows 7 11 164 56 84 288 66 128 256), losses := [] }

theorem u823 : Upper (D 6) (R 6) [6,9,160,48,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b823 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r824 : Route 9 := (fun mask => (mask,id))

def c824 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u824 : Upper (D 6) (R 6) [6,9,160,48,260,64,1] 13 := by
  apply FastRouting.sound _ _ [6,9,160,48,260,64,1] 13 (by decide) (choices 1) [2,64] r824 c824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u34
  · exact u35

def r825 : Route 9 := (fun mask => (mask,id))

def c825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u825 : Upper (D 6) (R 6) [6,9,160,48,260,64,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,48,260,64,2] 13 (by decide) (choices 1) [1,64] r825 c825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u36
  · exact u37

def b826 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 404, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 74 276 96 65 176 304), lower := (rows 7 11 164 74 276 96 65 128 256), losses := [] }

theorem u826 : Upper (D 6) (R 6) [6,9,160,66,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b827 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 164 74 276 96 80 161 289), lower := (rows 7 11 164 74 276 96 80 128 256), losses := [] }

theorem u827 : Upper (D 6) (R 6) [6,9,160,66,260,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b827 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b828 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 164 74 276 96 96 145 273), lower := (rows 7 11 164 74 276 96 96 128 256), losses := [] }

theorem u828 : Upper (D 6) (R 6) [6,9,160,66,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b829 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 404, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 74 304 96 65 148 276), lower := (rows 7 11 164 74 304 96 65 128 256), losses := [] }

theorem u829 : Upper (D 6) (R 6) [6,9,160,66,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b830 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 74 304 96 68 145 273), lower := (rows 7 11 164 74 304 96 68 128 256), losses := [] }

theorem u830 : Upper (D 6) (R 6) [6,9,160,66,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b831 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 164 74 304 96 80 133 261), lower := (rows 7 11 164 74 304 96 80 128 256), losses := [] }

theorem u831 : Upper (D 6) (R 6) [6,9,160,66,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b831 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b832 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 88 273 96 66 164 292), lower := (rows 7 11 164 88 273 96 66 128 256), losses := [] }

theorem u832 : Upper (D 6) (R 6) [6,9,160,80,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 34, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 88 273 96 68 162 290), lower := (rows 7 11 164 88 273 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 151 24 16 255 223 131 259), good := (rows 486 494 228 124 508 96 100 228 256) }] }

theorem u833 : Upper (D 6) (R 6) [6,9,160,80,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 272, targets := 96 },{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0),(4,5),(4,6)], upper := (rows 7 11 164 88 273 96 96 134 262), lower := (rows 7 11 164 88 273 96 96 128 256), losses := [] }

theorem u834 : Upper (D 6) (R 6) [6,9,160,80,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 88 274 96 65 164 292), lower := (rows 7 11 164 88 274 96 65 128 256), losses := [] }

theorem u835 : Upper (D 6) (R 6) [6,9,160,80,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b836 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 11 164 88 274 96 68 161 289), lower := (rows 7 11 164 88 274 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 151 24 16 255 223 131 259), good := (rows 485 493 228 124 508 96 100 228 256) }] }

theorem u836 : Upper (D 6) (R 6) [6,9,160,80,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b837 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 164 88 274 96 96 133 261), lower := (rows 7 11 164 88 274 96 96 128 256), losses := [] }

theorem u837 : Upper (D 6) (R 6) [6,9,160,80,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 88 276 33 66 224 352), lower := (rows 7 11 164 88 276 33 66 128 256), losses := [] }

theorem u838 : Upper (D 6) (R 6) [6,9,160,80,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b839 : PairBound 9 := { available := 66, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 164 88 276 33 96 194 322), lower := (rows 7 11 164 88 276 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 36 125 49 32 100 129 257), good := (rows 478 410 252 88 348 508 124 128 256) }] }

theorem u839 : Upper (D 6) (R 6) [6,9,160,80,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u839
end Delivery.IrregularNine14.P06
