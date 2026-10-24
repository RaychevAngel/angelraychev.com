import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0056

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14880 : Route 9 := (fun mask => (mask,id))

def c14880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14880 : Upper (D 6) (R 6) [10,96,129,260,6,1] 13 := by
  apply FastRouting.sound _ _ [10,96,129,260,6,1] 13 (by decide) (choices 1) [16,32] r14880 c14880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3376
  · exact u3377

theorem m14881_1 : Upper (D 6) (R 6) [10,96,129,260,6,16,1] 13 :=
  permutation_upper _ _ _ [10,96,129,260,6,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3376

def r14881 : Route 9 := (fun mask => (mask,id))

def c14881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14881 : Upper (D 6) (R 6) [10,96,129,260,6,16] 13 := by
  apply FastRouting.sound _ _ [10,96,129,260,6,16] 13 (by decide) (choices 1) [1,32] r14881 c14881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14881_1
  · exact u3378

def b14882 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 268 22 96 113 177 305), lower := (rows 11 98 133 268 22 96 64 128 256), losses := [] }

theorem u14882 : Upper (D 6) (R 6) [10,96,129,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14883 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 98 133 268 49 34 84 212 340), lower := (rows 11 98 133 268 49 34 64 128 256), losses := [] }

theorem u14883 : Upper (D 6) (R 6) [10,96,129,260,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14884 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 98 133 268 49 36 82 210 338), lower := (rows 11 98 133 268 49 36 64 128 256), losses := [] }

theorem u14884 : Upper (D 6) (R 6) [10,96,129,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14885 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 98 133 268 49 48 70 198 326), lower := (rows 11 98 133 268 49 48 64 128 256), losses := [] }

theorem u14885 : Upper (D 6) (R 6) [10,96,129,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14885 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14886 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 268 49 96 86 150 278), lower := (rows 11 98 133 268 49 96 64 128 256), losses := [] }

theorem u14886 : Upper (D 6) (R 6) [10,96,129,260,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14887 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 98 133 268 52 33 82 210 338), lower := (rows 11 98 133 268 52 33 64 128 256), losses := [] }

theorem u14887 : Upper (D 6) (R 6) [10,96,129,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14888 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 98 133 268 52 34 81 209 337), lower := (rows 11 98 133 268 52 34 64 128 256), losses := [{ target := 0, region := (rows 0 66 4 8 20 99 64 128 256), good := (rows 42 98 180 284 52 34 98 128 256) }] }

theorem u14888 : Upper (D 6) (R 6) [10,96,129,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14889 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 98 133 268 52 48 67 195 323), lower := (rows 11 98 133 268 52 48 64 128 256), losses := [] }

theorem u14889 : Upper (D 6) (R 6) [10,96,129,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14889 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14890 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 268 52 96 83 147 275), lower := (rows 11 98 133 268 52 96 64 128 256), losses := [] }

theorem u14890 : Upper (D 6) (R 6) [10,96,129,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14891 : Route 9 := (fun mask => (mask,id))

def c14891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14891 : Upper (D 6) (R 6) [10,96,129,272,6,1] 13 := by
  apply FastRouting.sound _ _ [10,96,129,272,6,1] 13 (by decide) (choices 1) [4,32] r14891 c14891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3379
  · exact u3380

theorem m14892_1 : Upper (D 6) (R 6) [10,96,129,272,6,4,1] 13 :=
  permutation_upper _ _ _ [10,96,129,272,6,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3379

def r14892 : Route 9 := (fun mask => (mask,id))

def c14892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14892 : Upper (D 6) (R 6) [10,96,129,272,6,4] 13 := by
  apply FastRouting.sound _ _ [10,96,129,272,6,4] 13 (by decide) (choices 1) [1,32] r14892 c14892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14892_1
  · exact u3381

def b14893 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 280 22 96 101 165 293), lower := (rows 11 98 133 280 22 96 64 128 256), losses := [] }

theorem u14893 : Upper (D 6) (R 6) [10,96,129,272,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14894 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 98 133 280 52 33 70 198 326), lower := (rows 11 98 133 280 52 33 64 128 256), losses := [] }

theorem u14894 : Upper (D 6) (R 6) [10,96,129,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14895 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 98 133 280 52 34 69 197 325), lower := (rows 11 98 133 280 52 34 64 128 256), losses := [] }

theorem u14895 : Upper (D 6) (R 6) [10,96,129,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14896 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 98 133 280 52 36 67 195 323), lower := (rows 11 98 133 280 52 36 64 128 256), losses := [] }

theorem u14896 : Upper (D 6) (R 6) [10,96,129,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14897 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 280 52 96 71 135 263), lower := (rows 11 98 133 280 52 96 64 128 256), losses := [] }

theorem u14897 : Upper (D 6) (R 6) [10,96,129,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14898 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 133 296 22 33 84 212 340), lower := (rows 11 98 133 296 22 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 80 144 272), good := (rows 41 96 165 296 508 33 64 128 256) }] }

theorem u14898 : Upper (D 6) (R 6) [10,96,129,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14899 : Route 9 := (fun mask => (mask,id))

def c14899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14899 : Upper (D 6) (R 6) [10,96,129,288,6,4] 13 := by
  apply FastRouting.sound _ _ [10,96,129,288,6,4] 13 (by decide) (choices 1) [1,16] r14899 c14899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3382
  · exact u3383

def b14900 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 133 296 22 48 69 197 325), lower := (rows 11 98 133 296 22 48 64 128 256), losses := [] }

theorem u14900 : Upper (D 6) (R 6) [10,96,129,288,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14900 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14901 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 296 22 96 85 149 277), lower := (rows 11 98 133 296 22 96 64 128 256), losses := [] }

theorem u14901 : Upper (D 6) (R 6) [10,96,129,288,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14902 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 133 296 81 34 84 148 276), lower := (rows 11 98 133 296 81 34 64 128 256), losses := [] }

theorem u14902 : Upper (D 6) (R 6) [10,96,129,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14903 : Route 9 := (fun mask => (mask,id))

def c14903 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14903 : Upper (D 6) (R 6) [10,96,129,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,96,129,288,65,4] 13 (by decide) (choices 1) [2,4,16] r14903 c14903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3384
  · exact u3385
  · exact u3386

def b14904 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 133 296 81 48 70 134 262), lower := (rows 11 98 133 296 81 48 64 128 256), losses := [] }

theorem u14904 : Upper (D 6) (R 6) [10,96,129,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14904 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14905 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 98 133 296 84 33 86 150 278), lower := (rows 11 98 133 296 84 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 64 128 256), good := (rows 43 98 161 296 114 33 64 128 256) }] }

theorem u14905 : Upper (D 6) (R 6) [10,96,129,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14906 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 133 296 84 34 85 149 277), lower := (rows 11 98 133 296 84 34 64 128 256), losses := [] }

theorem u14906 : Upper (D 6) (R 6) [10,96,129,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14907 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 98 133 296 84 36 83 147 275), lower := (rows 11 98 133 296 84 36 64 128 256), losses := [] }

theorem u14907 : Upper (D 6) (R 6) [10,96,129,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14908 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 133 296 84 48 71 135 263), lower := (rows 11 98 133 296 84 48 64 128 256), losses := [] }

theorem u14908 : Upper (D 6) (R 6) [10,96,129,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14908 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14909 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 98 134 25 52 33 324 452 324), lower := (rows 11 98 134 25 52 33 64 128 256), losses := [] }

theorem u14909 : Upper (D 6) (R 6) [10,96,130,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14910 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 98 134 25 52 36 321 449 321), lower := (rows 11 98 134 25 52 36 64 128 256), losses := [] }

theorem u14910 : Upper (D 6) (R 6) [10,96,130,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14911 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 25 52 96 325 389 261), lower := (rows 11 98 134 25 52 96 64 128 256), losses := [] }

theorem u14911 : Upper (D 6) (R 6) [10,96,130,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14912 : Route 9 := (fun mask => (mask,id))

def c14912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14912 : Upper (D 6) (R 6) [10,96,130,17,36,256] 13 := by
  apply FastRouting.sound _ _ [10,96,130,17,36,256] 13 (by decide) (choices 1) [1,4] r14912 c14912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3387
  · exact u3388

def b14913 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 134 25 276 33 100 228 356), lower := (rows 11 98 134 25 276 33 64 128 256), losses := [] }

theorem u14913 : Upper (D 6) (R 6) [10,96,130,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m14914_1 : Upper (D 6) (R 6) [10,96,130,17,260,4,1] 13 :=
  permutation_upper _ _ _ [10,96,130,17,260,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3389

def r14914 : Route 9 := (fun mask => (mask,id))

def c14914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14914 : Upper (D 6) (R 6) [10,96,130,17,260,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,17,260,4] 13 (by decide) (choices 1) [1,32] r14914 c14914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14914_1
  · exact u3390

def b14915 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 25 276 96 101 165 293), lower := (rows 11 98 134 25 276 96 64 128 256), losses := [] }

theorem u14915 : Upper (D 6) (R 6) [10,96,130,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14916 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 134 25 304 33 68 196 324), lower := (rows 11 98 134 25 304 33 64 128 256), losses := [] }

theorem u14916 : Upper (D 6) (R 6) [10,96,130,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14917 : Route 9 := (fun mask => (mask,id))

def c14917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14917 : Upper (D 6) (R 6) [10,96,130,17,288,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,17,288,4] 13 (by decide) (choices 1) [1,4] r14917 c14917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3391
  · exact u3392

def b14918 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 25 304 96 69 133 261), lower := (rows 11 98 134 25 304 96 64 128 256), losses := [] }

theorem u14918 : Upper (D 6) (R 6) [10,96,130,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14919 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 98 134 28 49 33 324 452 324), lower := (rows 11 98 134 28 49 33 64 128 256), losses := [] }

theorem u14919 : Upper (D 6) (R 6) [10,96,130,20,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14920 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 98 134 28 49 36 321 449 321), lower := (rows 11 98 134 28 49 36 64 128 256), losses := [] }

theorem u14920 : Upper (D 6) (R 6) [10,96,130,20,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14921 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 28 49 96 325 389 261), lower := (rows 11 98 134 28 49 96 64 128 256), losses := [] }

theorem u14921 : Upper (D 6) (R 6) [10,96,130,20,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14922 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 98 134 28 49 288 69 197 325), lower := (rows 11 98 134 28 49 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 24 16 0 81 145 273), good := (rows 463 66 134 476 477 256 64 128 256) }] }

theorem u14922 : Upper (D 6) (R 6) [10,96,130,20,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14922 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14923 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 98 134 28 273 33 100 228 356), lower := (rows 11 98 134 28 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 39 24 16 32 98 162 290), good := (rows 462 486 454 28 284 486 64 128 256) }] }

theorem u14923 : Upper (D 6) (R 6) [10,96,130,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m14924_1 : Upper (D 6) (R 6) [10,96,130,20,257,4,1] 13 :=
  permutation_upper _ _ _ [10,96,130,20,257,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3393

def r14924 : Route 9 := (fun mask => (mask,id))

def c14924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14924 : Upper (D 6) (R 6) [10,96,130,20,257,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,20,257,4] 13 (by decide) (choices 1) [1,32] r14924 c14924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14924_1
  · exact u3394

def b14925 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 28 273 96 101 165 293), lower := (rows 11 98 134 28 273 96 64 128 256), losses := [] }

theorem u14925 : Upper (D 6) (R 6) [10,96,130,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14926 : Route 9 := (fun mask => (mask,id))

def c14926 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14926 : Upper (D 6) (R 6) [10,96,130,20,288,1] 13 := by
  apply FastRouting.sound _ _ [10,96,130,20,288,1] 13 (by decide) (choices 1) [1,4] r14926 c14926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3395
  · exact u3396

def r14927 : Route 9 := (fun mask => (mask,id))

def c14927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14927 : Upper (D 6) (R 6) [10,96,130,20,288,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,20,288,4] 13 (by decide) (choices 1) [1] r14927 c14927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u3397

def b14928 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 28 304 96 69 133 261), lower := (rows 11 98 134 28 304 96 64 128 256), losses := [] }

theorem u14928 : Upper (D 6) (R 6) [10,96,130,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14929 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 134 44 81 33 340 404 276), lower := (rows 11 98 134 44 81 33 64 128 256), losses := [] }

theorem u14929 : Upper (D 6) (R 6) [10,96,130,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14930 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 98 134 44 81 36 337 401 273), lower := (rows 11 98 134 44 81 36 64 128 256), losses := [] }

theorem u14930 : Upper (D 6) (R 6) [10,96,130,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14931 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 134 44 81 48 325 389 261), lower := (rows 11 98 134 44 81 48 64 128 256), losses := [] }

theorem u14931 : Upper (D 6) (R 6) [10,96,130,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14931 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14932 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 134 44 81 288 85 149 277), lower := (rows 11 98 134 44 81 288 64 128 256), losses := [] }

theorem u14932 : Upper (D 6) (R 6) [10,96,130,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14932 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14933 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 134 44 84 33 337 401 273), lower := (rows 11 98 134 44 84 33 64 128 256), losses := [] }

theorem u14933 : Upper (D 6) (R 6) [10,96,130,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14934 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 134 44 84 48 321 385 257), lower := (rows 11 98 134 44 84 48 64 128 256), losses := [] }

theorem u14934 : Upper (D 6) (R 6) [10,96,130,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14934 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14935 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 134 44 84 288 81 145 273), lower := (rows 11 98 134 44 84 288 64 128 256), losses := [] }

theorem u14935 : Upper (D 6) (R 6) [10,96,130,36,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14935 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14936 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 134 44 273 33 84 212 340), lower := (rows 11 98 134 44 273 33 64 128 256), losses := [] }

theorem u14936 : Upper (D 6) (R 6) [10,96,130,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14937 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 98 134 44 273 36 81 209 337), lower := (rows 11 98 134 44 273 36 64 128 256), losses := [] }

theorem u14937 : Upper (D 6) (R 6) [10,96,130,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14938 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 134 44 273 48 69 197 325), lower := (rows 11 98 134 44 273 48 64 128 256), losses := [] }

theorem u14938 : Upper (D 6) (R 6) [10,96,130,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14938 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14939 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 44 273 96 85 149 277), lower := (rows 11 98 134 44 273 96 64 128 256), losses := [] }

theorem u14939 : Upper (D 6) (R 6) [10,96,130,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14939
end Delivery.IrregularNine14.P06
