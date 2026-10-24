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

def b14820 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 200 276 36 67 131 259), lower := (rows 11 98 52 200 276 36 64 128 256), losses := [] }

theorem u14820 : Upper (D 6) (R 6) [10,96,48,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14821 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 98 52 392 21 33 70 198 326), lower := (rows 11 98 52 392 21 33 64 128 256), losses := [] }

theorem u14821 : Upper (D 6) (R 6) [10,96,48,384,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14822 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 456, targets := 2 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 11 98 52 392 21 34 69 197 325), lower := (rows 11 98 52 392 21 34 64 128 256), losses := [] }

theorem u14822 : Upper (D 6) (R 6) [10,96,48,384,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14823 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 98 52 392 21 36 67 195 323), lower := (rows 11 98 52 392 21 36 64 128 256), losses := [] }

theorem u14823 : Upper (D 6) (R 6) [10,96,48,384,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14824 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 392 21 96 71 135 263), lower := (rows 11 98 52 392 21 96 64 128 256), losses := [] }

theorem u14824 : Upper (D 6) (R 6) [10,96,48,384,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14825 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 458, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 98 52 392 81 33 70 134 262), lower := (rows 11 98 52 392 81 33 64 128 256), losses := [] }

theorem u14825 : Upper (D 6) (R 6) [10,96,48,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14826 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 52 392 81 34 69 133 261), lower := (rows 11 98 52 392 81 34 64 128 256), losses := [] }

theorem u14826 : Upper (D 6) (R 6) [10,96,48,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14827 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 98 52 392 81 36 71 135 263), lower := (rows 11 98 52 392 81 36 64 128 256), losses := [] }

theorem u14827 : Upper (D 6) (R 6) [10,96,48,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14828 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 98 133 25 276 34 100 228 356), lower := (rows 11 98 133 25 276 34 64 128 256), losses := [] }

theorem u14828 : Upper (D 6) (R 6) [10,96,129,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14829 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 5, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 98 133 25 276 36 98 226 354), lower := (rows 11 98 133 25 276 36 64 128 256), losses := [] }

theorem u14829 : Upper (D 6) (R 6) [10,96,129,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14830 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 25 276 96 102 166 294), lower := (rows 11 98 133 25 276 96 64 128 256), losses := [] }

theorem u14830 : Upper (D 6) (R 6) [10,96,129,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14831 : Route 9 := (fun mask => (mask,id))

def c14831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14831 : Upper (D 6) (R 6) [10,96,129,20,257,2] 13 := by
  apply FastRouting.sound _ _ [10,96,129,20,257,2] 13 (by decide) (choices 1) [4,32] r14831 c14831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3365
  · exact u3366

def b14832 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 11 98 133 28 273 36 98 226 354), lower := (rows 11 98 133 28 273 36 64 128 256), losses := [{ target := 2, region := (rows 1 34 0 8 17 32 98 162 290), good := (rows 475 482 145 24 273 482 64 128 256) }] }

theorem u14832 : Upper (D 6) (R 6) [10,96,129,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14833 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 28 273 96 102 166 294), lower := (rows 11 98 133 28 273 96 64 128 256), losses := [] }

theorem u14833 : Upper (D 6) (R 6) [10,96,129,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14834 : Route 9 := (fun mask => (mask,id))

def c14834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14834 : Upper (D 6) (R 6) [10,96,129,20,258,1] 13 := by
  apply FastRouting.sound _ _ [10,96,129,20,258,1] 13 (by decide) (choices 1) [4,32] r14834 c14834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3367
  · exact u3368

theorem m14835_1 : Upper (D 6) (R 6) [10,96,129,20,258,4,1] 13 :=
  permutation_upper _ _ _ [10,96,129,20,258,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3367

def r14835 : Route 9 := (fun mask => (mask,id))

def c14835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14835 : Upper (D 6) (R 6) [10,96,129,20,258,4] 13 := by
  apply FastRouting.sound _ _ [10,96,129,20,258,4] 13 (by decide) (choices 1) [1,32] r14835 c14835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14835_1
  · exact u3369

def b14836 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 28 274 96 101 165 293), lower := (rows 11 98 133 28 274 96 64 128 256), losses := [] }

theorem u14836 : Upper (D 6) (R 6) [10,96,129,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14837 : Route 9 := (fun mask => (mask,id))

def c14837 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14837 : Upper (D 6) (R 6) [10,96,129,20,288,1] 13 := by
  apply FastRouting.sound _ _ [10,96,129,20,288,1] 13 (by decide) (choices 1) [2,4] r14837 c14837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3370
  · exact u3371

def b14838 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 98 133 28 304 34 69 197 325), lower := (rows 11 98 133 28 304 34 64 128 256), losses := [] }

theorem u14838 : Upper (D 6) (R 6) [10,96,129,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14839 : Route 9 := (fun mask => (mask,id))

def c14839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14839 : Upper (D 6) (R 6) [10,96,129,20,288,4] 13 := by
  apply FastRouting.sound _ _ [10,96,129,20,288,4] 13 (by decide) (choices 1) [1,2] r14839 c14839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3372
  · exact u3373

def b14840 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 28 304 96 71 135 263), lower := (rows 11 98 133 28 304 96 64 128 256), losses := [] }

theorem u14840 : Upper (D 6) (R 6) [10,96,129,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14841 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 133 44 22 33 336 464 336), lower := (rows 11 98 133 44 22 33 64 128 256), losses := [] }

theorem u14841 : Upper (D 6) (R 6) [10,96,129,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14842 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 133 44 22 48 321 449 321), lower := (rows 11 98 133 44 22 48 64 128 256), losses := [] }

theorem u14842 : Upper (D 6) (R 6) [10,96,129,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14842 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14843 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 44 22 96 337 401 273), lower := (rows 11 98 133 44 22 96 64 128 256), losses := [] }

theorem u14843 : Upper (D 6) (R 6) [10,96,129,36,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14844 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 133 44 22 288 81 209 337), lower := (rows 11 98 133 44 22 288 64 128 256), losses := [] }

theorem u14844 : Upper (D 6) (R 6) [10,96,129,36,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14844 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14845 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 133 44 81 34 340 404 276), lower := (rows 11 98 133 44 81 34 64 128 256), losses := [] }

theorem u14845 : Upper (D 6) (R 6) [10,96,129,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14846 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 133 44 81 36 338 402 274), lower := (rows 11 98 133 44 81 36 64 128 256), losses := [] }

theorem u14846 : Upper (D 6) (R 6) [10,96,129,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14847 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 133 44 81 48 326 390 262), lower := (rows 11 98 133 44 81 48 64 128 256), losses := [] }

theorem u14847 : Upper (D 6) (R 6) [10,96,129,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14847 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14848 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 133 44 81 288 86 150 278), lower := (rows 11 98 133 44 81 288 64 128 256), losses := [] }

theorem u14848 : Upper (D 6) (R 6) [10,96,129,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14848 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14849 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 133 44 84 33 338 402 274), lower := (rows 11 98 133 44 84 33 64 128 256), losses := [] }

theorem u14849 : Upper (D 6) (R 6) [10,96,129,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14850 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 133 44 84 34 337 401 273), lower := (rows 11 98 133 44 84 34 64 128 256), losses := [] }

theorem u14850 : Upper (D 6) (R 6) [10,96,129,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14851 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 133 44 84 48 323 387 259), lower := (rows 11 98 133 44 84 48 64 128 256), losses := [] }

theorem u14851 : Upper (D 6) (R 6) [10,96,129,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14851 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14852 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 133 44 84 288 83 147 275), lower := (rows 11 98 133 44 84 288 64 128 256), losses := [] }

theorem u14852 : Upper (D 6) (R 6) [10,96,129,36,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14852 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14853 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 133 44 273 34 84 212 340), lower := (rows 11 98 133 44 273 34 64 128 256), losses := [] }

theorem u14853 : Upper (D 6) (R 6) [10,96,129,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14854 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 133 44 273 36 82 210 338), lower := (rows 11 98 133 44 273 36 64 128 256), losses := [] }

theorem u14854 : Upper (D 6) (R 6) [10,96,129,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14855 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 133 44 273 48 70 198 326), lower := (rows 11 98 133 44 273 48 64 128 256), losses := [] }

theorem u14855 : Upper (D 6) (R 6) [10,96,129,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14855 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14856 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 44 273 96 86 150 278), lower := (rows 11 98 133 44 273 96 64 128 256), losses := [] }

theorem u14856 : Upper (D 6) (R 6) [10,96,129,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14857 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 133 44 274 33 84 212 340), lower := (rows 11 98 133 44 274 33 64 128 256), losses := [] }

theorem u14857 : Upper (D 6) (R 6) [10,96,129,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14858 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 133 44 274 36 81 209 337), lower := (rows 11 98 133 44 274 36 64 128 256), losses := [] }

theorem u14858 : Upper (D 6) (R 6) [10,96,129,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14859 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 133 44 274 48 69 197 325), lower := (rows 11 98 133 44 274 48 64 128 256), losses := [] }

theorem u14859 : Upper (D 6) (R 6) [10,96,129,36,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14859 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14860 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 44 274 96 85 149 277), lower := (rows 11 98 133 44 274 96 64 128 256), losses := [] }

theorem u14860 : Upper (D 6) (R 6) [10,96,129,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14861 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 133 44 276 33 82 210 338), lower := (rows 11 98 133 44 276 33 64 128 256), losses := [] }

theorem u14861 : Upper (D 6) (R 6) [10,96,129,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14862 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 133 44 276 34 81 209 337), lower := (rows 11 98 133 44 276 34 64 128 256), losses := [] }

theorem u14862 : Upper (D 6) (R 6) [10,96,129,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14863 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 98 133 44 276 48 67 195 323), lower := (rows 11 98 133 44 276 48 64 128 256), losses := [] }

theorem u14863 : Upper (D 6) (R 6) [10,96,129,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14863 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14864 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 44 276 96 83 147 275), lower := (rows 11 98 133 44 276 96 64 128 256), losses := [] }

theorem u14864 : Upper (D 6) (R 6) [10,96,129,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14865 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 133 44 336 33 86 150 278), lower := (rows 11 98 133 44 336 33 64 128 256), losses := [] }

theorem u14865 : Upper (D 6) (R 6) [10,96,129,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14866 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 133 44 336 34 85 149 277), lower := (rows 11 98 133 44 336 34 64 128 256), losses := [] }

theorem u14866 : Upper (D 6) (R 6) [10,96,129,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14867 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 133 44 336 36 83 147 275), lower := (rows 11 98 133 44 336 36 64 128 256), losses := [] }

theorem u14867 : Upper (D 6) (R 6) [10,96,129,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14868 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 133 44 336 48 71 135 263), lower := (rows 11 98 133 44 336 48 64 128 256), losses := [] }

theorem u14868 : Upper (D 6) (R 6) [10,96,129,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14868 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14869 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 133 56 276 33 70 198 326), lower := (rows 11 98 133 56 276 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 64 128 256), good := (rows 41 96 165 56 316 33 64 128 256) }] }

theorem u14869 : Upper (D 6) (R 6) [10,96,129,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14870 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 98 133 56 276 34 69 197 325), lower := (rows 11 98 133 56 276 34 64 128 256), losses := [] }

theorem u14870 : Upper (D 6) (R 6) [10,96,129,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14871 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 133 56 276 36 67 195 323), lower := (rows 11 98 133 56 276 36 64 128 256), losses := [] }

theorem u14871 : Upper (D 6) (R 6) [10,96,129,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14872 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 56 276 96 71 135 263), lower := (rows 11 98 133 56 276 96 64 128 256), losses := [] }

theorem u14872 : Upper (D 6) (R 6) [10,96,129,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14873 : Route 9 := (fun mask => (mask,id))

def c14873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14873 : Upper (D 6) (R 6) [10,96,129,257,6,4] 13 := by
  apply FastRouting.sound _ _ [10,96,129,257,6,4] 13 (by decide) (choices 1) [16,32] r14873 c14873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3374
  · exact u3375

def b14874 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 98 133 265 22 48 100 228 356), lower := (rows 11 98 133 265 22 48 64 128 256), losses := [] }

theorem u14874 : Upper (D 6) (R 6) [10,96,129,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14874 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14875 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 265 22 96 116 180 308), lower := (rows 11 98 133 265 22 96 64 128 256), losses := [] }

theorem u14875 : Upper (D 6) (R 6) [10,96,129,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14876 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 98 133 265 52 34 84 212 340), lower := (rows 11 98 133 265 52 34 64 128 256), losses := [] }

theorem u14876 : Upper (D 6) (R 6) [10,96,129,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14877 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 133 265 52 36 82 210 338), lower := (rows 11 98 133 265 52 36 64 128 256), losses := [] }

theorem u14877 : Upper (D 6) (R 6) [10,96,129,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14878 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 98 133 265 52 48 70 198 326), lower := (rows 11 98 133 265 52 48 64 128 256), losses := [] }

theorem u14878 : Upper (D 6) (R 6) [10,96,129,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14878 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14879 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 133 265 52 96 86 150 278), lower := (rows 11 98 133 265 52 96 64 128 256), losses := [] }

theorem u14879 : Upper (D 6) (R 6) [10,96,129,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14879
end Delivery.IrregularNine14.P06
