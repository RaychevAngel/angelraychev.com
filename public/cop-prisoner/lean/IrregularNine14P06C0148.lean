import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0011
import IrregularNine14P06C0012

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8880 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 200 273 36 98 226 354), lower := (rows 7 11 52 200 273 36 64 128 256), losses := [] }

theorem u8880 : Upper (D 6) (R 6) [6,9,48,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8881 : Route 9 := (fun mask => (mask,id))

def c8881 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8881 : Upper (D 6) (R 6) [6,9,48,192,257,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,257,64] 13 (by decide) (choices 1) [2,4,32] r8881 c8881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u700
  · exact u701
  · exact u702

def b8882 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 200, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 7 11 52 200 274 33 100 228 356), lower := (rows 7 11 52 200 274 33 64 128 256), losses := [] }

theorem u8882 : Upper (D 6) (R 6) [6,9,48,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8883 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 7 11 52 200 274 36 97 225 353), lower := (rows 7 11 52 200 274 36 64 128 256), losses := [] }

theorem u8883 : Upper (D 6) (R 6) [6,9,48,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8884 : Route 9 := (fun mask => (mask,id))

def c8884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8884 : Upper (D 6) (R 6) [6,9,48,192,258,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,258,64] 13 (by decide) (choices 1) [1,4,32] r8884 c8884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u703
  · exact u704
  · exact u705

def r8885 : Route 9 := (fun mask => (mask,id))

def c8885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8885 : Upper (D 6) (R 6) [6,9,48,192,260,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,260,1] 13 (by decide) (choices 1) [2,32] r8885 c8885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u706
  · exact u707

def r8886 : Route 9 := (fun mask => (mask,id))

def c8886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8886 : Upper (D 6) (R 6) [6,9,48,192,260,2] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,260,2] 13 (by decide) (choices 1) [1,32] r8886 c8886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u708
  · exact u709

def r8887 : Route 9 := (fun mask => (mask,id))

def c8887 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8887 : Upper (D 6) (R 6) [6,9,48,192,260,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,260,64] 13 (by decide) (choices 1) [1,2,32] r8887 c8887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u710
  · exact u711
  · exact u712

def r8888 : Route 9 := (fun mask => (mask,id))

def c8888 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8888 : Upper (D 6) (R 6) [6,9,48,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,1] 13 (by decide) (choices 1) [2,4,32] r8888 c8888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u713
  · exact u714
  · exact u715

def r8889 : Route 9 := (fun mask => (mask,id))

def c8889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8889 : Upper (D 6) (R 6) [6,9,48,192,320,2] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,2] 13 (by decide) (choices 1) [1,4,32] r8889 c8889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u716
  · exact u717
  · exact u718

def b8890 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 200 336 36 99 163 291), lower := (rows 7 11 52 200 336 36 64 128 256), losses := [] }

theorem u8890 : Upper (D 6) (R 6) [6,9,48,192,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8891 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 456, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 11 52 392 81 34 100 228 356), lower := (rows 7 11 52 392 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 31 16 35 85 149 277), good := (rows 494 490 508 392 508 42 64 128 256) }] }

theorem u8891 : Upper (D 6) (R 6) [6,9,48,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8892 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 392 81 36 98 226 354), lower := (rows 7 11 52 392 81 36 64 128 256), losses := [] }

theorem u8892 : Upper (D 6) (R 6) [6,9,48,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8893 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 52 392 81 96 102 166 294), lower := (rows 7 11 52 392 81 96 64 128 256), losses := [] }

theorem u8893 : Upper (D 6) (R 6) [6,9,48,384,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8894 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 456, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 7 11 52 392 82 33 100 228 356), lower := (rows 7 11 52 392 82 33 64 128 256), losses := [] }

theorem u8894 : Upper (D 6) (R 6) [6,9,48,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8895 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 7 11 52 392 82 36 97 225 353), lower := (rows 7 11 52 392 82 36 64 128 256), losses := [] }

theorem u8895 : Upper (D 6) (R 6) [6,9,48,384,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8896 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 52 392 82 96 101 165 293), lower := (rows 7 11 52 392 82 96 64 128 256), losses := [] }

theorem u8896 : Upper (D 6) (R 6) [6,9,48,384,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8897 : Route 9 := (fun mask => (mask,id))

def c8897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8897 : Upper (D 6) (R 6) [6,9,48,384,68,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,384,68,1] 13 (by decide) (choices 1) [2,32] r8897 c8897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u719
  · exact u720

def r8898 : Route 9 := (fun mask => (mask,id))

def c8898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8898 : Upper (D 6) (R 6) [6,9,48,384,68,2] 13 := by
  apply FastRouting.sound _ _ [6,9,48,384,68,2] 13 (by decide) (choices 1) [1,32] r8898 c8898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u721
  · exact u722

def b8899 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 392 84 96 99 163 291), lower := (rows 7 11 52 392 84 96 64 128 256), losses := [] }

theorem u8899 : Upper (D 6) (R 6) [6,9,48,384,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8900 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 100 26 176 33 324 452 324), lower := (rows 7 11 100 26 176 33 64 128 256), losses := [] }

theorem u8900 : Upper (D 6) (R 6) [6,9,96,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8901 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 100 26 176 36 321 449 321), lower := (rows 7 11 100 26 176 36 64 128 256), losses := [] }

theorem u8901 : Upper (D 6) (R 6) [6,9,96,18,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8902 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 26 176 96 325 389 261), lower := (rows 7 11 100 26 176 96 64 128 256), losses := [] }

theorem u8902 : Upper (D 6) (R 6) [6,9,96,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8903 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 100 26 176 288 69 197 325), lower := (rows 7 11 100 26 176 288 64 128 256), losses := [] }

theorem u8903 : Upper (D 6) (R 6) [6,9,96,18,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8903 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8904 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 100 26 400 33 100 228 356), lower := (rows 7 11 100 26 400 33 64 128 256), losses := [] }

theorem u8904 : Upper (D 6) (R 6) [6,9,96,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8905 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 100 26 400 36 97 225 353), lower := (rows 7 11 100 26 400 36 64 128 256), losses := [] }

theorem u8905 : Upper (D 6) (R 6) [6,9,96,18,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8906 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 26 400 96 101 165 293), lower := (rows 7 11 100 26 400 96 64 128 256), losses := [] }

theorem u8906 : Upper (D 6) (R 6) [6,9,96,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8907 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 56 148 33 322 450 322), lower := (rows 7 11 100 56 148 33 64 128 256), losses := [] }

theorem u8907 : Upper (D 6) (R 6) [6,9,96,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8908 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 56 148 34 321 449 321), lower := (rows 7 11 100 56 148 34 64 128 256), losses := [] }

theorem u8908 : Upper (D 6) (R 6) [6,9,96,48,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8909 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 56 148 96 323 387 259), lower := (rows 7 11 100 56 148 96 64 128 256), losses := [] }

theorem u8909 : Upper (D 6) (R 6) [6,9,96,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8910 : Route 9 := (fun mask => (mask,id))

def c8910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8910 : Upper (D 6) (R 6) [6,9,96,48,132,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,132,256] 13 (by decide) (choices 1) [1,2] r8910 c8910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u723
  · exact u724

def b8911 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 100 56 208 33 326 390 262), lower := (rows 7 11 100 56 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 51 32 65 129 257), good := (rows 478 474 124 60 208 508 64 128 256) }] }

theorem u8911 : Upper (D 6) (R 6) [6,9,96,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8912 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 464, targets := 34 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 7 11 100 56 208 34 325 389 261), lower := (rows 7 11 100 56 208 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 40 19 32 65 129 257), good := (rows 469 473 108 56 208 56 64 128 256) }] }

theorem u8912 : Upper (D 6) (R 6) [6,9,96,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8913 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 56 208 36 323 387 259), lower := (rows 7 11 100 56 208 36 64 128 256), losses := [] }

theorem u8913 : Upper (D 6) (R 6) [6,9,96,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8914 : Route 9 := (fun mask => (mask,id))

def c8914 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8914 : Upper (D 6) (R 6) [6,9,96,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,192,256] 13 (by decide) (choices 1) [1,2,4] r8914 c8914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u725
  · exact u726
  · exact u727

def b8915 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 100 56 400 33 70 198 326), lower := (rows 7 11 100 56 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 51 32 65 129 257), good := (rows 478 474 124 60 400 508 64 128 256) }] }

theorem u8915 : Upper (D 6) (R 6) [6,9,96,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8916 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 464, targets := 34 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 7 11 100 56 400 34 69 197 325), lower := (rows 7 11 100 56 400 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 40 19 32 65 129 257), good := (rows 469 473 108 56 400 56 64 128 256) }] }

theorem u8916 : Upper (D 6) (R 6) [6,9,96,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8917 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 11 100 56 400 36 67 195 323), lower := (rows 7 11 100 56 400 36 64 128 256), losses := [] }

theorem u8917 : Upper (D 6) (R 6) [6,9,96,48,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8918 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 56 400 96 71 135 263), lower := (rows 7 11 100 56 400 96 64 128 256), losses := [] }

theorem u8918 : Upper (D 6) (R 6) [6,9,96,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8919 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 100 138 276 33 112 240 368), lower := (rows 7 11 100 138 276 33 64 128 256), losses := [] }

theorem u8919 : Upper (D 6) (R 6) [6,9,96,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8920 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 100 138 276 48 97 225 353), lower := (rows 7 11 100 138 276 48 64 128 256), losses := [] }

theorem u8920 : Upper (D 6) (R 6) [6,9,96,130,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8920 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8921 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 138 276 96 113 177 305), lower := (rows 7 11 100 138 276 96 64 128 256), losses := [] }

theorem u8921 : Upper (D 6) (R 6) [6,9,96,130,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8922 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 100 138 304 33 84 212 340), lower := (rows 7 11 100 138 304 33 64 128 256), losses := [] }

theorem u8922 : Upper (D 6) (R 6) [6,9,96,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8923 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 100 138 304 36 81 209 337), lower := (rows 7 11 100 138 304 36 64 128 256), losses := [] }

theorem u8923 : Upper (D 6) (R 6) [6,9,96,130,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8924 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 100 138 304 48 69 197 325), lower := (rows 7 11 100 138 304 48 64 128 256), losses := [] }

theorem u8924 : Upper (D 6) (R 6) [6,9,96,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8924 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8925 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 138 304 96 85 149 277), lower := (rows 7 11 100 138 304 96 64 128 256), losses := [] }

theorem u8925 : Upper (D 6) (R 6) [6,9,96,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8926 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 152 50 33 324 452 324), lower := (rows 7 11 100 152 50 33 64 128 256), losses := [] }

theorem u8926 : Upper (D 6) (R 6) [6,9,96,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8927 : PairBound 9 := { available := 321, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 0, region := 48, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 100 152 50 36 321 449 321), lower := (rows 7 11 100 152 50 36 64 128 256), losses := [] }

theorem u8927 : Upper (D 6) (R 6) [6,9,96,144,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8928 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 152 50 96 325 389 261), lower := (rows 7 11 100 152 50 96 64 128 256), losses := [] }

theorem u8928 : Upper (D 6) (R 6) [6,9,96,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8929 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 11 100 152 50 288 69 197 325), lower := (rows 7 11 100 152 50 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 307 67 131 259), good := (rows 485 493 100 188 508 288 64 128 288) }] }

theorem u8929 : Upper (D 6) (R 6) [6,9,96,144,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8929 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8930 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 152 273 34 100 228 356), lower := (rows 7 11 100 152 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 55 24 16 35 119 183 311), good := (rows 486 494 484 476 508 486 64 128 256) }] }

theorem u8930 : Upper (D 6) (R 6) [6,9,96,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8931 : PairBound 9 := { available := 98, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 152 273 36 98 226 354), lower := (rows 7 11 100 152 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 87 24 16 127 67 131 259), good := (rows 486 494 100 188 508 36 100 128 256) }] }

theorem u8931 : Upper (D 6) (R 6) [6,9,96,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8932 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 152 273 96 102 166 294), lower := (rows 7 11 100 152 273 96 64 128 256), losses := [] }

theorem u8932 : Upper (D 6) (R 6) [6,9,96,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8933 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 152 274 33 100 228 356), lower := (rows 7 11 100 152 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 17 32 100 164 292), good := (rows 478 26 492 152 274 508 64 128 256) }] }

theorem u8933 : Upper (D 6) (R 6) [6,9,96,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8934 : PairBound 9 := { available := 97, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 11 100 152 274 36 97 225 353), lower := (rows 7 11 100 152 274 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 87 24 16 127 67 131 259), good := (rows 485 493 100 188 508 36 100 128 256) }] }

theorem u8934 : Upper (D 6) (R 6) [6,9,96,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8935 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 152 274 96 101 165 293), lower := (rows 7 11 100 152 274 96 64 128 256), losses := [] }

theorem u8935 : Upper (D 6) (R 6) [6,9,96,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8936 : Route 9 := (fun mask => (mask,id))

def c8936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8936 : Upper (D 6) (R 6) [6,9,96,144,260,1] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,260,1] 13 (by decide) (choices 1) [2,32] r8936 c8936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u728
  · exact u729

theorem m8937_1 : Upper (D 6) (R 6) [6,9,96,144,260,2,1] 13 :=
  permutation_upper _ _ _ [6,9,96,144,260,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u728

def r8937 : Route 9 := (fun mask => (mask,id))

def c8937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8937 : Upper (D 6) (R 6) [6,9,96,144,260,2] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,260,2] 13 (by decide) (choices 1) [1,32] r8937 c8937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m8937_1
  · exact u730

def b8938 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 152 276 96 99 163 291), lower := (rows 7 11 100 152 276 96 64 128 256), losses := [] }

theorem u8938 : Upper (D 6) (R 6) [6,9,96,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8939 : PairBound 9 := { available := 70, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 100 152 304 33 70 198 326), lower := (rows 7 11 100 152 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 48 32 65 129 257), good := (rows 454 458 124 152 316 508 64 128 256) }] }

theorem u8939 : Upper (D 6) (R 6) [6,9,96,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8939
end Delivery.IrregularNine14.P06
