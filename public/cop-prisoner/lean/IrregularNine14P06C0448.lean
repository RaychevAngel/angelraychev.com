import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0140
import IrregularNine14P06C0141

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26880 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 4, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 41 134 324 13 81 34 114 178 306), lower := (rows 41 134 324 13 81 34 64 128 256), losses := [] }

theorem u26880 : Upper (D 6) (R 6) [40,132,320,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26881 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 41 134 324 13 81 48 98 162 290), lower := (rows 41 134 324 13 81 48 64 128 256), losses := [] }

theorem u26881 : Upper (D 6) (R 6) [40,132,320,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26881 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26882 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 134 324 13 82 33 114 178 306), lower := (rows 41 134 324 13 82 33 64 128 256), losses := [] }

theorem u26882 : Upper (D 6) (R 6) [40,132,320,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26883 : Route 9 := (fun mask => (mask,id))

def c26883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26883 : Upper (D 6) (R 6) [40,132,320,5,66,2] 13 := by
  apply FastRouting.sound _ _ [40,132,320,5,66,2] 13 (by decide) (choices 1) [1,16,32] r26883 c26883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8434
  · exact u8435
  · exact u8436

def r26884 : Route 9 := (fun mask => (mask,id))

def c26884 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26884 : Upper (D 6) (R 6) [40,132,320,5,66,16] 13 := by
  apply FastRouting.sound _ _ [40,132,320,5,66,16] 13 (by decide) (choices 1) [1,2,32] r26884 c26884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8437
  · exact u8438
  · exact u8439

def b26885 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 324 13 112 33 82 146 274), lower := (rows 41 134 324 13 112 33 64 128 256), losses := [] }

theorem u26885 : Upper (D 6) (R 6) [40,132,320,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26886 : Route 9 := (fun mask => (mask,id))

def c26886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26886 : Upper (D 6) (R 6) [40,132,320,5,96,2] 13 := by
  apply FastRouting.sound _ _ [40,132,320,5,96,2] 13 (by decide) (choices 1) [1,2,16] r26886 c26886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8440
  · exact u8441
  · exact u8442

def b26887 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 324 13 112 48 67 131 259), lower := (rows 41 134 324 13 112 48 64 128 256), losses := [] }

theorem u26887 : Upper (D 6) (R 6) [40,132,320,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26887 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26888 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 25 82 33 102 166 294), lower := (rows 41 134 324 25 82 33 64 128 256), losses := [] }

theorem u26888 : Upper (D 6) (R 6) [40,132,320,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26889 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 324 25 82 34 101 165 293), lower := (rows 41 134 324 25 82 34 64 128 256), losses := [] }

theorem u26889 : Upper (D 6) (R 6) [40,132,320,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26890 : PairBound 9 := { available := 35, camps := [], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 134 324 25 82 36 99 163 291), lower := (rows 41 134 324 25 82 36 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 24 16 38 64 128 256), good := (rows 41 164 356 25 121 36 64 128 256) },{ target := 6, region := (rows 17 2 4 24 16 38 0 144 272), good := (rows 41 166 292 409 443 36 0 128 256) }] }

theorem u26890 : Upper (D 6) (R 6) [40,132,320,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26891 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 324 26 21 33 98 226 354), lower := (rows 41 134 324 26 21 33 64 128 256), losses := [] }

theorem u26891 : Upper (D 6) (R 6) [40,132,320,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26892 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 324 26 21 34 97 225 353), lower := (rows 41 134 324 26 21 34 64 128 256), losses := [] }

theorem u26892 : Upper (D 6) (R 6) [40,132,320,18,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26893 : Route 9 := (fun mask => (mask,id))

def c26893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26893 : Upper (D 6) (R 6) [40,132,320,18,5,64] 13 := by
  apply FastRouting.sound _ _ [40,132,320,18,5,64] 13 (by decide) (choices 1) [1,2,32] r26893 c26893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8443
  · exact u8444
  · exact u8445

def b26894 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 26 81 33 102 166 294), lower := (rows 41 134 324 26 81 33 64 128 256), losses := [] }

theorem u26894 : Upper (D 6) (R 6) [40,132,320,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26895 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 324 26 81 34 101 165 293), lower := (rows 41 134 324 26 81 34 64 128 256), losses := [] }

theorem u26895 : Upper (D 6) (R 6) [40,132,320,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26896 : Route 9 := (fun mask => (mask,id))

def c26896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26896 : Upper (D 6) (R 6) [40,132,320,18,65,4] 13 := by
  apply FastRouting.sound _ _ [40,132,320,18,65,4] 13 (by decide) (choices 1) [1,2,32] r26896 c26896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8446
  · exact u8447
  · exact u8448

def b26897 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 26 112 33 71 135 263), lower := (rows 41 134 324 26 112 33 64 128 256), losses := [] }

theorem u26897 : Upper (D 6) (R 6) [40,132,320,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26898 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 41 134 324 26 112 34 69 133 261), lower := (rows 41 134 324 26 112 34 64 128 256), losses := [] }

theorem u26898 : Upper (D 6) (R 6) [40,132,320,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26899 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 41 134 324 26 112 36 67 131 259), lower := (rows 41 134 324 26 112 36 64 128 256), losses := [] }

theorem u26899 : Upper (D 6) (R 6) [40,132,320,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26900 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 324 28 19 33 98 226 354), lower := (rows 41 134 324 28 19 33 64 128 256), losses := [] }

theorem u26900 : Upper (D 6) (R 6) [40,132,320,20,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26901 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 324 28 19 34 97 225 353), lower := (rows 41 134 324 28 19 34 64 128 256), losses := [] }

theorem u26901 : Upper (D 6) (R 6) [40,132,320,20,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26902 : Route 9 := (fun mask => (mask,id))

def c26902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26902 : Upper (D 6) (R 6) [40,132,320,20,3,64] 13 := by
  apply FastRouting.sound _ _ [40,132,320,20,3,64] 13 (by decide) (choices 1) [1,2,32] r26902 c26902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8449
  · exact u8450
  · exact u8451

def b26903 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 324 28 50 33 67 195 323), lower := (rows 41 134 324 28 50 33 64 128 256), losses := [] }

theorem u26903 : Upper (D 6) (R 6) [40,132,320,20,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26904 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 134 324 28 50 34 65 193 321), lower := (rows 41 134 324 28 50 34 64 128 256), losses := [] }

theorem u26904 : Upper (D 6) (R 6) [40,132,320,20,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26905 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 41 134 324 28 50 96 67 131 259), lower := (rows 41 134 324 28 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 100 64 128 256), good := (rows 40 190 356 60 58 96 96 128 256) }] }

theorem u26905 : Upper (D 6) (R 6) [40,132,320,20,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26906 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 134 324 28 81 33 98 162 290), lower := (rows 41 134 324 28 81 33 64 128 256), losses := [] }

theorem u26906 : Upper (D 6) (R 6) [40,132,320,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26907 : Route 9 := (fun mask => (mask,id))

def c26907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26907 : Upper (D 6) (R 6) [40,132,320,20,65,2] 13 := by
  apply FastRouting.sound _ _ [40,132,320,20,65,2] 13 (by decide) (choices 1) [1,2,32] r26907 c26907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8452
  · exact u8453
  · exact u8454

def b26908 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 28 82 33 99 163 291), lower := (rows 41 134 324 28 82 33 64 128 256), losses := [] }

theorem u26908 : Upper (D 6) (R 6) [40,132,320,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26909 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 41 134 324 28 82 34 97 161 289), lower := (rows 41 134 324 28 82 34 64 128 256), losses := [] }

theorem u26909 : Upper (D 6) (R 6) [40,132,320,20,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26910 : Route 9 := (fun mask => (mask,id))

def c26910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26910 : Upper (D 6) (R 6) [40,132,320,65,3,2] 13 := by
  apply FastRouting.sound _ _ [40,132,320,65,3,2] 13 (by decide) (choices 1) [4,16,32] r26910 c26910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8455
  · exact u8456
  · exact u8457

def b26911 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 41, targets := 2 },{ cop := 4, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(3,1)], upper := (rows 41 134 324 73 19 36 114 178 306), lower := (rows 41 134 324 73 19 36 64 128 256), losses := [] }

theorem u26911 : Upper (D 6) (R 6) [40,132,320,65,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26912 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 324 73 19 48 102 166 294), lower := (rows 41 134 324 73 19 48 64 128 256), losses := [] }

theorem u26912 : Upper (D 6) (R 6) [40,132,320,65,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26912 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26913 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 324 73 50 33 86 150 278), lower := (rows 41 134 324 73 50 33 64 128 256), losses := [] }

theorem u26913 : Upper (D 6) (R 6) [40,132,320,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26914 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 48, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 41 134 324 73 50 34 85 149 277), lower := (rows 41 134 324 73 50 34 64 128 256), losses := [] }

theorem u26914 : Upper (D 6) (R 6) [40,132,320,65,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26915 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 2, region := 41, targets := 2 }], pairs := [(0,1),(4,0),(4,6)], upper := (rows 41 134 324 73 50 36 83 147 275), lower := (rows 41 134 324 73 50 36 64 128 256), losses := [] }

theorem u26915 : Upper (D 6) (R 6) [40,132,320,65,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26916 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 324 73 50 48 71 135 263), lower := (rows 41 134 324 73 50 48 64 128 256), losses := [] }

theorem u26916 : Upper (D 6) (R 6) [40,132,320,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26916 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26917 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 324 73 52 33 82 146 274), lower := (rows 41 134 324 73 52 33 64 128 256), losses := [] }

theorem u26917 : Upper (D 6) (R 6) [40,132,320,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26918 : Route 9 := (fun mask => (mask,id))

def c26918 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26918 : Upper (D 6) (R 6) [40,132,320,65,36,2] 13 := by
  apply FastRouting.sound _ _ [40,132,320,65,36,2] 13 (by decide) (choices 1) [1,2,16] r26918 c26918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8458
  · exact u8459
  · exact u8460

def b26919 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 324 73 52 48 67 131 259), lower := (rows 41 134 324 73 52 48 64 128 256), losses := [] }

theorem u26919 : Upper (D 6) (R 6) [40,132,320,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26919 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26920 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 134 324 74 19 33 116 180 308), lower := (rows 41 134 324 74 19 33 64 128 256), losses := [] }

theorem u26920 : Upper (D 6) (R 6) [40,132,320,66,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26921 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 356, targets := 2 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 134 324 74 19 36 113 177 305), lower := (rows 41 134 324 74 19 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 20 8 16 54 80 144 272), good := (rows 41 164 356 105 501 36 64 128 256) },{ target := 6, region := (rows 9 2 4 8 24 38 0 153 281), good := (rows 441 166 292 443 435 36 0 128 256) }] }

theorem u26921 : Upper (D 6) (R 6) [40,132,320,66,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26922 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 134 324 74 19 48 101 165 293), lower := (rows 41 134 324 74 19 48 64 128 256), losses := [] }

theorem u26922 : Upper (D 6) (R 6) [40,132,320,66,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26922 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26923 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 74 21 33 114 178 306), lower := (rows 41 134 324 74 21 33 64 128 256), losses := [] }

theorem u26923 : Upper (D 6) (R 6) [40,132,320,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26924 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 324 74 21 34 113 177 305), lower := (rows 41 134 324 74 21 34 64 128 256), losses := [] }

theorem u26924 : Upper (D 6) (R 6) [40,132,320,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26925 : Route 9 := (fun mask => (mask,id))

def c26925 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26925 : Upper (D 6) (R 6) [40,132,320,66,5,16] 13 := by
  apply FastRouting.sound _ _ [40,132,320,66,5,16] 13 (by decide) (choices 1) [1,2,32] r26925 c26925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8461
  · exact u8462
  · exact u8463

def b26926 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 134 324 74 50 33 85 149 277), lower := (rows 41 134 324 74 50 33 64 128 256), losses := [] }

theorem u26926 : Upper (D 6) (R 6) [40,132,320,66,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26927 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 41 134 324 74 50 36 81 145 273), lower := (rows 41 134 324 74 50 36 64 128 256), losses := [] }

theorem u26927 : Upper (D 6) (R 6) [40,132,320,66,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26928 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 134 324 74 50 48 69 133 261), lower := (rows 41 134 324 74 50 48 64 128 256), losses := [] }

theorem u26928 : Upper (D 6) (R 6) [40,132,320,66,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26928 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26929 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 74 52 33 83 147 275), lower := (rows 41 134 324 74 52 33 64 128 256), losses := [] }

theorem u26929 : Upper (D 6) (R 6) [40,132,320,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26930 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 48, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 41 134 324 74 52 34 81 145 273), lower := (rows 41 134 324 74 52 34 64 128 256), losses := [] }

theorem u26930 : Upper (D 6) (R 6) [40,132,320,66,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26931 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 134 324 74 52 48 67 131 259), lower := (rows 41 134 324 74 52 48 64 128 256), losses := [] }

theorem u26931 : Upper (D 6) (R 6) [40,132,320,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26931 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26932 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 88 19 33 102 166 294), lower := (rows 41 134 324 88 19 33 64 128 256), losses := [] }

theorem u26932 : Upper (D 6) (R 6) [40,132,320,80,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26933 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 41 134 324 88 19 34 101 165 293), lower := (rows 41 134 324 88 19 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 21 24 16 32 65 129 257), good := (rows 493 132 324 92 477 32 64 128 256) },{ target := 2, region := (rows 9 2 0 8 16 50 64 128 256), good := (rows 41 162 320 121 51 34 64 128 256) }] }

theorem u26933 : Upper (D 6) (R 6) [40,132,320,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26934 : Route 9 := (fun mask => (mask,id))

def c26934 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26934 : Upper (D 6) (R 6) [40,132,320,80,3,4] 13 := by
  apply FastRouting.sound _ _ [40,132,320,80,3,4] 13 (by decide) (choices 1) [1,2,32] r26934 c26934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8464
  · exact u8465
  · exact u8466

def b26935 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 134 324 88 21 33 98 162 290), lower := (rows 41 134 324 88 21 33 64 128 256), losses := [] }

theorem u26935 : Upper (D 6) (R 6) [40,132,320,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26936 : Route 9 := (fun mask => (mask,id))

def c26936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26936 : Upper (D 6) (R 6) [40,132,320,80,5,2] 13 := by
  apply FastRouting.sound _ _ [40,132,320,80,5,2] 13 (by decide) (choices 1) [1,2,32] r26936 c26936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8467
  · exact u8468
  · exact u8469

def b26937 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 324 88 50 33 71 135 263), lower := (rows 41 134 324 88 50 33 64 128 256), losses := [] }

theorem u26937 : Upper (D 6) (R 6) [40,132,320,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26938 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 48, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 41 134 324 88 50 34 69 133 261), lower := (rows 41 134 324 88 50 34 64 128 256), losses := [] }

theorem u26938 : Upper (D 6) (R 6) [40,132,320,80,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26939 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 41 134 324 88 50 36 67 131 259), lower := (rows 41 134 324 88 50 36 64 128 256), losses := [] }

theorem u26939 : Upper (D 6) (R 6) [40,132,320,80,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26939
end Delivery.IrregularNine14.P06
