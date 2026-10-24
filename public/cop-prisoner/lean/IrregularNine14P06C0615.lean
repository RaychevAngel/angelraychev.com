import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0359
import IrregularNine14P06C0360

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36900 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 388 13 50 117 85 213 341), lower := (rows 35 74 388 13 50 32 64 128 256), losses := [] }

theorem u36900 : Upper (D 6) (R 6) [34,72,384,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36901 : Route 9 := (fun mask => (mask,id))

def c36901 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36901 : Upper (D 6) (R 6) [34,72,384,5,36] 13 := by
  apply FastRouting.sound _ _ [34,72,384,5,36] 13 (by decide) (choices 1) [1,2,16,64] r36901 c36901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21568
  · exact u21569
  · exact u21570
  · exact u21571

def r36902 : Route 9 := (fun mask => (mask,id))

def c36902 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36902 : Upper (D 6) (R 6) [34,72,384,5,65] 13 := by
  apply FastRouting.sound _ _ [34,72,384,5,65] 13 (by decide) (choices 1) [2,4,16] r36902 c36902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21572
  · exact u21573
  · exact u21574

def b36903 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 388 13 82 53 117 181 309), lower := (rows 35 74 388 13 82 32 64 128 256), losses := [] }

theorem u36903 : Upper (D 6) (R 6) [34,72,384,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36904 : Route 9 := (fun mask => (mask,id))

def c36904 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36904 : Upper (D 6) (R 6) [34,72,384,5,68] 13 := by
  apply FastRouting.sound _ _ [34,72,384,5,68] 13 (by decide) (choices 1) [1,2,16] r36904 c36904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21575
  · exact u21576
  · exact u21577

def r36905 : Route 9 := (fun mask => (mask,id))

def c36905 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36905 : Upper (D 6) (R 6) [34,72,384,5,96] 13 := by
  apply FastRouting.sound _ _ [34,72,384,5,96] 13 (by decide) (choices 1) [1,2,4,16] r36905 c36905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21578
  · exact u21579
  · exact u21580
  · exact u21581

def r36906 : Route 9 := (fun mask => (mask,id))

def c36906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36906 : Upper (D 6) (R 6) [34,72,384,6,5] 13 := by
  apply FastRouting.sound _ _ [34,72,384,6,5] 13 (by decide) (choices 1) [1,16,64] r36906 c36906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21582
  · exact u21583
  · exact u21584

def b36907 : PairBound 9 := { available := 85, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 388 14 49 117 85 213 341), lower := (rows 35 74 388 14 49 32 64 128 256), losses := [] }

theorem u36907 : Upper (D 6) (R 6) [34,72,384,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36908 : Route 9 := (fun mask => (mask,id))

def c36908 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36908 : Upper (D 6) (R 6) [34,72,384,6,36] 13 := by
  apply FastRouting.sound _ _ [34,72,384,6,36] 13 (by decide) (choices 1) [1,16,64] r36908 c36908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21585
  · exact u21586
  · exact u21587

def b36909 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 4, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 388 14 81 53 117 181 309), lower := (rows 35 74 388 14 81 32 64 128 256), losses := [] }

theorem u36909 : Upper (D 6) (R 6) [34,72,384,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36910 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 388 14 84 49 113 177 305), lower := (rows 35 74 388 14 84 32 64 128 256), losses := [] }

theorem u36910 : Upper (D 6) (R 6) [34,72,384,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36911 : Route 9 := (fun mask => (mask,id))

def c36911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36911 : Upper (D 6) (R 6) [34,72,384,6,96] 13 := by
  apply FastRouting.sound _ _ [34,72,384,6,96] 13 (by decide) (choices 1) [1,4,16] r36911 c36911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21588
  · exact u21589
  · exact u21590

def b36912 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 388 25 19 100 100 228 356), lower := (rows 35 74 388 25 19 32 64 128 256), losses := [] }

theorem u36912 : Upper (D 6) (R 6) [34,72,384,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36913 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 74 388 25 21 102 102 230 358), lower := (rows 35 74 388 25 21 32 64 128 256), losses := [] }

theorem u36913 : Upper (D 6) (R 6) [34,72,384,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36914 : Route 9 := (fun mask => (mask,id))

def c36914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36914 : Upper (D 6) (R 6) [34,72,384,17,6] 13 := by
  apply FastRouting.sound _ _ [34,72,384,17,6] 13 (by decide) (choices 1) [1,4,64] r36914 c36914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21591
  · exact u21592
  · exact u21593

def b36915 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 388 25 49 102 70 198 326), lower := (rows 35 74 388 25 49 32 64 128 256), losses := [] }

theorem u36915 : Upper (D 6) (R 6) [34,72,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36916 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 388 25 50 101 69 197 325), lower := (rows 35 74 388 25 50 32 64 128 256), losses := [] }

theorem u36916 : Upper (D 6) (R 6) [34,72,384,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36917 : Route 9 := (fun mask => (mask,id))

def c36917 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36917 : Upper (D 6) (R 6) [34,72,384,17,36] 13 := by
  apply FastRouting.sound _ _ [34,72,384,17,36] 13 (by decide) (choices 1) [1,2,4,64] r36917 c36917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21594
  · exact u21595
  · exact u21596
  · exact u21597

def b36918 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 10, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 388 25 81 38 102 166 294), lower := (rows 35 74 388 25 81 32 64 128 256), losses := [] }

theorem u36918 : Upper (D 6) (R 6) [34,72,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36919 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 388 25 82 37 101 165 293), lower := (rows 35 74 388 25 82 32 64 128 256), losses := [] }

theorem u36919 : Upper (D 6) (R 6) [34,72,384,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36920 : Route 9 := (fun mask => (mask,id))

def c36920 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36920 : Upper (D 6) (R 6) [34,72,384,17,68] 13 := by
  apply FastRouting.sound _ _ [34,72,384,17,68] 13 (by decide) (choices 1) [1,2,4] r36920 c36920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21598
  · exact u21599
  · exact u21600

def b36921 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 388 25 112 39 71 135 263), lower := (rows 35 74 388 25 112 32 64 128 256), losses := [] }

theorem u36921 : Upper (D 6) (R 6) [34,72,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36922 : Route 9 := (fun mask => (mask,id))

def c36922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36922 : Upper (D 6) (R 6) [34,72,384,18,5] 13 := by
  apply FastRouting.sound _ _ [34,72,384,18,5] 13 (by decide) (choices 1) [1,4,64] r36922 c36922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21601
  · exact u21602
  · exact u21603

def b36923 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 388 26 49 101 69 197 325), lower := (rows 35 74 388 26 49 32 64 128 256), losses := [] }

theorem u36923 : Upper (D 6) (R 6) [34,72,384,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36924 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 74 388 26 52 101 69 197 325), lower := (rows 35 74 388 26 52 32 64 128 256), losses := [] }

theorem u36924 : Upper (D 6) (R 6) [34,72,384,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36925 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 388 26 81 37 101 165 293), lower := (rows 35 74 388 26 81 32 64 128 256), losses := [] }

theorem u36925 : Upper (D 6) (R 6) [34,72,384,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36926 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 388 26 84 37 101 165 293), lower := (rows 35 74 388 26 84 32 64 128 256), losses := [] }

theorem u36926 : Upper (D 6) (R 6) [34,72,384,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36927 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 388 26 112 37 69 133 261), lower := (rows 35 74 388 26 112 32 64 128 256), losses := [] }

theorem u36927 : Upper (D 6) (R 6) [34,72,384,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36928 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 388 28 19 101 101 229 357), lower := (rows 35 74 388 28 19 32 64 128 256), losses := [] }

theorem u36928 : Upper (D 6) (R 6) [34,72,384,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36929 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 388 28 21 99 99 227 355), lower := (rows 35 74 388 28 21 32 64 128 256), losses := [] }

theorem u36929 : Upper (D 6) (R 6) [34,72,384,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36930 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 388 28 22 97 97 225 353), lower := (rows 35 74 388 28 22 32 64 128 256), losses := [] }

theorem u36930 : Upper (D 6) (R 6) [34,72,384,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36931 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 388 28 49 103 71 199 327), lower := (rows 35 74 388 28 49 32 64 128 256), losses := [] }

theorem u36931 : Upper (D 6) (R 6) [34,72,384,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36932 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 388 28 50 101 69 197 325), lower := (rows 35 74 388 28 50 32 64 128 256), losses := [] }

theorem u36932 : Upper (D 6) (R 6) [34,72,384,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36933 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 388 28 52 99 67 195 323), lower := (rows 35 74 388 28 52 32 64 128 256), losses := [] }

theorem u36933 : Upper (D 6) (R 6) [34,72,384,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36934 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 74 388 28 81 39 103 167 295), lower := (rows 35 74 388 28 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 23 24 16 35 0 131 259), good := (rows 423 431 388 28 445 32 0 128 256) }] }

theorem u36934 : Upper (D 6) (R 6) [34,72,384,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36935 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 388 28 82 37 101 165 293), lower := (rows 35 74 388 28 82 32 64 128 256), losses := [] }

theorem u36935 : Upper (D 6) (R 6) [34,72,384,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36936 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 388 28 84 35 99 163 291), lower := (rows 35 74 388 28 84 32 64 128 256), losses := [] }

theorem u36936 : Upper (D 6) (R 6) [34,72,384,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36937 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,6),(2,5),(2,6)], upper := (rows 35 74 388 28 112 39 71 135 263), lower := (rows 35 74 388 28 112 32 64 128 256), losses := [] }

theorem u36937 : Upper (D 6) (R 6) [34,72,384,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36938 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 388 44 19 117 85 213 341), lower := (rows 35 74 388 44 19 32 64 128 256), losses := [] }

theorem u36938 : Upper (D 6) (R 6) [34,72,384,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36939 : Route 9 := (fun mask => (mask,id))

def c36939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36939 : Upper (D 6) (R 6) [34,72,384,36,5] 13 := by
  apply FastRouting.sound _ _ [34,72,384,36,5] 13 (by decide) (choices 1) [1,2,16,64] r36939 c36939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21604
  · exact u21605
  · exact u21606
  · exact u21607

def b36940 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 388 44 22 113 81 209 337), lower := (rows 35 74 388 44 22 32 64 128 256), losses := [] }

theorem u36940 : Upper (D 6) (R 6) [34,72,384,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36941 : Route 9 := (fun mask => (mask,id))

def c36941 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36941 : Upper (D 6) (R 6) [34,72,384,36,65] 13 := by
  apply FastRouting.sound _ _ [34,72,384,36,65] 13 (by decide) (choices 1) [1,2,4,16] r36941 c36941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21608
  · exact u21609
  · exact u21610
  · exact u21611

def b36942 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 388 44 82 53 85 149 277), lower := (rows 35 74 388 44 82 32 64 128 256), losses := [] }

theorem u36942 : Upper (D 6) (R 6) [34,72,384,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36943 : Route 9 := (fun mask => (mask,id))

def c36943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36943 : Upper (D 6) (R 6) [34,72,384,36,68] 13 := by
  apply FastRouting.sound _ _ [34,72,384,36,68] 13 (by decide) (choices 1) [1,2,16] r36943 c36943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21612
  · exact u21613
  · exact u21614

def b36944 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 388 56 19 101 69 197 325), lower := (rows 35 74 388 56 19 32 64 128 256), losses := [] }

theorem u36944 : Upper (D 6) (R 6) [34,72,384,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36945 : Route 9 := (fun mask => (mask,id))

def c36945 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36945 : Upper (D 6) (R 6) [34,72,384,48,5] 13 := by
  apply FastRouting.sound _ _ [34,72,384,48,5] 13 (by decide) (choices 1) [1,2,4,64] r36945 c36945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21615
  · exact u21616
  · exact u21617
  · exact u21618

def b36946 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 35 74 388 56 22 101 69 197 325), lower := (rows 35 74 388 56 22 32 64 128 256), losses := [] }

theorem u36946 : Upper (D 6) (R 6) [34,72,384,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36947 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 388 56 81 39 71 135 263), lower := (rows 35 74 388 56 81 32 64 128 256), losses := [] }

theorem u36947 : Upper (D 6) (R 6) [34,72,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36948 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 388 56 82 37 69 133 261), lower := (rows 35 74 388 56 82 32 64 128 256), losses := [] }

theorem u36948 : Upper (D 6) (R 6) [34,72,384,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36949 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 388 56 84 39 71 135 263), lower := (rows 35 74 388 56 84 32 64 128 256), losses := [] }

theorem u36949 : Upper (D 6) (R 6) [34,72,384,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36950 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 131 44 25 22 356 324 452 324), lower := (rows 35 131 44 25 22 32 64 128 256), losses := [] }

theorem u36950 : Upper (D 6) (R 6) [34,129,40,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36951 : Route 9 := (fun mask => (mask,id))

def c36951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36951 : Upper (D 6) (R 6) [34,129,40,17,66] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17,66] 13 (by decide) (choices 1) [4,64,256] r36951 c36951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21619
  · exact u21620
  · exact u21621

def r36952 : Route 9 := (fun mask => (mask,id))

def c36952 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36952 : Upper (D 6) (R 6) [34,129,40,17,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17,68] 13 (by decide) (choices 1) [2,4,64,256] r36952 c36952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21622
  · exact u21623
  · exact u21624
  · exact u21625

def r36953 : Route 9 := (fun mask => (mask,id))

def c36953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36953 : Upper (D 6) (R 6) [34,129,40,17,258] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17,258] 13 (by decide) (choices 1) [4,64] r36953 c36953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21626
  · exact u21627

def r36954 : Route 9 := (fun mask => (mask,id))

def c36954 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36954 : Upper (D 6) (R 6) [34,129,40,17,260] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17,260] 13 (by decide) (choices 1) [2,4,64] r36954 c36954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21628
  · exact u21629
  · exact u21630

def r36955 : Route 9 := (fun mask => (mask,id))

def c36955 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36955 : Upper (D 6) (R 6) [34,129,40,17,320] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17,320] 13 (by decide) (choices 1) [2,4,64] r36955 c36955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21631
  · exact u21632
  · exact u21633

def b36956 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 131 44 26 21 356 324 452 324), lower := (rows 35 131 44 26 21 32 64 128 256), losses := [] }

theorem u36956 : Upper (D 6) (R 6) [34,129,40,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36957 : Route 9 := (fun mask => (mask,id))

def c36957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36957 : Upper (D 6) (R 6) [34,129,40,18,65] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18,65] 13 (by decide) (choices 1) [4,64,256] r36957 c36957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21634
  · exact u21635
  · exact u21636

def r36958 : Route 9 := (fun mask => (mask,id))

def c36958 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36958 : Upper (D 6) (R 6) [34,129,40,18,68] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18,68] 13 (by decide) (choices 1) [1,4,64,256] r36958 c36958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21637
  · exact u21638
  · exact u21639
  · exact u21640

def r36959 : Route 9 := (fun mask => (mask,id))

def c36959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36959 : Upper (D 6) (R 6) [34,129,40,18,257] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18,257] 13 (by decide) (choices 1) [4,64] r36959 c36959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21641
  · exact u21642

#print axioms u36959
end Delivery.IrregularNine14.P06
