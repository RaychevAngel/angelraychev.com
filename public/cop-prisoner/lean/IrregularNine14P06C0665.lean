import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0443
import IrregularNine14P06C0444

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39900 : Route 9 := (fun mask => (mask,id))

def c39900 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39900 : Upper (D 6) (R 6) [40,129,320,17,66] 13 := by
  apply FastRouting.sound _ _ [40,129,320,17,66] 13 (by decide) (choices 1) [2,4] r39900 c39900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26609
  · exact u26610

def b39901 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 131 324 25 84 38 102 166 294), lower := (rows 41 131 324 25 84 32 64 128 256), losses := [] }

theorem u39901 : Upper (D 6) (R 6) [40,129,320,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39902 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 25 112 38 70 134 262), lower := (rows 41 131 324 25 112 32 64 128 256), losses := [] }

theorem u39902 : Upper (D 6) (R 6) [40,129,320,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39903 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 41 131 324 26 19 100 100 228 356), lower := (rows 41 131 324 26 19 32 64 128 256), losses := [] }

theorem u39903 : Upper (D 6) (R 6) [40,129,320,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39904 : Route 9 := (fun mask => (mask,id))

def c39904 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39904 : Upper (D 6) (R 6) [40,129,320,18,5] 13 := by
  apply FastRouting.sound _ _ [40,129,320,18,5] 13 (by decide) (choices 1) [2,4,64] r39904 c39904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26611
  · exact u26612
  · exact u26613

def b39905 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 131 324 26 22 101 101 229 357), lower := (rows 41 131 324 26 22 32 64 128 256), losses := [] }

theorem u39905 : Upper (D 6) (R 6) [40,129,320,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39906 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 324 26 49 102 70 198 326), lower := (rows 41 131 324 26 49 32 64 128 256), losses := [] }

theorem u39906 : Upper (D 6) (R 6) [40,129,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39907 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 131 324 26 50 101 69 197 325), lower := (rows 41 131 324 26 50 32 64 128 256), losses := [] }

theorem u39907 : Upper (D 6) (R 6) [40,129,320,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39908 : Route 9 := (fun mask => (mask,id))

def c39908 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39908 : Upper (D 6) (R 6) [40,129,320,18,36] 13 := by
  apply FastRouting.sound _ _ [40,129,320,18,36] 13 (by decide) (choices 1) [1,2,4,64] r39908 c39908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26614
  · exact u26615
  · exact u26616
  · exact u26617

def r39909 : Route 9 := (fun mask => (mask,id))

def c39909 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39909 : Upper (D 6) (R 6) [40,129,320,18,65] 13 := by
  apply FastRouting.sound _ _ [40,129,320,18,65] 13 (by decide) (choices 1) [2,4] r39909 c39909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26618
  · exact u26619

def b39910 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 131 324 26 82 37 101 165 293), lower := (rows 41 131 324 26 82 32 64 128 256), losses := [] }

theorem u39910 : Upper (D 6) (R 6) [40,129,320,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39911 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 131 324 26 84 39 103 167 295), lower := (rows 41 131 324 26 84 32 64 128 256), losses := [] }

theorem u39911 : Upper (D 6) (R 6) [40,129,320,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39912 : Route 9 := (fun mask => (mask,id))

def c39912 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39912 : Upper (D 6) (R 6) [40,129,320,18,96] 13 := by
  apply FastRouting.sound _ _ [40,129,320,18,96] 13 (by decide) (choices 1) [1,2,4] r39912 c39912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26620
  · exact u26621
  · exact u26622

def b39913 : PairBound 9 := { available := 102, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 324 28 19 102 102 230 358), lower := (rows 41 131 324 28 19 32 64 128 256), losses := [] }

theorem u39913 : Upper (D 6) (R 6) [40,129,320,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39914 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 324 28 21 98 98 226 354), lower := (rows 41 131 324 28 21 32 64 128 256), losses := [] }

theorem u39914 : Upper (D 6) (R 6) [40,129,320,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39915 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 324 28 22 99 99 227 355), lower := (rows 41 131 324 28 22 32 64 128 256), losses := [] }

theorem u39915 : Upper (D 6) (R 6) [40,129,320,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39916 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 324 28 49 102 70 198 326), lower := (rows 41 131 324 28 49 32 64 128 256), losses := [] }

theorem u39916 : Upper (D 6) (R 6) [40,129,320,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39917 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 131 324 28 50 103 71 199 327), lower := (rows 41 131 324 28 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 23 24 16 0 67 131 259), good := (rows 463 455 324 28 478 0 64 128 256) }] }

theorem u39917 : Upper (D 6) (R 6) [40,129,320,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39918 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 324 28 52 99 67 195 323), lower := (rows 41 131 324 28 52 32 64 128 256), losses := [] }

theorem u39918 : Upper (D 6) (R 6) [40,129,320,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39919 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 1, region := 356, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 41 131 324 28 81 38 102 166 294), lower := (rows 41 131 324 28 81 32 64 128 256), losses := [] }

theorem u39919 : Upper (D 6) (R 6) [40,129,320,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39920 : Route 9 := (fun mask => (mask,id))

def c39920 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39920 : Upper (D 6) (R 6) [40,129,320,20,66] 13 := by
  apply FastRouting.sound _ _ [40,129,320,20,66] 13 (by decide) (choices 1) [1,2,4] r39920 c39920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26623
  · exact u26624
  · exact u26625

def b39921 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 324 28 84 35 99 163 291), lower := (rows 41 131 324 28 84 32 64 128 256), losses := [] }

theorem u39921 : Upper (D 6) (R 6) [40,129,320,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39922 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 41 131 324 28 112 39 71 135 263), lower := (rows 41 131 324 28 112 32 64 128 256), losses := [] }

theorem u39922 : Upper (D 6) (R 6) [40,129,320,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39923 : Route 9 := (fun mask => (mask,id))

def c39923 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39923 : Upper (D 6) (R 6) [40,129,320,65,6] 13 := by
  apply FastRouting.sound _ _ [40,129,320,65,6] 13 (by decide) (choices 1) [2,4,16] r39923 c39923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26626
  · exact u26627
  · exact u26628

def b39924 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 131 324 73 50 54 86 150 278), lower := (rows 41 131 324 73 50 32 64 128 256), losses := [] }

theorem u39924 : Upper (D 6) (R 6) [40,129,320,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39925 : Route 9 := (fun mask => (mask,id))

def c39925 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39925 : Upper (D 6) (R 6) [40,129,320,65,36] 13 := by
  apply FastRouting.sound _ _ [40,129,320,65,36] 13 (by decide) (choices 1) [2,4,16] r39925 c39925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26629
  · exact u26630
  · exact u26631

def b39926 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 324 74 19 52 116 180 308), lower := (rows 41 131 324 74 19 32 64 128 256), losses := [] }

theorem u39926 : Upper (D 6) (R 6) [40,129,320,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39927 : Route 9 := (fun mask => (mask,id))

def c39927 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39927 : Upper (D 6) (R 6) [40,129,320,66,5] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66,5] 13 (by decide) (choices 1) [2,4,16] r39927 c39927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26632
  · exact u26633
  · exact u26634

def r39928 : Route 9 := (fun mask => (mask,id))

def c39928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39928 : Upper (D 6) (R 6) [40,129,320,66,6] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66,6] 13 (by decide) (choices 1) [1,4,16] r39928 c39928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26635
  · exact u26636
  · exact u26637

def b39929 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 324 74 49 54 86 150 278), lower := (rows 41 131 324 74 49 32 64 128 256), losses := [] }

theorem u39929 : Upper (D 6) (R 6) [40,129,320,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39930 : Route 9 := (fun mask => (mask,id))

def c39930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39930 : Upper (D 6) (R 6) [40,129,320,66,34] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66,34] 13 (by decide) (choices 1) [1,4,16] r39930 c39930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26638
  · exact u26639
  · exact u26640

def r39931 : Route 9 := (fun mask => (mask,id))

def c39931 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39931 : Upper (D 6) (R 6) [40,129,320,66,36] 13 := by
  apply FastRouting.sound _ _ [40,129,320,66,36] 13 (by decide) (choices 1) [1,2,4,16] r39931 c39931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26641
  · exact u26642
  · exact u26643
  · exact u26644

def b39932 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 324 88 19 38 102 166 294), lower := (rows 41 131 324 88 19 32 64 128 256), losses := [] }

theorem u39932 : Upper (D 6) (R 6) [40,129,320,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39933 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 356, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 41 131 324 88 21 38 102 166 294), lower := (rows 41 131 324 88 21 32 64 128 256), losses := [{ target := 6, region := (rows 9 26 4 8 16 48 0 144 272), good := (rows 43 131 260 443 439 32 0 128 256) }] }

theorem u39933 : Upper (D 6) (R 6) [40,129,320,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39934 : Route 9 := (fun mask => (mask,id))

def c39934 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39934 : Upper (D 6) (R 6) [40,129,320,80,6] 13 := by
  apply FastRouting.sound _ _ [40,129,320,80,6] 13 (by decide) (choices 1) [1,2,4] r39934 c39934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26645
  · exact u26646
  · exact u26647

def b39935 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 324 88 49 38 70 134 262), lower := (rows 41 131 324 88 49 32 64 128 256), losses := [] }

theorem u39935 : Upper (D 6) (R 6) [40,129,320,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39936 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 131 324 88 50 39 71 135 263), lower := (rows 41 131 324 88 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 23 24 16 0 67 131 259), good := (rows 463 455 324 92 478 0 64 128 256) }] }

theorem u39936 : Upper (D 6) (R 6) [40,129,320,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39937 : Route 9 := (fun mask => (mask,id))

def c39937 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39937 : Upper (D 6) (R 6) [40,129,320,80,36] 13 := by
  apply FastRouting.sound _ _ [40,129,320,80,36] 13 (by decide) (choices 1) [1,2,4] r39937 c39937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26648
  · exact u26649
  · exact u26650

def r39938 : Route 9 := (fun mask => (mask,id))

def c39938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39938 : Upper (D 6) (R 6) [40,132,258,3,5] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,5] 13 (by decide) (choices 1) [16,64] r39938 c39938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26651
  · exact u26652

def b39939 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 262 11 49 116 84 212 340), lower := (rows 41 134 262 11 49 32 64 128 256), losses := [] }

theorem u39939 : Upper (D 6) (R 6) [40,132,258,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39940 : Route 9 := (fun mask => (mask,id))

def c39940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39940 : Upper (D 6) (R 6) [40,132,258,3,36] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,36] 13 (by decide) (choices 1) [1,16,64] r39940 c39940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26653
  · exact u26654
  · exact u26655

def r39941 : Route 9 := (fun mask => (mask,id))

def c39941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39941 : Upper (D 6) (R 6) [40,132,258,3,65] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,65] 13 (by decide) (choices 1) [4,16,64] r39941 c39941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26656
  · exact u26657
  · exact u26658

def r39942 : Route 9 := (fun mask => (mask,id))

def c39942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39942 : Upper (D 6) (R 6) [40,132,258,3,68] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,68] 13 (by decide) (choices 1) [1,16,64] r39942 c39942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26659
  · exact u26660
  · exact u26661

def r39943 : Route 9 := (fun mask => (mask,id))

def c39943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39943 : Upper (D 6) (R 6) [40,132,258,3,96] 13 := by
  apply FastRouting.sound _ _ [40,132,258,3,96] 13 (by decide) (choices 1) [1,4,16,64] r39943 c39943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26662
  · exact u26663
  · exact u26664
  · exact u26665

def b39944 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 134 262 25 19 100 100 228 356), lower := (rows 41 134 262 25 19 32 64 128 256), losses := [] }

theorem u39944 : Upper (D 6) (R 6) [40,132,258,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39945 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 25 22 97 97 225 353), lower := (rows 41 134 262 25 22 32 64 128 256), losses := [] }

theorem u39945 : Upper (D 6) (R 6) [40,132,258,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39946 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 25, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 25 49 102 70 198 326), lower := (rows 41 134 262 25 49 32 64 128 256), losses := [] }

theorem u39946 : Upper (D 6) (R 6) [40,132,258,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39947 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 25 50 101 69 197 325), lower := (rows 41 134 262 25 50 32 64 128 256), losses := [] }

theorem u39947 : Upper (D 6) (R 6) [40,132,258,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39948 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 134 262 25 81 102 102 230 358), lower := (rows 41 134 262 25 81 32 64 128 256), losses := [] }

theorem u39948 : Upper (D 6) (R 6) [40,132,258,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39949 : Route 9 := (fun mask => (mask,id))

def c39949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39949 : Upper (D 6) (R 6) [40,132,258,17,66] 13 := by
  apply FastRouting.sound _ _ [40,132,258,17,66] 13 (by decide) (choices 1) [1,4,64] r39949 c39949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26666
  · exact u26667
  · exact u26668

def b39950 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 262 25 112 103 71 199 327), lower := (rows 41 134 262 25 112 32 64 128 256), losses := [] }

theorem u39950 : Upper (D 6) (R 6) [40,132,258,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39951 : Route 9 := (fun mask => (mask,id))

def c39951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39951 : Upper (D 6) (R 6) [40,132,258,18,5] 13 := by
  apply FastRouting.sound _ _ [40,132,258,18,5] 13 (by decide) (choices 1) [1,64] r39951 c39951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26669
  · exact u26670

def b39952 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 262 26 49 101 69 197 325), lower := (rows 41 134 262 26 49 32 64 128 256), losses := [] }

theorem u39952 : Upper (D 6) (R 6) [40,132,258,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39953 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 41 134 262 26 52 97 65 193 321), lower := (rows 41 134 262 26 52 32 64 128 256), losses := [] }

theorem u39953 : Upper (D 6) (R 6) [40,132,258,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39954 : Route 9 := (fun mask => (mask,id))

def c39954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39954 : Upper (D 6) (R 6) [40,132,258,18,65] 13 := by
  apply FastRouting.sound _ _ [40,132,258,18,65] 13 (by decide) (choices 1) [1,4,64] r39954 c39954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26671
  · exact u26672
  · exact u26673

def r39955 : Route 9 := (fun mask => (mask,id))

def c39955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39955 : Upper (D 6) (R 6) [40,132,258,18,68] 13 := by
  apply FastRouting.sound _ _ [40,132,258,18,68] 13 (by decide) (choices 1) [1,64] r39955 c39955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26674
  · exact u26675

def r39956 : Route 9 := (fun mask => (mask,id))

def c39956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39956 : Upper (D 6) (R 6) [40,132,258,18,96] 13 := by
  apply FastRouting.sound _ _ [40,132,258,18,96] 13 (by decide) (choices 1) [1,4,64] r39956 c39956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26676
  · exact u26677
  · exact u26678

def r39957 : Route 9 := (fun mask => (mask,id))

def c39957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39957 : Upper (D 6) (R 6) [40,132,258,65,3] 13 := by
  apply FastRouting.sound _ _ [40,132,258,65,3] 13 (by decide) (choices 1) [4,16,64] r39957 c39957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26679
  · exact u26680
  · exact u26681

def b39958 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 73 22 113 113 241 369), lower := (rows 41 134 262 73 22 32 64 128 256), losses := [] }

theorem u39958 : Upper (D 6) (R 6) [40,132,258,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39959 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 262 73 49 118 86 214 342), lower := (rows 41 134 262 73 49 32 64 128 256), losses := [] }

theorem u39959 : Upper (D 6) (R 6) [40,132,258,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39959
end Delivery.IrregularNine14.P06
