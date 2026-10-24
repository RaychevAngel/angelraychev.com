import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0393
import IrregularNine14P06C0394

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37980 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 324 25 49 110 78 206 334), lower := (rows 35 134 324 25 49 32 64 128 256), losses := [] }

theorem u37980 : Upper (D 6) (R 6) [34,132,320,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37981 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 324 25 50 109 77 205 333), lower := (rows 35 134 324 25 50 32 64 128 256), losses := [] }

theorem u37981 : Upper (D 6) (R 6) [34,132,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37982 : Route 9 := (fun mask => (mask,id))

def c37982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37982 : Upper (D 6) (R 6) [34,132,320,17,36] 13 := by
  apply FastRouting.sound _ _ [34,132,320,17,36] 13 (by decide) (choices 1) [1,2,8,64] r37982 c37982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23590
  · exact u23591
  · exact u23592
  · exact u23593

def b37983 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 324 25 56 103 71 199 327), lower := (rows 35 134 324 25 56 32 64 128 256), losses := [] }

theorem u37983 : Upper (D 6) (R 6) [34,132,320,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37984 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 324 25 81 46 110 174 302), lower := (rows 35 134 324 25 81 32 64 128 256), losses := [] }

theorem u37984 : Upper (D 6) (R 6) [34,132,320,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37985 : Route 9 := (fun mask => (mask,id))

def c37985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37985 : Upper (D 6) (R 6) [34,132,320,17,66] 13 := by
  apply FastRouting.sound _ _ [34,132,320,17,66] 13 (by decide) (choices 1) [1,4,8] r37985 c37985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23594
  · exact u23595
  · exact u23596

def b37986 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 324 25 84 43 107 171 299), lower := (rows 35 134 324 25 84 32 64 128 256), losses := [] }

theorem u37986 : Upper (D 6) (R 6) [34,132,320,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37987 : Route 9 := (fun mask => (mask,id))

def c37987 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37987 : Upper (D 6) (R 6) [34,132,320,17,72] 13 := by
  apply FastRouting.sound _ _ [34,132,320,17,72] 13 (by decide) (choices 1) [1,2,4] r37987 c37987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23597
  · exact u23598
  · exact u23599

def r37988 : Route 9 := (fun mask => (mask,id))

def c37988 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37988 : Upper (D 6) (R 6) [34,132,320,17,96] 13 := by
  apply FastRouting.sound _ _ [34,132,320,17,96] 13 (by decide) (choices 1) [1,2,4,8] r37988 c37988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23600
  · exact u23601
  · exact u23602
  · exact u23603

def b37989 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 324 26 28 97 97 225 353), lower := (rows 35 134 324 26 28 32 64 128 256), losses := [] }

theorem u37989 : Upper (D 6) (R 6) [34,132,320,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37990 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 324 26 49 109 77 205 333), lower := (rows 35 134 324 26 49 32 64 128 256), losses := [] }

theorem u37990 : Upper (D 6) (R 6) [34,132,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37991 : Route 9 := (fun mask => (mask,id))

def c37991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37991 : Upper (D 6) (R 6) [34,132,320,18,36] 13 := by
  apply FastRouting.sound _ _ [34,132,320,18,36] 13 (by decide) (choices 1) [1,8,64] r37991 c37991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23604
  · exact u23605
  · exact u23606

def b37992 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 324 26 56 101 69 197 325), lower := (rows 35 134 324 26 56 32 64 128 256), losses := [] }

theorem u37992 : Upper (D 6) (R 6) [34,132,320,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37993 : Route 9 := (fun mask => (mask,id))

def c37993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37993 : Upper (D 6) (R 6) [34,132,320,18,65] 13 := by
  apply FastRouting.sound _ _ [34,132,320,18,65] 13 (by decide) (choices 1) [1,4,8] r37993 c37993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23607
  · exact u23608
  · exact u23609

def b37994 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 324 26 84 41 105 169 297), lower := (rows 35 134 324 26 84 32 64 128 256), losses := [] }

theorem u37994 : Upper (D 6) (R 6) [34,132,320,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37995 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 134 324 26 88 37 101 165 293), lower := (rows 35 134 324 26 88 32 64 128 256), losses := [] }

theorem u37995 : Upper (D 6) (R 6) [34,132,320,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37996 : Route 9 := (fun mask => (mask,id))

def c37996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37996 : Upper (D 6) (R 6) [34,132,320,18,96] 13 := by
  apply FastRouting.sound _ _ [34,132,320,18,96] 13 (by decide) (choices 1) [1,4,8] r37996 c37996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23610
  · exact u23611
  · exact u23612

def b37997 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 324 28 49 107 75 203 331), lower := (rows 35 134 324 28 49 32 64 128 256), losses := [] }

theorem u37997 : Upper (D 6) (R 6) [34,132,320,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37998 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 324 28 50 105 73 201 329), lower := (rows 35 134 324 28 50 32 64 128 256), losses := [] }

theorem u37998 : Upper (D 6) (R 6) [34,132,320,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37999 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 134 324 28 56 99 67 195 323), lower := (rows 35 134 324 28 56 32 64 128 256), losses := [] }

theorem u37999 : Upper (D 6) (R 6) [34,132,320,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38000 : Route 9 := (fun mask => (mask,id))

def c38000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38000 : Upper (D 6) (R 6) [34,132,320,20,65] 13 := by
  apply FastRouting.sound _ _ [34,132,320,20,65] 13 (by decide) (choices 1) [1,2,8] r38000 c38000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23613
  · exact u23614
  · exact u23615

def r38001 : Route 9 := (fun mask => (mask,id))

def c38001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38001 : Upper (D 6) (R 6) [34,132,320,20,66] 13 := by
  apply FastRouting.sound _ _ [34,132,320,20,66] 13 (by decide) (choices 1) [1,8] r38001 c38001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23616
  · exact u23617

def b38002 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 134 324 28 88 35 99 163 291), lower := (rows 35 134 324 28 88 32 64 128 256), losses := [] }

theorem u38002 : Upper (D 6) (R 6) [34,132,320,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38003 : Route 9 := (fun mask => (mask,id))

def c38003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38003 : Upper (D 6) (R 6) [34,132,320,20,96] 13 := by
  apply FastRouting.sound _ _ [34,132,320,20,96] 13 (by decide) (choices 1) [1,2,8] r38003 c38003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23618
  · exact u23619
  · exact u23620

def b38004 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 324 41 81 62 94 158 286), lower := (rows 35 134 324 41 81 32 64 128 256), losses := [] }

theorem u38004 : Upper (D 6) (R 6) [34,132,320,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38005 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 324 41 82 61 93 157 285), lower := (rows 35 134 324 41 82 32 64 128 256), losses := [] }

theorem u38005 : Upper (D 6) (R 6) [34,132,320,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38006 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 324 41 88 55 87 151 279), lower := (rows 35 134 324 41 88 32 64 128 256), losses := [] }

theorem u38006 : Upper (D 6) (R 6) [34,132,320,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38007 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 134 324 42 81 61 93 157 285), lower := (rows 35 134 324 42 81 32 64 128 256), losses := [] }

theorem u38007 : Upper (D 6) (R 6) [34,132,320,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38008 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 134 324 42 88 53 85 149 277), lower := (rows 35 134 324 42 88 32 64 128 256), losses := [] }

theorem u38008 : Upper (D 6) (R 6) [34,132,320,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38009 : Route 9 := (fun mask => (mask,id))

def c38009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38009 : Upper (D 6) (R 6) [34,132,320,36,65] 13 := by
  apply FastRouting.sound _ _ [34,132,320,36,65] 13 (by decide) (choices 1) [1,2,8,16] r38009 c38009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23621
  · exact u23622
  · exact u23623
  · exact u23624

def r38010 : Route 9 := (fun mask => (mask,id))

def c38010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38010 : Upper (D 6) (R 6) [34,132,320,36,66] 13 := by
  apply FastRouting.sound _ _ [34,132,320,36,66] 13 (by decide) (choices 1) [1,8,16] r38010 c38010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23625
  · exact u23626
  · exact u23627

def r38011 : Route 9 := (fun mask => (mask,id))

def c38011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38011 : Upper (D 6) (R 6) [34,132,320,36,72] 13 := by
  apply FastRouting.sound _ _ [34,132,320,36,72] 13 (by decide) (choices 1) [1,2,16] r38011 c38011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23628
  · exact u23629
  · exact u23630

def r38012 : Route 9 := (fun mask => (mask,id))

def c38012 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38012 : Upper (D 6) (R 6) [34,132,320,48,65] 13 := by
  apply FastRouting.sound _ _ [34,132,320,48,65] 13 (by decide) (choices 1) [1,2,4,8] r38012 c38012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23631
  · exact u23632
  · exact u23633
  · exact u23634

def r38013 : Route 9 := (fun mask => (mask,id))

def c38013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38013 : Upper (D 6) (R 6) [34,132,320,48,66] 13 := by
  apply FastRouting.sound _ _ [34,132,320,48,66] 13 (by decide) (choices 1) [1,4,8] r38013 c38013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23635
  · exact u23636
  · exact u23637

def b38014 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 324 56 84 43 75 139 267), lower := (rows 35 134 324 56 84 32 64 128 256), losses := [] }

theorem u38014 : Upper (D 6) (R 6) [34,132,320,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38015 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 134 324 56 88 39 71 135 263), lower := (rows 35 134 324 56 88 32 64 128 256), losses := [] }

theorem u38015 : Upper (D 6) (R 6) [34,132,320,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38016 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 138 52 13 19 356 324 452 324), lower := (rows 35 138 52 13 19 32 64 128 256), losses := [] }

theorem u38016 : Upper (D 6) (R 6) [34,136,48,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38017 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 138 52 13 21 354 322 450 322), lower := (rows 35 138 52 13 21 32 64 128 256), losses := [] }

theorem u38017 : Upper (D 6) (R 6) [34,136,48,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38018 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 138 52 13 22 353 321 449 321), lower := (rows 35 138 52 13 22 32 64 128 256), losses := [] }

theorem u38018 : Upper (D 6) (R 6) [34,136,48,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38019 : PairBound 9 := { available := 326, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 138 52 13 81 358 326 454 326), lower := (rows 35 138 52 13 81 32 64 128 256), losses := [] }

theorem u38019 : Upper (D 6) (R 6) [34,136,48,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38020 : Route 9 := (fun mask => (mask,id))

def c38020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u38020 : Upper (D 6) (R 6) [34,136,48,5,66] 13 := by
  apply FastRouting.sound _ _ [34,136,48,5,66] 13 (by decide) (choices 1) [1,4,64,256] r38020 c38020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23638
  · exact u23639
  · exact u23640
  · exact u23641

def b38021 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 483, targets := 4 },{ cop := 3, region := 450, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 138 52 13 84 355 323 451 323), lower := (rows 35 138 52 13 84 32 64 128 256), losses := [] }

theorem u38021 : Upper (D 6) (R 6) [34,136,48,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38022 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 138 52 13 273 102 70 198 326), lower := (rows 35 138 52 13 273 32 64 128 256), losses := [] }

theorem u38022 : Upper (D 6) (R 6) [34,136,48,5,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38023 : Route 9 := (fun mask => (mask,id))

def c38023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38023 : Upper (D 6) (R 6) [34,136,48,5,258] 13 := by
  apply FastRouting.sound _ _ [34,136,48,5,258] 13 (by decide) (choices 1) [1,4,64] r38023 c38023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23642
  · exact u23643
  · exact u23644

def b38024 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 3, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 138 52 13 276 99 67 195 323), lower := (rows 35 138 52 13 276 32 64 128 256), losses := [] }

theorem u38024 : Upper (D 6) (R 6) [34,136,48,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38025 : Route 9 := (fun mask => (mask,id))

def c38025 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38025 : Upper (D 6) (R 6) [34,136,48,5,320] 13 := by
  apply FastRouting.sound _ _ [34,136,48,5,320] 13 (by decide) (choices 1) [1,2,4,64] r38025 c38025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23645
  · exact u23646
  · exact u23647
  · exact u23648

def b38026 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 138 52 14 21 353 321 449 321), lower := (rows 35 138 52 14 21 32 64 128 256), losses := [] }

theorem u38026 : Upper (D 6) (R 6) [34,136,48,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38027 : Route 9 := (fun mask => (mask,id))

def c38027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u38027 : Upper (D 6) (R 6) [34,136,48,6,65] 13 := by
  apply FastRouting.sound _ _ [34,136,48,6,65] 13 (by decide) (choices 1) [1,4,64,256] r38027 c38027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23649
  · exact u23650
  · exact u23651
  · exact u23652

def b38028 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 353, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 52 14 84 353 321 449 321), lower := (rows 35 138 52 14 84 32 64 128 256), losses := [] }

theorem u38028 : Upper (D 6) (R 6) [34,136,48,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38029 : Route 9 := (fun mask => (mask,id))

def c38029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38029 : Upper (D 6) (R 6) [34,136,48,6,257] 13 := by
  apply FastRouting.sound _ _ [34,136,48,6,257] 13 (by decide) (choices 1) [1,4,64] r38029 c38029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23653
  · exact u23654
  · exact u23655

def b38030 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 52 14 276 97 65 193 321), lower := (rows 35 138 52 14 276 32 64 128 256), losses := [] }

theorem u38030 : Upper (D 6) (R 6) [34,136,48,6,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38031 : Route 9 := (fun mask => (mask,id))

def c38031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38031 : Upper (D 6) (R 6) [34,136,48,6,320] 13 := by
  apply FastRouting.sound _ _ [34,136,48,6,320] 13 (by decide) (choices 1) [1,4,64] r38031 c38031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23656
  · exact u23657
  · exact u23658

def b38032 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 35 138 52 73 19 356 324 452 324), lower := (rows 35 138 52 73 19 32 64 128 256), losses := [] }

theorem u38032 : Upper (D 6) (R 6) [34,136,48,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38033 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 73 21 358 326 454 326), lower := (rows 35 138 52 73 21 32 64 128 256), losses := [] }

theorem u38033 : Upper (D 6) (R 6) [34,136,48,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38034 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 20, targets := 1 },{ cop := 0, region := 20, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 35 138 52 73 22 357 325 453 325), lower := (rows 35 138 52 73 22 32 64 128 256), losses := [] }

theorem u38034 : Upper (D 6) (R 6) [34,136,48,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38035 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 138 52 73 81 294 326 390 262), lower := (rows 35 138 52 73 81 32 64 128 256), losses := [] }

theorem u38035 : Upper (D 6) (R 6) [34,136,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38036 : Route 9 := (fun mask => (mask,id))

def c38036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38036 : Upper (D 6) (R 6) [34,136,48,65,66] 13 := by
  apply FastRouting.sound _ _ [34,136,48,65,66] 13 (by decide) (choices 1) [1,4,256] r38036 c38036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23659
  · exact u23660
  · exact u23661

def r38037 : Route 9 := (fun mask => (mask,id))

def c38037 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38037 : Upper (D 6) (R 6) [34,136,48,65,68] 13 := by
  apply FastRouting.sound _ _ [34,136,48,65,68] 13 (by decide) (choices 1) [1,2,4,256] r38037 c38037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23662
  · exact u23663
  · exact u23664
  · exact u23665

def r38038 : Route 9 := (fun mask => (mask,id))

def c38038 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38038 : Upper (D 6) (R 6) [34,136,48,65,257] 13 := by
  apply FastRouting.sound _ _ [34,136,48,65,257] 13 (by decide) (choices 1) [2,4,64] r38038 c38038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23666
  · exact u23667
  · exact u23668

def r38039 : Route 9 := (fun mask => (mask,id))

def c38039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38039 : Upper (D 6) (R 6) [34,136,48,65,258] 13 := by
  apply FastRouting.sound _ _ [34,136,48,65,258] 13 (by decide) (choices 1) [1,4,64] r38039 c38039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23669
  · exact u23670
  · exact u23671

#print axioms u38039
end Delivery.IrregularNine14.P06
