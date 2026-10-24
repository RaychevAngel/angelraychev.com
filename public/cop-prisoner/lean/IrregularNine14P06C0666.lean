import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0444
import IrregularNine14P06C0445
import IrregularNine14P06C0446

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39960 : Route 9 := (fun mask => (mask,id))

def c39960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39960 : Upper (D 6) (R 6) [40,132,258,65,34] 13 := by
  apply FastRouting.sound _ _ [40,132,258,65,34] 13 (by decide) (choices 1) [1,4,16,64] r39960 c39960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26682
  · exact u26683
  · exact u26684
  · exact u26685

def b39961 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 134 262 73 81 54 118 182 310), lower := (rows 41 134 262 73 81 32 64 128 256), losses := [] }

theorem u39961 : Upper (D 6) (R 6) [40,132,258,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39962 : Route 9 := (fun mask => (mask,id))

def c39962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39962 : Upper (D 6) (R 6) [40,132,258,65,66] 13 := by
  apply FastRouting.sound _ _ [40,132,258,65,66] 13 (by decide) (choices 1) [1,4,16] r39962 c39962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26686
  · exact u26687
  · exact u26688

def b39963 : PairBound 9 := { available := 23, camps := [{ cop := 4, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 73 112 55 87 151 279), lower := (rows 41 134 262 73 112 32 64 128 256), losses := [] }

theorem u39963 : Upper (D 6) (R 6) [40,132,258,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39964 : Route 9 := (fun mask => (mask,id))

def c39964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39964 : Upper (D 6) (R 6) [40,132,258,66,5] 13 := by
  apply FastRouting.sound _ _ [40,132,258,66,5] 13 (by decide) (choices 1) [1,16,64] r39964 c39964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26689
  · exact u26690
  · exact u26691

def b39965 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 262 74 49 117 85 213 341), lower := (rows 41 134 262 74 49 32 64 128 256), losses := [] }

theorem u39965 : Upper (D 6) (R 6) [40,132,258,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39966 : Route 9 := (fun mask => (mask,id))

def c39966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39966 : Upper (D 6) (R 6) [40,132,258,66,36] 13 := by
  apply FastRouting.sound _ _ [40,132,258,66,36] 13 (by decide) (choices 1) [1,16,64] r39966 c39966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26692
  · exact u26693
  · exact u26694

def r39967 : Route 9 := (fun mask => (mask,id))

def c39967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39967 : Upper (D 6) (R 6) [40,132,258,66,65] 13 := by
  apply FastRouting.sound _ _ [40,132,258,66,65] 13 (by decide) (choices 1) [1,4,16] r39967 c39967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26695
  · exact u26696
  · exact u26697

def r39968 : Route 9 := (fun mask => (mask,id))

def c39968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39968 : Upper (D 6) (R 6) [40,132,258,66,68] 13 := by
  apply FastRouting.sound _ _ [40,132,258,66,68] 13 (by decide) (choices 1) [1,16] r39968 c39968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26698
  · exact u26699

def r39969 : Route 9 := (fun mask => (mask,id))

def c39969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39969 : Upper (D 6) (R 6) [40,132,258,66,96] 13 := by
  apply FastRouting.sound _ _ [40,132,258,66,96] 13 (by decide) (choices 1) [1,4,16] r39969 c39969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26700
  · exact u26701
  · exact u26702

def r39970 : Route 9 := (fun mask => (mask,id))

def c39970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39970 : Upper (D 6) (R 6) [40,132,258,80,3] 13 := by
  apply FastRouting.sound _ _ [40,132,258,80,3] 13 (by decide) (choices 1) [1,4,64] r39970 c39970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26703
  · exact u26704
  · exact u26705

def b39971 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 88 22 97 97 225 353), lower := (rows 41 134 262 88 22 32 64 128 256), losses := [] }

theorem u39971 : Upper (D 6) (R 6) [40,132,258,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39972 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 262 88 49 103 71 199 327), lower := (rows 41 134 262 88 49 32 64 128 256), losses := [] }

theorem u39972 : Upper (D 6) (R 6) [40,132,258,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39973 : Route 9 := (fun mask => (mask,id))

def c39973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39973 : Upper (D 6) (R 6) [40,132,258,80,34] 13 := by
  apply FastRouting.sound _ _ [40,132,258,80,34] 13 (by decide) (choices 1) [1,4,64] r39973 c39973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26706
  · exact u26707
  · exact u26708

def b39974 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 134 262 88 81 39 103 167 295), lower := (rows 41 134 262 88 81 32 64 128 256), losses := [] }

theorem u39974 : Upper (D 6) (R 6) [40,132,258,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39975 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 134 262 88 82 37 101 165 293), lower := (rows 41 134 262 88 82 32 64 128 256), losses := [] }

theorem u39975 : Upper (D 6) (R 6) [40,132,258,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39976 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 88 112 39 71 135 263), lower := (rows 41 134 262 88 112 32 64 128 256), losses := [] }

theorem u39976 : Upper (D 6) (R 6) [40,132,258,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39977 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 134 276 11 19 100 100 228 356), lower := (rows 41 134 276 11 19 32 64 128 256), losses := [] }

theorem u39977 : Upper (D 6) (R 6) [40,132,272,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39978 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 134 276 11 21 98 98 226 354), lower := (rows 41 134 276 11 21 32 64 128 256), losses := [] }

theorem u39978 : Upper (D 6) (R 6) [40,132,272,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39979 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 276 11 22 97 97 225 353), lower := (rows 41 134 276 11 22 32 64 128 256), losses := [] }

theorem u39979 : Upper (D 6) (R 6) [40,132,272,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39980 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 276 11 49 102 70 198 326), lower := (rows 41 134 276 11 49 32 64 128 256), losses := [] }

theorem u39980 : Upper (D 6) (R 6) [40,132,272,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39981 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 276 11 50 101 69 197 325), lower := (rows 41 134 276 11 50 32 64 128 256), losses := [] }

theorem u39981 : Upper (D 6) (R 6) [40,132,272,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39982 : Route 9 := (fun mask => (mask,id))

def c39982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39982 : Upper (D 6) (R 6) [40,132,272,3,36] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3,36] 13 (by decide) (choices 1) [1,2,64] r39982 c39982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26709
  · exact u26710
  · exact u26711

def r39983 : Route 9 := (fun mask => (mask,id))

def c39983 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39983 : Upper (D 6) (R 6) [40,132,272,3,65] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3,65] 13 (by decide) (choices 1) [2,4,64] r39983 c39983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26712
  · exact u26713
  · exact u26714

def r39984 : Route 9 := (fun mask => (mask,id))

def c39984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39984 : Upper (D 6) (R 6) [40,132,272,3,66] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3,66] 13 (by decide) (choices 1) [1,4,64] r39984 c39984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26715
  · exact u26716
  · exact u26717

def r39985 : Route 9 := (fun mask => (mask,id))

def c39985 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39985 : Upper (D 6) (R 6) [40,132,272,3,68] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3,68] 13 (by decide) (choices 1) [1,2,64] r39985 c39985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26718
  · exact u26719
  · exact u26720

def r39986 : Route 9 := (fun mask => (mask,id))

def c39986 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39986 : Upper (D 6) (R 6) [40,132,272,3,96] 13 := by
  apply FastRouting.sound _ _ [40,132,272,3,96] 13 (by decide) (choices 1) [1,2,4,64] r39986 c39986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26721
  · exact u26722
  · exact u26723
  · exact u26724

def r39987 : Route 9 := (fun mask => (mask,id))

def c39987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39987 : Upper (D 6) (R 6) [40,132,272,5,3] 13 := by
  apply FastRouting.sound _ _ [40,132,272,5,3] 13 (by decide) (choices 1) [2,64] r39987 c39987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26725
  · exact u26726

def b39988 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 276 13 49 98 66 194 322), lower := (rows 41 134 276 13 49 32 64 128 256), losses := [] }

theorem u39988 : Upper (D 6) (R 6) [40,132,272,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39989 : Route 9 := (fun mask => (mask,id))

def c39989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39989 : Upper (D 6) (R 6) [40,132,272,5,34] 13 := by
  apply FastRouting.sound _ _ [40,132,272,5,34] 13 (by decide) (choices 1) [1,2,64] r39989 c39989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26727
  · exact u26728
  · exact u26729

def r39990 : Route 9 := (fun mask => (mask,id))

def c39990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39990 : Upper (D 6) (R 6) [40,132,272,5,65] 13 := by
  apply FastRouting.sound _ _ [40,132,272,5,65] 13 (by decide) (choices 1) [2,64] r39990 c39990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26730
  · exact u26731

def r39991 : Route 9 := (fun mask => (mask,id))

def c39991 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39991 : Upper (D 6) (R 6) [40,132,272,5,66] 13 := by
  apply FastRouting.sound _ _ [40,132,272,5,66] 13 (by decide) (choices 1) [1,2,64] r39991 c39991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26732
  · exact u26733
  · exact u26734

def r39992 : Route 9 := (fun mask => (mask,id))

def c39992 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39992 : Upper (D 6) (R 6) [40,132,272,5,96] 13 := by
  apply FastRouting.sound _ _ [40,132,272,5,96] 13 (by decide) (choices 1) [1,2,64] r39992 c39992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26735
  · exact u26736
  · exact u26737

def r39993 : Route 9 := (fun mask => (mask,id))

def c39993 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39993 : Upper (D 6) (R 6) [40,132,272,65,3] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,3] 13 (by decide) (choices 1) [2,4,64] r39993 c39993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26738
  · exact u26739
  · exact u26740

def b39994 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 134 276 73 21 98 98 226 354), lower := (rows 41 134 276 73 21 32 64 128 256), losses := [] }

theorem u39994 : Upper (D 6) (R 6) [40,132,272,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39995 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 276 73 22 99 99 227 355), lower := (rows 41 134 276 73 22 32 64 128 256), losses := [] }

theorem u39995 : Upper (D 6) (R 6) [40,132,272,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39996 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 276 73 49 102 70 198 326), lower := (rows 41 134 276 73 49 32 64 128 256), losses := [] }

theorem u39996 : Upper (D 6) (R 6) [40,132,272,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39997 : Route 9 := (fun mask => (mask,id))

def c39997 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39997 : Upper (D 6) (R 6) [40,132,272,65,34] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,34] 13 (by decide) (choices 1) [1,2,4,64] r39997 c39997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26741
  · exact u26742
  · exact u26743
  · exact u26744

def r39998 : Route 9 := (fun mask => (mask,id))

def c39998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39998 : Upper (D 6) (R 6) [40,132,272,65,36] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,36] 13 (by decide) (choices 1) [1,2,64] r39998 c39998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26745
  · exact u26746
  · exact u26747

def b39999 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 134 276 73 81 38 102 166 294), lower := (rows 41 134 276 73 81 32 64 128 256), losses := [] }

theorem u39999 : Upper (D 6) (R 6) [40,132,272,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40000 : Route 9 := (fun mask => (mask,id))

def c40000 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40000 : Upper (D 6) (R 6) [40,132,272,65,66] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,66] 13 (by decide) (choices 1) [1,2,4] r40000 c40000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26748
  · exact u26749
  · exact u26750

def r40001 : Route 9 := (fun mask => (mask,id))

def c40001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40001 : Upper (D 6) (R 6) [40,132,272,65,68] 13 := by
  apply FastRouting.sound _ _ [40,132,272,65,68] 13 (by decide) (choices 1) [1,2] r40001 c40001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26751
  · exact u26752

def b40002 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 112 39 71 135 263), lower := (rows 41 134 276 73 112 32 64 128 256), losses := [] }

theorem u40002 : Upper (D 6) (R 6) [40,132,272,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40003 : Route 9 := (fun mask => (mask,id))

def c40003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40003 : Upper (D 6) (R 6) [40,132,272,66,3] 13 := by
  apply FastRouting.sound _ _ [40,132,272,66,3] 13 (by decide) (choices 1) [1,4,64] r40003 c40003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26753
  · exact u26754
  · exact u26755

def r40004 : Route 9 := (fun mask => (mask,id))

def c40004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40004 : Upper (D 6) (R 6) [40,132,272,66,5] 13 := by
  apply FastRouting.sound _ _ [40,132,272,66,5] 13 (by decide) (choices 1) [1,2,64] r40004 c40004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26756
  · exact u26757
  · exact u26758

def b40005 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 276 74 22 97 97 225 353), lower := (rows 41 134 276 74 22 32 64 128 256), losses := [] }

theorem u40005 : Upper (D 6) (R 6) [40,132,272,66,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40006 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 276 74 49 103 71 199 327), lower := (rows 41 134 276 74 49 32 64 128 256), losses := [] }

theorem u40006 : Upper (D 6) (R 6) [40,132,272,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40007 : Route 9 := (fun mask => (mask,id))

def c40007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40007 : Upper (D 6) (R 6) [40,132,272,66,34] 13 := by
  apply FastRouting.sound _ _ [40,132,272,66,34] 13 (by decide) (choices 1) [1,4,64] r40007 c40007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26759
  · exact u26760
  · exact u26761

def r40008 : Route 9 := (fun mask => (mask,id))

def c40008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40008 : Upper (D 6) (R 6) [40,132,272,66,36] 13 := by
  apply FastRouting.sound _ _ [40,132,272,66,36] 13 (by decide) (choices 1) [1,2,64] r40008 c40008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26762
  · exact u26763
  · exact u26764

def r40009 : Route 9 := (fun mask => (mask,id))

def c40009 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40009 : Upper (D 6) (R 6) [40,132,272,66,65] 13 := by
  apply FastRouting.sound _ _ [40,132,272,66,65] 13 (by decide) (choices 1) [1,2,4] r40009 c40009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26765
  · exact u26766
  · exact u26767

def b40010 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 134 276 74 82 37 101 165 293), lower := (rows 41 134 276 74 82 32 64 128 256), losses := [] }

theorem u40010 : Upper (D 6) (R 6) [40,132,272,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40011 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 276 74 84 35 99 163 291), lower := (rows 41 134 276 74 84 32 64 128 256), losses := [] }

theorem u40011 : Upper (D 6) (R 6) [40,132,272,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40012 : Route 9 := (fun mask => (mask,id))

def c40012 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40012 : Upper (D 6) (R 6) [40,132,272,66,96] 13 := by
  apply FastRouting.sound _ _ [40,132,272,66,96] 13 (by decide) (choices 1) [1,2,4] r40012 c40012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26768
  · exact u26769
  · exact u26770

def r40013 : Route 9 := (fun mask => (mask,id))

def c40013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40013 : Upper (D 6) (R 6) [40,132,272,68,3] 13 := by
  apply FastRouting.sound _ _ [40,132,272,68,3] 13 (by decide) (choices 1) [1,2,64] r40013 c40013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26771
  · exact u26772
  · exact u26773

def b40014 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 276 76 49 99 67 195 323), lower := (rows 41 134 276 76 49 32 64 128 256), losses := [] }

theorem u40014 : Upper (D 6) (R 6) [40,132,272,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40015 : Route 9 := (fun mask => (mask,id))

def c40015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40015 : Upper (D 6) (R 6) [40,132,272,68,34] 13 := by
  apply FastRouting.sound _ _ [40,132,272,68,34] 13 (by decide) (choices 1) [1,2,64] r40015 c40015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26774
  · exact u26775
  · exact u26776

def b40016 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 134 276 76 81 35 99 163 291), lower := (rows 41 134 276 76 81 32 64 128 256), losses := [] }

theorem u40016 : Upper (D 6) (R 6) [40,132,272,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40017 : Route 9 := (fun mask => (mask,id))

def c40017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40017 : Upper (D 6) (R 6) [40,132,272,68,66] 13 := by
  apply FastRouting.sound _ _ [40,132,272,68,66] 13 (by decide) (choices 1) [1,2] r40017 c40017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26777
  · exact u26778

def r40018 : Route 9 := (fun mask => (mask,id))

def c40018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40018 : Upper (D 6) (R 6) [40,132,272,68,96] 13 := by
  apply FastRouting.sound _ _ [40,132,272,68,96] 13 (by decide) (choices 1) [1,2] r40018 c40018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26779
  · exact u26780

def b40019 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 134 292 11 19 116 84 212 340), lower := (rows 41 134 292 11 19 32 64 128 256), losses := [] }

theorem u40019 : Upper (D 6) (R 6) [40,132,288,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40019
end Delivery.IrregularNine14.P06
