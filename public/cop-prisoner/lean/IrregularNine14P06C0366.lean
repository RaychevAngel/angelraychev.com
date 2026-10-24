import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0108

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r21960 : Route 9 := (fun mask => (mask,id))

def c21960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21960 : Upper (D 6) (R 6) [34,129,66,96,260,16] 13 := by
  apply FastRouting.sound _ _ [34,129,66,96,260,16] 13 (by decide) (choices 1) [1,4,8] r21960 c21960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6485
  · exact u6486
  · exact u6487

def b21961 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 70 104 280 33 84 148 276), lower := (rows 35 131 70 104 280 33 64 128 256), losses := [] }

theorem u21961 : Upper (D 6) (R 6) [34,129,66,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21962 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 40, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 35 131 70 104 280 36 85 149 277), lower := (rows 35 131 70 104 280 36 64 128 256), losses := [] }

theorem u21962 : Upper (D 6) (R 6) [34,129,66,96,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21963 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 70 104 280 48 69 133 261), lower := (rows 35 131 70 104 280 48 64 128 256), losses := [] }

theorem u21963 : Upper (D 6) (R 6) [34,129,66,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21963 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21964 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 13 22 48 352 480 352), lower := (rows 35 131 76 13 22 48 64 128 256), losses := [] }

theorem u21964 : Upper (D 6) (R 6) [34,129,72,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21964 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21965 : Route 9 := (fun mask => (mask,id))

def c21965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u21965 : Upper (D 6) (R 6) [34,129,72,5,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,6,64] 13 (by decide) (choices 1) [16,32,256] r21965 c21965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6488
  · exact u6489
  · exact u6490

def b21966 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 483, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 13 22 288 112 240 368), lower := (rows 35 131 76 13 22 288 64 128 256), losses := [] }

theorem u21966 : Upper (D 6) (R 6) [34,129,72,5,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21966 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21967 : PairBound 9 := { available := 336, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 13 52 34 336 464 336), lower := (rows 35 131 76 13 52 34 64 128 256), losses := [] }

theorem u21967 : Upper (D 6) (R 6) [34,129,72,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21968 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 13 52 48 322 450 322), lower := (rows 35 131 76 13 52 48 64 128 256), losses := [] }

theorem u21968 : Upper (D 6) (R 6) [34,129,72,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21968 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21969 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 76 13 52 96 338 402 274), lower := (rows 35 131 76 13 52 96 64 128 256), losses := [] }

theorem u21969 : Upper (D 6) (R 6) [34,129,72,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21970 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 195, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 13 52 288 82 210 338), lower := (rows 35 131 76 13 52 288 64 128 256), losses := [] }

theorem u21970 : Upper (D 6) (R 6) [34,129,72,5,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21970 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21971 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 13 82 36 368 432 304), lower := (rows 35 131 76 13 82 36 64 128 256), losses := [] }

theorem u21971 : Upper (D 6) (R 6) [34,129,72,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21972 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 13 82 48 356 420 292), lower := (rows 35 131 76 13 82 48 64 128 256), losses := [] }

theorem u21972 : Upper (D 6) (R 6) [34,129,72,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21972 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21973 : Route 9 := (fun mask => (mask,id))

def c21973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21973 : Upper (D 6) (R 6) [34,129,72,5,66,256] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,66,256] 13 (by decide) (choices 1) [4,16,32] r21973 c21973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6491
  · exact u6492
  · exact u6493

def b21974 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 13 112 34 340 404 276), lower := (rows 35 131 76 13 112 34 64 128 256), losses := [] }

theorem u21974 : Upper (D 6) (R 6) [34,129,72,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21975 : PairBound 9 := { available := 274, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 13 112 36 338 402 274), lower := (rows 35 131 76 13 112 36 64 128 256), losses := [] }

theorem u21975 : Upper (D 6) (R 6) [34,129,72,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21976 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 13 112 48 326 390 262), lower := (rows 35 131 76 13 112 48 64 128 256), losses := [] }

theorem u21976 : Upper (D 6) (R 6) [34,129,72,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21976 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21977 : Route 9 := (fun mask => (mask,id))

def c21977 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21977 : Upper (D 6) (R 6) [34,129,72,5,96,256] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,96,256] 13 (by decide) (choices 1) [2,4,16] r21977 c21977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6494
  · exact u6495
  · exact u6496

def b21978 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 13 274 36 112 240 368), lower := (rows 35 131 76 13 274 36 64 128 256), losses := [] }

theorem u21978 : Upper (D 6) (R 6) [34,129,72,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21979 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 76 13 274 48 100 228 356), lower := (rows 35 131 76 13 274 48 64 128 256), losses := [] }

theorem u21979 : Upper (D 6) (R 6) [34,129,72,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21979 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21980 : Route 9 := (fun mask => (mask,id))

def c21980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21980 : Upper (D 6) (R 6) [34,129,72,5,258,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,258,64] 13 (by decide) (choices 1) [4,16,32] r21980 c21980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6497
  · exact u6498
  · exact u6499

def b21981 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 13 276 34 112 240 368), lower := (rows 35 131 76 13 276 34 64 128 256), losses := [] }

theorem u21981 : Upper (D 6) (R 6) [34,129,72,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21982 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 13 276 48 98 226 354), lower := (rows 35 131 76 13 276 48 64 128 256), losses := [] }

theorem u21982 : Upper (D 6) (R 6) [34,129,72,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21982 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21983 : Route 9 := (fun mask => (mask,id))

def c21983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21983 : Upper (D 6) (R 6) [34,129,72,5,260,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,260,64] 13 (by decide) (choices 1) [2,16,32] r21983 c21983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6500
  · exact u6501
  · exact u6502

def b21984 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 13 304 34 84 212 340), lower := (rows 35 131 76 13 304 34 64 128 256), losses := [] }

theorem u21984 : Upper (D 6) (R 6) [34,129,72,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21985 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 13 304 36 82 210 338), lower := (rows 35 131 76 13 304 36 64 128 256), losses := [] }

theorem u21985 : Upper (D 6) (R 6) [34,129,72,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21986 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 76 13 304 48 70 198 326), lower := (rows 35 131 76 13 304 48 64 128 256), losses := [] }

theorem u21986 : Upper (D 6) (R 6) [34,129,72,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21986 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21987 : Route 9 := (fun mask => (mask,id))

def c21987 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21987 : Upper (D 6) (R 6) [34,129,72,5,288,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,288,64] 13 (by decide) (choices 1) [2,4,16] r21987 c21987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6503
  · exact u6504
  · exact u6505

def b21988 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 13 336 34 116 180 308), lower := (rows 35 131 76 13 336 34 64 128 256), losses := [] }

theorem u21988 : Upper (D 6) (R 6) [34,129,72,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21989 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 13 336 36 114 178 306), lower := (rows 35 131 76 13 336 36 64 128 256), losses := [] }

theorem u21989 : Upper (D 6) (R 6) [34,129,72,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21990 : Route 9 := (fun mask => (mask,id))

def c21990 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21990 : Upper (D 6) (R 6) [34,129,72,5,320,16] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,320,16] 13 (by decide) (choices 1) [2,4,32] r21990 c21990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6506
  · exact u6507
  · exact u6508

def b21991 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 14 21 48 352 480 352), lower := (rows 35 131 76 14 21 48 64 128 256), losses := [] }

theorem u21991 : Upper (D 6) (R 6) [34,129,72,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21991 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21992 : Route 9 := (fun mask => (mask,id))

def c21992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u21992 : Upper (D 6) (R 6) [34,129,72,6,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,5,64] 13 (by decide) (choices 1) [16,32,256] r21992 c21992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6509
  · exact u6510
  · exact u6511

def b21993 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 483, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 14 21 288 112 240 368), lower := (rows 35 131 76 14 21 288 64 128 256), losses := [] }

theorem u21993 : Upper (D 6) (R 6) [34,129,72,6,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21993 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21994 : PairBound 9 := { available := 336, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 14 52 33 336 464 336), lower := (rows 35 131 76 14 52 33 64 128 256), losses := [] }

theorem u21994 : Upper (D 6) (R 6) [34,129,72,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21995 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 14 52 48 321 449 321), lower := (rows 35 131 76 14 52 48 64 128 256), losses := [] }

theorem u21995 : Upper (D 6) (R 6) [34,129,72,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21995 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21996 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 76 14 52 96 337 401 273), lower := (rows 35 131 76 14 52 96 64 128 256), losses := [] }

theorem u21996 : Upper (D 6) (R 6) [34,129,72,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21997 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 195, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 14 52 288 81 209 337), lower := (rows 35 131 76 14 52 288 64 128 256), losses := [] }

theorem u21997 : Upper (D 6) (R 6) [34,129,72,6,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21997 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21998 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 14 81 36 368 432 304), lower := (rows 35 131 76 14 81 36 64 128 256), losses := [] }

theorem u21998 : Upper (D 6) (R 6) [34,129,72,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21999 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 14 81 48 356 420 292), lower := (rows 35 131 76 14 81 48 64 128 256), losses := [] }

theorem u21999 : Upper (D 6) (R 6) [34,129,72,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21999 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22000 : Route 9 := (fun mask => (mask,id))

def c22000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22000 : Upper (D 6) (R 6) [34,129,72,6,65,256] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,65,256] 13 (by decide) (choices 1) [4,16,32] r22000 c22000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6512
  · exact u6513
  · exact u6514

def b22001 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 14 112 33 340 404 276), lower := (rows 35 131 76 14 112 33 64 128 256), losses := [] }

theorem u22001 : Upper (D 6) (R 6) [34,129,72,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22002 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 14 112 36 337 401 273), lower := (rows 35 131 76 14 112 36 64 128 256), losses := [] }

theorem u22002 : Upper (D 6) (R 6) [34,129,72,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22003 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 76 14 112 48 325 389 261), lower := (rows 35 131 76 14 112 48 64 128 256), losses := [] }

theorem u22003 : Upper (D 6) (R 6) [34,129,72,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22003 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22004 : Route 9 := (fun mask => (mask,id))

def c22004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22004 : Upper (D 6) (R 6) [34,129,72,6,96,256] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,96,256] 13 (by decide) (choices 1) [1,4,16] r22004 c22004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6515
  · exact u6516
  · exact u6517

def b22005 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 14 273 36 112 240 368), lower := (rows 35 131 76 14 273 36 64 128 256), losses := [] }

theorem u22005 : Upper (D 6) (R 6) [34,129,72,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22006 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 76 14 273 48 100 228 356), lower := (rows 35 131 76 14 273 48 64 128 256), losses := [] }

theorem u22006 : Upper (D 6) (R 6) [34,129,72,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22006 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22007 : Route 9 := (fun mask => (mask,id))

def c22007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22007 : Upper (D 6) (R 6) [34,129,72,6,257,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,257,64] 13 (by decide) (choices 1) [4,16,32] r22007 c22007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6518
  · exact u6519
  · exact u6520

def b22008 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 14 276 33 112 240 368), lower := (rows 35 131 76 14 276 33 64 128 256), losses := [] }

theorem u22008 : Upper (D 6) (R 6) [34,129,72,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22009 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 14 276 48 97 225 353), lower := (rows 35 131 76 14 276 48 64 128 256), losses := [] }

theorem u22009 : Upper (D 6) (R 6) [34,129,72,6,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22009 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22010 : Route 9 := (fun mask => (mask,id))

def c22010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22010 : Upper (D 6) (R 6) [34,129,72,6,260,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,260,64] 13 (by decide) (choices 1) [1,16,32] r22010 c22010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6521
  · exact u6522
  · exact u6523

def b22011 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 14 304 33 84 212 340), lower := (rows 35 131 76 14 304 33 64 128 256), losses := [] }

theorem u22011 : Upper (D 6) (R 6) [34,129,72,6,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22012 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 14 304 36 81 209 337), lower := (rows 35 131 76 14 304 36 64 128 256), losses := [] }

theorem u22012 : Upper (D 6) (R 6) [34,129,72,6,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22013 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 76 14 304 48 69 197 325), lower := (rows 35 131 76 14 304 48 64 128 256), losses := [] }

theorem u22013 : Upper (D 6) (R 6) [34,129,72,6,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22013 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22014 : Route 9 := (fun mask => (mask,id))

def c22014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22014 : Upper (D 6) (R 6) [34,129,72,6,288,64] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,288,64] 13 (by decide) (choices 1) [1,4,16] r22014 c22014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6524
  · exact u6525
  · exact u6526

def b22015 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 14 336 33 116 180 308), lower := (rows 35 131 76 14 336 33 64 128 256), losses := [] }

theorem u22015 : Upper (D 6) (R 6) [34,129,72,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22016 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 76 14 336 36 113 177 305), lower := (rows 35 131 76 14 336 36 64 128 256), losses := [] }

theorem u22016 : Upper (D 6) (R 6) [34,129,72,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22017 : Route 9 := (fun mask => (mask,id))

def c22017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22017 : Upper (D 6) (R 6) [34,129,72,6,320,16] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,320,16] 13 (by decide) (choices 1) [1,4,32] r22017 c22017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6527
  · exact u6528
  · exact u6529

def b22018 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 76 25 22 36 352 480 352), lower := (rows 35 131 76 25 22 36 64 128 256), losses := [] }

theorem u22018 : Upper (D 6) (R 6) [34,129,72,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22019 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 76 25 22 96 356 420 292), lower := (rows 35 131 76 25 22 96 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 24 16 100 64 128 256), good := (rows 35 131 104 25 59 96 96 128 256) }] }

theorem u22019 : Upper (D 6) (R 6) [34,129,72,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22019
end Delivery.IrregularNine14.P06
