import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0099

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19980 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 388 13 112 40 86 150 278), lower := (rows 35 67 388 13 112 40 64 128 256), losses := [] }

theorem u19980 : Upper (D 6) (R 6) [34,65,384,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19980 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19981 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 388 13 112 48 78 142 270), lower := (rows 35 67 388 13 112 48 64 128 256), losses := [] }

theorem u19981 : Upper (D 6) (R 6) [34,65,384,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19981 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19982 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 25 28 34 100 228 356), lower := (rows 35 67 388 25 28 34 64 128 256), losses := [] }

theorem u19982 : Upper (D 6) (R 6) [34,65,384,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19983 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 67, targets := 4 },{ cop := 0, region := 452, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 388 25 28 36 98 226 354), lower := (rows 35 67 388 25 28 36 64 128 256), losses := [] }

theorem u19983 : Upper (D 6) (R 6) [34,65,384,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19984 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 388 25 28 96 102 166 294), lower := (rows 35 67 388 25 28 96 64 128 256), losses := [] }

theorem u19984 : Upper (D 6) (R 6) [34,65,384,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19985 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 25 52 34 76 204 332), lower := (rows 35 67 388 25 52 34 64 128 256), losses := [] }

theorem u19985 : Upper (D 6) (R 6) [34,65,384,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19986 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 388 25 52 36 74 202 330), lower := (rows 35 67 388 25 52 36 64 128 256), losses := [] }

theorem u19986 : Upper (D 6) (R 6) [34,65,384,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19987 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 388 25 52 40 70 198 326), lower := (rows 35 67 388 25 52 40 64 128 256), losses := [] }

theorem u19987 : Upper (D 6) (R 6) [34,65,384,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19987 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19988 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 388 25 52 96 78 142 270), lower := (rows 35 67 388 25 52 96 64 128 256), losses := [] }

theorem u19988 : Upper (D 6) (R 6) [34,65,384,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19989 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 25 84 34 108 172 300), lower := (rows 35 67 388 25 84 34 64 128 256), losses := [] }

theorem u19989 : Upper (D 6) (R 6) [34,65,384,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19990 : Route 9 := (fun mask => (mask,id))

def c19990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19990 : Upper (D 6) (R 6) [34,65,384,17,68,4] 13 := by
  apply FastRouting.sound _ _ [34,65,384,17,68,4] 13 (by decide) (choices 1) [2,8,32] r19990 c19990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5976
  · exact u5977
  · exact u5978

def b19991 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 388 25 84 40 102 166 294), lower := (rows 35 67 388 25 84 40 64 128 256), losses := [] }

theorem u19991 : Upper (D 6) (R 6) [34,65,384,17,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19991 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19992 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 388 28 56 33 70 198 326), lower := (rows 35 67 388 28 56 33 64 128 256), losses := [] }

theorem u19992 : Upper (D 6) (R 6) [34,65,384,20,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19993 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 28 56 34 69 197 325), lower := (rows 35 67 388 28 56 34 64 128 256), losses := [] }

theorem u19993 : Upper (D 6) (R 6) [34,65,384,20,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19994 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 56, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 388 28 56 36 67 195 323), lower := (rows 35 67 388 28 56 36 64 128 256), losses := [] }

theorem u19994 : Upper (D 6) (R 6) [34,65,384,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19995 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 388 28 56 96 71 135 263), lower := (rows 35 67 388 28 56 96 64 128 256), losses := [] }

theorem u19995 : Upper (D 6) (R 6) [34,65,384,20,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19996 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 388 28 112 33 78 142 270), lower := (rows 35 67 388 28 112 33 64 128 256), losses := [] }

theorem u19996 : Upper (D 6) (R 6) [34,65,384,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19997 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 28 112 34 77 141 269), lower := (rows 35 67 388 28 112 34 64 128 256), losses := [] }

theorem u19997 : Upper (D 6) (R 6) [34,65,384,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19998_1 : Upper (D 6) (R 6) [34,65,384,20,96,4,1] 13 :=
  permutation_upper _ _ _ [34,65,384,20,96,2,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5980

theorem m19998_2 : Upper (D 6) (R 6) [34,65,384,20,96,4,2] 13 :=
  permutation_upper _ _ _ [34,65,384,20,96,1,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5979

def r19998 : Route 9 := (fun mask => (mask,id))

def c19998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19998 : Upper (D 6) (R 6) [34,65,384,20,96,4] 13 := by
  apply FastRouting.sound _ _ [34,65,384,20,96,4] 13 (by decide) (choices 1) [1,2,8] r19998 c19998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19998_1
  · exact m19998_2
  · exact u5981

def b19999 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 388 28 112 40 71 135 263), lower := (rows 35 67 388 28 112 40 64 128 256), losses := [] }

theorem u19999 : Upper (D 6) (R 6) [34,65,384,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19999 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20000 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 388 44 84 33 90 154 282), lower := (rows 35 67 388 44 84 33 64 128 256), losses := [] }

theorem u20000 : Upper (D 6) (R 6) [34,65,384,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20001 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 44 84 34 89 153 281), lower := (rows 35 67 388 44 84 34 64 128 256), losses := [] }

theorem u20001 : Upper (D 6) (R 6) [34,65,384,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20002 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 388 44 84 40 83 147 275), lower := (rows 35 67 388 44 84 40 64 128 256), losses := [] }

theorem u20002 : Upper (D 6) (R 6) [34,65,384,36,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20002 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20003 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 388 44 84 48 75 139 267), lower := (rows 35 67 388 44 84 48 64 128 256), losses := [] }

theorem u20003 : Upper (D 6) (R 6) [34,65,384,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20003 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20004 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 388 44 88 33 86 150 278), lower := (rows 35 67 388 44 88 33 64 128 256), losses := [] }

theorem u20004 : Upper (D 6) (R 6) [34,65,384,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20005 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 388 44 88 34 85 149 277), lower := (rows 35 67 388 44 88 34 64 128 256), losses := [] }

theorem u20005 : Upper (D 6) (R 6) [34,65,384,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20006 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 388 44 88 36 83 147 275), lower := (rows 35 67 388 44 88 36 64 128 256), losses := [] }

theorem u20006 : Upper (D 6) (R 6) [34,65,384,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20007 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 388 44 88 48 71 135 263), lower := (rows 35 67 388 44 88 48 64 128 256), losses := [] }

theorem u20007 : Upper (D 6) (R 6) [34,65,384,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20007 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20008 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 44 25 146 33 324 452 324), lower := (rows 35 70 44 25 146 33 64 128 256), losses := [] }

theorem u20008 : Upper (D 6) (R 6) [34,68,40,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20009 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 25 146 36 321 449 321), lower := (rows 35 70 44 25 146 36 64 128 256), losses := [] }

theorem u20009 : Upper (D 6) (R 6) [34,68,40,17,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20010 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 25 146 96 325 389 261), lower := (rows 35 70 44 25 146 96 64 128 256), losses := [] }

theorem u20010 : Upper (D 6) (R 6) [34,68,40,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20011 : Route 9 := (fun mask => (mask,id))

def c20011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20011 : Upper (D 6) (R 6) [34,68,40,17,130,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17,130,256] 13 (by decide) (choices 1) [1,4] r20011 c20011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5982
  · exact u5983

def b20012 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 44 25 148 33 322 450 322), lower := (rows 35 70 44 25 148 33 64 128 256), losses := [] }

theorem u20012 : Upper (D 6) (R 6) [34,68,40,17,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20013 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 25 148 34 321 449 321), lower := (rows 35 70 44 25 148 34 64 128 256), losses := [] }

theorem u20013 : Upper (D 6) (R 6) [34,68,40,17,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20014 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 25 148 96 323 387 259), lower := (rows 35 70 44 25 148 96 64 128 256), losses := [] }

theorem u20014 : Upper (D 6) (R 6) [34,68,40,17,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20015 : Route 9 := (fun mask => (mask,id))

def c20015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20015 : Upper (D 6) (R 6) [34,68,40,17,132,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17,132,256] 13 (by decide) (choices 1) [1,2] r20015 c20015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5984
  · exact u5985

def b20016 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 44 25 208 33 326 390 262), lower := (rows 35 70 44 25 208 33 64 128 256), losses := [] }

theorem u20016 : Upper (D 6) (R 6) [34,68,40,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20017 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 25 208 34 325 389 261), lower := (rows 35 70 44 25 208 34 64 128 256), losses := [] }

theorem u20017 : Upper (D 6) (R 6) [34,68,40,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20018 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 25 208 36 323 387 259), lower := (rows 35 70 44 25 208 36 64 128 256), losses := [] }

theorem u20018 : Upper (D 6) (R 6) [34,68,40,17,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20019 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 44 25 208 288 71 135 263), lower := (rows 35 70 44 25 208 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 291 0 130 258), good := (rows 419 423 44 61 144 288 0 128 288) }] }

theorem u20019 : Upper (D 6) (R 6) [34,68,40,17,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20019 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20020 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 44 25 400 33 70 198 326), lower := (rows 35 70 44 25 400 33 64 128 256), losses := [] }

theorem u20020 : Upper (D 6) (R 6) [34,68,40,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20021 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 44 25 400 34 69 197 325), lower := (rows 35 70 44 25 400 34 64 128 256), losses := [] }

theorem u20021 : Upper (D 6) (R 6) [34,68,40,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20022 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 25 400 36 67 195 323), lower := (rows 35 70 44 25 400 36 64 128 256), losses := [] }

theorem u20022 : Upper (D 6) (R 6) [34,68,40,17,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20023 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 25 400 96 71 135 263), lower := (rows 35 70 44 25 400 96 64 128 256), losses := [] }

theorem u20023 : Upper (D 6) (R 6) [34,68,40,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20024 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 44 26 81 33 452 388 388), lower := (rows 35 70 44 26 81 33 64 128 256), losses := [] }

theorem u20024 : Upper (D 6) (R 6) [34,68,40,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20025 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 26 81 36 449 385 385), lower := (rows 35 70 44 26 81 36 64 128 256), losses := [] }

theorem u20025 : Upper (D 6) (R 6) [34,68,40,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20026 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 44 26 81 160 325 389 261), lower := (rows 35 70 44 26 81 160 64 128 256), losses := [] }

theorem u20026 : Upper (D 6) (R 6) [34,68,40,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20026 [(5,7)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20027 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 322, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 44 26 145 33 324 452 324), lower := (rows 35 70 44 26 145 33 64 128 256), losses := [] }

theorem u20027 : Upper (D 6) (R 6) [34,68,40,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20028 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 26 145 36 321 449 321), lower := (rows 35 70 44 26 145 36 64 128 256), losses := [] }

theorem u20028 : Upper (D 6) (R 6) [34,68,40,18,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20029 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 26 145 96 325 389 261), lower := (rows 35 70 44 26 145 96 64 128 256), losses := [] }

theorem u20029 : Upper (D 6) (R 6) [34,68,40,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20030 : Route 9 := (fun mask => (mask,id))

def c20030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20030 : Upper (D 6) (R 6) [34,68,40,18,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18,129,256] 13 (by decide) (choices 1) [1,4] r20030 c20030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5986
  · exact u5987

def b20031 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 44 26 148 33 321 449 321), lower := (rows 35 70 44 26 148 33 64 128 256), losses := [] }

theorem u20031 : Upper (D 6) (R 6) [34,68,40,18,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20032 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 26 148 96 321 385 257), lower := (rows 35 70 44 26 148 96 64 128 256), losses := [] }

theorem u20032 : Upper (D 6) (R 6) [34,68,40,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20033 : Route 9 := (fun mask => (mask,id))

def c20033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20033 : Upper (D 6) (R 6) [34,68,40,18,132,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18,132,256] 13 (by decide) (choices 1) [1] r20033 c20033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u5988

def b20034 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 44 26 208 33 325 389 261), lower := (rows 35 70 44 26 208 33 64 128 256), losses := [] }

theorem u20034 : Upper (D 6) (R 6) [34,68,40,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20035 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 26 208 36 321 385 257), lower := (rows 35 70 44 26 208 36 64 128 256), losses := [] }

theorem u20035 : Upper (D 6) (R 6) [34,68,40,18,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20036 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 44 26 208 288 69 133 261), lower := (rows 35 70 44 26 208 288 64 128 256), losses := [] }

theorem u20036 : Upper (D 6) (R 6) [34,68,40,18,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20036 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20037 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 44 26 400 33 69 197 325), lower := (rows 35 70 44 26 400 33 64 128 256), losses := [] }

theorem u20037 : Upper (D 6) (R 6) [34,68,40,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20038 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 44 26 400 36 65 193 321), lower := (rows 35 70 44 26 400 36 64 128 256), losses := [] }

theorem u20038 : Upper (D 6) (R 6) [34,68,40,18,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20039 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 26 400 96 69 133 261), lower := (rows 35 70 44 26 400 96 64 128 256), losses := [] }

theorem u20039 : Upper (D 6) (R 6) [34,68,40,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20039
end Delivery.IrregularNine14.P06
