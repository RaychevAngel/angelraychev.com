import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0333
import IrregularNine14P07C0334

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34980 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 292 25 82 169 201 137 393), lower := (rows 35 70 292 25 82 32 64 128 256), losses := [] }

theorem u34980 : Upper (D 7) (R 7) [34,68,288,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34981 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 292 25 88 163 195 131 387), lower := (rows 35 70 292 25 88 32 64 128 256), losses := [] }

theorem u34981 : Upper (D 7) (R 7) [34,68,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34982 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 292 25 145 234 202 202 458), lower := (rows 35 70 292 25 145 32 64 128 256), losses := [] }

theorem u34982 : Upper (D 7) (R 7) [34,68,288,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34983 : Route 9 := (fun mask => (mask,id))

def c34983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34983 : Upper (D 7) (R 7) [34,68,288,17,130] 13 := by
  apply FastRouting.sound _ _ [34,68,288,17,130] 13 (by decide) (choices 1) [1,8,64,128] r34983 c34983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20001
  · exact u20002
  · exact u20003
  · exact u20004

def r34984 : Route 9 := (fun mask => (mask,id))

def c34984 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34984 : Upper (D 7) (R 7) [34,68,288,17,136] 13 := by
  apply FastRouting.sound _ _ [34,68,288,17,136] 13 (by decide) (choices 1) [1,2,64,128] r34984 c34984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20005
  · exact u20006
  · exact u20007
  · exact u20008

def r34985 : Route 9 := (fun mask => (mask,id))

def c34985 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34985 : Upper (D 7) (R 7) [34,68,288,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,288,17,192] 13 (by decide) (choices 1) [1,2,8,128] r34985 c34985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20009
  · exact u20010
  · exact u20011
  · exact u20012

def b34986 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 292 26 81 169 201 137 393), lower := (rows 35 70 292 26 81 32 64 128 256), losses := [] }

theorem u34986 : Upper (D 7) (R 7) [34,68,288,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34987 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 35 70 292 26 88 161 193 129 385), lower := (rows 35 70 292 26 88 32 64 128 256), losses := [] }

theorem u34987 : Upper (D 7) (R 7) [34,68,288,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34988 : Route 9 := (fun mask => (mask,id))

def c34988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34988 : Upper (D 7) (R 7) [34,68,288,18,129] 13 := by
  apply FastRouting.sound _ _ [34,68,288,18,129] 13 (by decide) (choices 1) [1,8,64,128] r34988 c34988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20013
  · exact u20014
  · exact u20015
  · exact u20016

def r34989 : Route 9 := (fun mask => (mask,id))

def c34989 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34989 : Upper (D 7) (R 7) [34,68,288,18,136] 13 := by
  apply FastRouting.sound _ _ [34,68,288,18,136] 13 (by decide) (choices 1) [1,64,128] r34989 c34989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20017
  · exact u20018
  · exact u20019

def b34990 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 292 26 208 169 201 137 393), lower := (rows 35 70 292 26 208 32 64 128 256), losses := [] }

theorem u34990 : Upper (D 7) (R 7) [34,68,288,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34991 : Route 9 := (fun mask => (mask,id))

def c34991 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34991 : Upper (D 7) (R 7) [34,68,288,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,288,65,129] 13 (by decide) (choices 1) [2,8,16,128] r34991 c34991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20020
  · exact u20021
  · exact u20022
  · exact u20023

def r34992 : Route 9 := (fun mask => (mask,id))

def c34992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34992 : Upper (D 7) (R 7) [34,68,288,65,130] 13 := by
  apply FastRouting.sound _ _ [34,68,288,65,130] 13 (by decide) (choices 1) [1,8,16,128] r34992 c34992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20024
  · exact u20025
  · exact u20026
  · exact u20027

def r34993 : Route 9 := (fun mask => (mask,id))

def c34993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34993 : Upper (D 7) (R 7) [34,68,288,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,288,65,136] 13 (by decide) (choices 1) [1,2,16,128] r34993 c34993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20028
  · exact u20029
  · exact u20030
  · exact u20031

def b34994 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 292 74 145 185 217 153 409), lower := (rows 35 70 292 74 145 32 64 128 256), losses := [] }

theorem u34994 : Upper (D 7) (R 7) [34,68,288,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34995 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 292 74 152 177 209 145 401), lower := (rows 35 70 292 74 152 32 64 128 256), losses := [] }

theorem u34995 : Upper (D 7) (R 7) [34,68,288,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34996 : Route 9 := (fun mask => (mask,id))

def c34996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34996 : Upper (D 7) (R 7) [34,68,288,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,288,80,129] 13 (by decide) (choices 1) [1,2,8,128] r34996 c34996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20032
  · exact u20033
  · exact u20034
  · exact u20035

def r34997 : Route 9 := (fun mask => (mask,id))

def c34997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34997 : Upper (D 7) (R 7) [34,68,288,80,130] 13 := by
  apply FastRouting.sound _ _ [34,68,288,80,130] 13 (by decide) (choices 1) [1,8,128] r34997 c34997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20036
  · exact u20037
  · exact u20038

def b34998 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 292 88 152 163 195 131 387), lower := (rows 35 70 292 88 152 32 64 128 256), losses := [] }

theorem u34998 : Upper (D 7) (R 7) [34,68,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34999 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 70 292 137 145 122 90 218 346), lower := (rows 35 70 292 137 145 32 64 128 256), losses := [] }

theorem u34999 : Upper (D 7) (R 7) [34,68,288,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35000 : Route 9 := (fun mask => (mask,id))

def c35000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35000 : Upper (D 7) (R 7) [34,68,288,129,130] 13 := by
  apply FastRouting.sound _ _ [34,68,288,129,130] 13 (by decide) (choices 1) [1,8,16,64] r35000 c35000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20039
  · exact u20040
  · exact u20041
  · exact u20042

def b35001 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 70 292 137 152 115 83 211 339), lower := (rows 35 70 292 137 152 32 64 128 256), losses := [] }

theorem u35001 : Upper (D 7) (R 7) [34,68,288,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35002 : Route 9 := (fun mask => (mask,id))

def c35002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35002 : Upper (D 7) (R 7) [34,68,288,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,288,129,192] 13 (by decide) (choices 1) [1,2,8,16] r35002 c35002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20043
  · exact u20044
  · exact u20045
  · exact u20046

def b35003 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 70 292 138 152 113 81 209 337), lower := (rows 35 70 292 138 152 32 64 128 256), losses := [] }

theorem u35003 : Upper (D 7) (R 7) [34,68,288,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35004 : Route 9 := (fun mask => (mask,id))

def c35004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35004 : Upper (D 7) (R 7) [34,68,288,130,192] 13 := by
  apply FastRouting.sound _ _ [34,68,288,130,192] 13 (by decide) (choices 1) [1,8,16] r35004 c35004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20047
  · exact u20048
  · exact u20049

def b35005 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 292 152 152 99 67 195 323), lower := (rows 35 70 292 152 152 32 64 128 256), losses := [] }

theorem u35005 : Upper (D 7) (R 7) [34,68,288,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35006 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 292 152 208 43 75 139 267), lower := (rows 35 70 292 152 208 32 64 128 256), losses := [] }

theorem u35006 : Upper (D 7) (R 7) [34,68,288,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35007 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 388 11 25 240 240 240 496), lower := (rows 35 70 388 11 25 32 64 128 256), losses := [] }

theorem u35007 : Upper (D 7) (R 7) [34,68,384,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35008 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 388 11 56 241 209 209 465), lower := (rows 35 70 388 11 56 32 64 128 256), losses := [] }

theorem u35008 : Upper (D 7) (R 7) [34,68,384,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35009 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 11 81 184 248 184 440), lower := (rows 35 70 388 11 81 32 64 128 256), losses := [] }

theorem u35009 : Upper (D 7) (R 7) [34,68,384,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35010 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 11 88 177 241 177 433), lower := (rows 35 70 388 11 88 32 64 128 256), losses := [] }

theorem u35010 : Upper (D 7) (R 7) [34,68,384,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35011 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 11 112 185 217 153 409), lower := (rows 35 70 388 11 112 32 64 128 256), losses := [] }

theorem u35011 : Upper (D 7) (R 7) [34,68,384,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35012 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 11 145 120 120 248 376), lower := (rows 35 70 388 11 145 32 64 128 256), losses := [] }

theorem u35012 : Upper (D 7) (R 7) [34,68,384,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35013 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 11 152 113 113 241 369), lower := (rows 35 70 388 11 152 32 64 128 256), losses := [] }

theorem u35013 : Upper (D 7) (R 7) [34,68,384,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35014 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 11 176 121 89 217 345), lower := (rows 35 70 388 11 176 32 64 128 256), losses := [] }

theorem u35014 : Upper (D 7) (R 7) [34,68,384,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35015 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 11 208 57 121 185 313), lower := (rows 35 70 388 11 208 32 64 128 256), losses := [] }

theorem u35015 : Upper (D 7) (R 7) [34,68,384,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35016 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 25 25 226 226 226 482), lower := (rows 35 70 388 25 25 32 64 128 256), losses := [] }

theorem u35016 : Upper (D 7) (R 7) [34,68,384,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35017 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 388 25 26 225 225 225 481), lower := (rows 35 70 388 25 26 32 64 128 256), losses := [] }

theorem u35017 : Upper (D 7) (R 7) [34,68,384,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35018 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 388 25 49 234 202 202 458), lower := (rows 35 70 388 25 49 32 64 128 256), losses := [] }

theorem u35018 : Upper (D 7) (R 7) [34,68,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35019 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 388 25 50 233 201 201 457), lower := (rows 35 70 388 25 50 32 64 128 256), losses := [] }

theorem u35019 : Upper (D 7) (R 7) [34,68,384,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35020 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 388 25 56 227 195 195 451), lower := (rows 35 70 388 25 56 32 64 128 256), losses := [] }

theorem u35020 : Upper (D 7) (R 7) [34,68,384,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35021 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 25 81 170 234 170 426), lower := (rows 35 70 388 25 81 32 64 128 256), losses := [] }

theorem u35021 : Upper (D 7) (R 7) [34,68,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35022 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 388 25 82 169 233 169 425), lower := (rows 35 70 388 25 82 32 64 128 256), losses := [] }

theorem u35022 : Upper (D 7) (R 7) [34,68,384,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35023 : Route 9 := (fun mask => (mask,id))

def c35023 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35023 : Upper (D 7) (R 7) [34,68,384,17,72] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,72] 13 (by decide) (choices 1) [1,2,128] r35023 c35023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20050
  · exact u20051
  · exact u20052

def r35024 : Route 9 := (fun mask => (mask,id))

def c35024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35024 : Upper (D 7) (R 7) [34,68,384,17,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,96] 13 (by decide) (choices 1) [1,2,8,128] r35024 c35024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20053
  · exact u20054
  · exact u20055
  · exact u20056

def b35025 : PairBound 9 := { available := 106, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 25 145 106 106 234 362), lower := (rows 35 70 388 25 145 32 64 128 256), losses := [] }

theorem u35025 : Upper (D 7) (R 7) [34,68,384,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35026 : Route 9 := (fun mask => (mask,id))

def c35026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35026 : Upper (D 7) (R 7) [34,68,384,17,130] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,130] 13 (by decide) (choices 1) [1,8,64] r35026 c35026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20057
  · exact u20058
  · exact u20059

def r35027 : Route 9 := (fun mask => (mask,id))

def c35027 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35027 : Upper (D 7) (R 7) [34,68,384,17,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,136] 13 (by decide) (choices 1) [1,2,64] r35027 c35027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20060
  · exact u20061
  · exact u20062

def r35028 : Route 9 := (fun mask => (mask,id))

def c35028 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35028 : Upper (D 7) (R 7) [34,68,384,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,160] 13 (by decide) (choices 1) [1,2,8,64] r35028 c35028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20063
  · exact u20064
  · exact u20065
  · exact u20066

def r35029 : Route 9 := (fun mask => (mask,id))

def c35029 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35029 : Upper (D 7) (R 7) [34,68,384,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,192] 13 (by decide) (choices 1) [1,2,8] r35029 c35029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20067
  · exact u20068
  · exact u20069

def b35030 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 388 26 49 233 201 201 457), lower := (rows 35 70 388 26 49 32 64 128 256), losses := [] }

theorem u35030 : Upper (D 7) (R 7) [34,68,384,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35031 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 388 26 56 225 193 193 449), lower := (rows 35 70 388 26 56 32 64 128 256), losses := [] }

theorem u35031 : Upper (D 7) (R 7) [34,68,384,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35032 : Route 9 := (fun mask => (mask,id))

def c35032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35032 : Upper (D 7) (R 7) [34,68,384,18,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,65] 13 (by decide) (choices 1) [1,8,128] r35032 c35032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20070
  · exact u20071
  · exact u20072

def b35033 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 35 70 388 26 88 161 225 161 417), lower := (rows 35 70 388 26 88 32 64 128 256), losses := [] }

theorem u35033 : Upper (D 7) (R 7) [34,68,384,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35034 : Route 9 := (fun mask => (mask,id))

def c35034 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35034 : Upper (D 7) (R 7) [34,68,384,18,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,96] 13 (by decide) (choices 1) [1,8,128] r35034 c35034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20073
  · exact u20074
  · exact u20075

def r35035 : Route 9 := (fun mask => (mask,id))

def c35035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35035 : Upper (D 7) (R 7) [34,68,384,18,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,129] 13 (by decide) (choices 1) [1,8,64] r35035 c35035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20076
  · exact u20077
  · exact u20078

def r35036 : Route 9 := (fun mask => (mask,id))

def c35036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35036 : Upper (D 7) (R 7) [34,68,384,18,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,136] 13 (by decide) (choices 1) [1,64] r35036 c35036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20079
  · exact u20080

def r35037 : Route 9 := (fun mask => (mask,id))

def c35037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35037 : Upper (D 7) (R 7) [34,68,384,18,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,160] 13 (by decide) (choices 1) [1,8,64] r35037 c35037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20081
  · exact u20082
  · exact u20083

def r35038 : Route 9 := (fun mask => (mask,id))

def c35038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35038 : Upper (D 7) (R 7) [34,68,384,18,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,192] 13 (by decide) (choices 1) [1,8] r35038 c35038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20084
  · exact u20085

def b35039 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 388 41 81 186 218 154 410), lower := (rows 35 70 388 41 81 32 64 128 256), losses := [] }

theorem u35039 : Upper (D 7) (R 7) [34,68,384,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u35039
end Delivery.IrregularNine14.P07
