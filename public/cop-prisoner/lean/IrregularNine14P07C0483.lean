import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0183

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r28980 : Route 9 := (fun mask => (mask,id))

def c28980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28980 : Upper (D 7) (R 7) [96,260,34,17,10,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,17,10,128] 13 (by decide) (choices 1) [1,128] r28980 c28980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10987
  · exact u10988

def r28981 : Route 9 := (fun mask => (mask,id))

def c28981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28981 : Upper (D 7) (R 7) [96,260,34,17,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,34,17,130,1] 13 (by decide) (choices 1) [8,128] r28981 c28981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10989
  · exact u10990

def r28982 : Route 9 := (fun mask => (mask,id))

def c28982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28982 : Upper (D 7) (R 7) [96,260,34,17,130,8] 13 := by
  apply FastRouting.sound _ _ [96,260,34,17,130,8] 13 (by decide) (choices 1) [1,128] r28982 c28982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10991
  · exact u10992

def b28983 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 38 25 146 96 201 137 393), lower := (rows 97 262 38 25 146 96 64 128 256), losses := [] }

theorem u28983 : Upper (D 7) (R 7) [96,260,34,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28984 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 36, targets := 65 },{ cop := 4, region := 105, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(3,1)], upper := (rows 97 262 38 25 146 160 73 201 329), lower := (rows 97 262 38 25 146 160 64 128 256), losses := [] }

theorem u28984 : Upper (D 7) (R 7) [96,260,34,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28985 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(2,0)], upper := (rows 97 262 38 25 152 33 194 194 450), lower := (rows 97 262 38 25 152 33 64 128 256), losses := [] }

theorem u28985 : Upper (D 7) (R 7) [96,260,34,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28986 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 38, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 97 262 38 25 152 34 193 193 449), lower := (rows 97 262 38 25 152 34 64 128 256), losses := [] }

theorem u28986 : Upper (D 7) (R 7) [96,260,34,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28987 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 38 25 152 96 195 131 387), lower := (rows 97 262 38 25 152 96 64 128 256), losses := [] }

theorem u28987 : Upper (D 7) (R 7) [96,260,34,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28988 : Route 9 := (fun mask => (mask,id))

def c28988 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28988 : Upper (D 7) (R 7) [96,260,34,17,136,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,17,136,128] 13 (by decide) (choices 1) [1,2] r28988 c28988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10993
  · exact u10994

def b28989 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 38 25 208 33 202 138 394), lower := (rows 97 262 38 25 208 33 64 128 256), losses := [] }

theorem u28989 : Upper (D 7) (R 7) [96,260,34,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28990 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 38, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 97 262 38 25 208 34 201 137 393), lower := (rows 97 262 38 25 208 34 64 128 256), losses := [] }

theorem u28990 : Upper (D 7) (R 7) [96,260,34,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28991 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 262 38 25 208 40 195 131 387), lower := (rows 97 262 38 25 208 40 64 128 256), losses := [] }

theorem u28991 : Upper (D 7) (R 7) [96,260,34,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28991 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28992 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 422, targets := 64 },{ cop := 4, region := 41, targets := 2 }], pairs := [(0,1),(1,6),(2,6),(3,1)], upper := (rows 97 262 38 25 208 160 75 139 267), lower := (rows 97 262 38 25 208 160 64 128 256), losses := [] }

theorem u28992 : Upper (D 7) (R 7) [96,260,34,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28993 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(2,6),(4,1)], upper := (rows 97 262 38 26 145 33 200 200 456), lower := (rows 97 262 38 26 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 49 0 128 256), good := (rows 33 262 38 62 177 33 0 128 256) }] }

theorem u28993 : Upper (D 7) (R 7) [96,260,34,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28994 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 262 38 26 145 40 193 193 449), lower := (rows 97 262 38 26 145 40 64 128 256), losses := [] }

theorem u28994 : Upper (D 7) (R 7) [96,260,34,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28994 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28995 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 38 26 145 96 201 137 393), lower := (rows 97 262 38 26 145 96 64 128 256), losses := [] }

theorem u28995 : Upper (D 7) (R 7) [96,260,34,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28996 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(4,1)], upper := (rows 97 262 38 26 145 160 73 201 329), lower := (rows 97 262 38 26 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 262 38 62 176 160 64 160 256) },{ target := 6, region := (rows 1 2 12 8 16 176 0 128 256), good := (rows 33 262 38 62 177 160 0 160 256) }] }

theorem u28996 : Upper (D 7) (R 7) [96,260,34,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28997 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,5),(4,1)], upper := (rows 97 262 38 26 152 33 193 193 449), lower := (rows 97 262 38 26 152 33 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 14 20 0 97 161 289), good := (rows 449 286 478 26 152 449 64 128 256) }] }

theorem u28997 : Upper (D 7) (R 7) [96,260,34,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28998 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 38 26 152 96 193 129 385), lower := (rows 97 262 38 26 152 96 64 128 256), losses := [] }

theorem u28998 : Upper (D 7) (R 7) [96,260,34,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28999 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 97 262 38 26 152 160 65 193 321), lower := (rows 97 262 38 26 152 160 64 128 256), losses := [] }

theorem u28999 : Upper (D 7) (R 7) [96,260,34,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29000 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 97 262 38 26 208 33 201 137 393), lower := (rows 97 262 38 26 208 33 64 128 256), losses := [{ target := 7, region := (rows 81 2 12 8 16 121 64 0 256), good := (rows 97 262 38 63 113 33 97 0 256) }] }

theorem u29000 : Upper (D 7) (R 7) [96,260,34,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29001 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 262 38 26 208 40 193 129 385), lower := (rows 97 262 38 26 208 40 64 128 256), losses := [] }

theorem u29001 : Upper (D 7) (R 7) [96,260,34,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29001 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29002 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(4,1)], upper := (rows 97 262 38 26 208 160 73 137 265), lower := (rows 97 262 38 26 208 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 262 38 62 240 160 64 160 256) },{ target := 6, region := (rows 1 2 12 8 16 176 0 128 256), good := (rows 33 262 38 62 176 160 0 160 256) }] }

theorem u29002 : Upper (D 7) (R 7) [96,260,34,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29003 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 177, targets := 2 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 97 262 38 74 145 33 216 152 408), lower := (rows 97 262 38 74 145 33 64 128 256), losses := [] }

theorem u29003 : Upper (D 7) (R 7) [96,260,34,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29004 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 38 74 145 40 209 145 401), lower := (rows 97 262 38 74 145 40 64 128 256), losses := [] }

theorem u29004 : Upper (D 7) (R 7) [96,260,34,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29004 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29005 : Route 9 := (fun mask => (mask,id))

def c29005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29005 : Upper (D 7) (R 7) [96,260,34,66,129,16] 13 := by
  apply FastRouting.sound _ _ [96,260,34,66,129,16] 13 (by decide) (choices 1) [1,8,128] r29005 c29005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10995
  · exact u10996
  · exact u10997

def r29006 : Route 9 := (fun mask => (mask,id))

def c29006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29006 : Upper (D 7) (R 7) [96,260,34,66,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,66,129,128] 13 (by decide) (choices 1) [1,8,16] r29006 c29006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10998
  · exact u10999
  · exact u11000

def b29007 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 177, targets := 2 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 97 262 38 74 152 33 209 145 401), lower := (rows 97 262 38 74 152 33 64 128 256), losses := [] }

theorem u29007 : Upper (D 7) (R 7) [96,260,34,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29008 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 177, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 97 262 38 74 152 48 193 129 385), lower := (rows 97 262 38 74 152 48 64 128 256), losses := [] }

theorem u29008 : Upper (D 7) (R 7) [96,260,34,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29008 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29009 : Route 9 := (fun mask => (mask,id))

def c29009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29009 : Upper (D 7) (R 7) [96,260,34,66,136,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,66,136,128] 13 (by decide) (choices 1) [1,16] r29009 c29009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11001
  · exact u11002

def b29010 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(2,6)], upper := (rows 97 262 38 88 145 33 202 138 394), lower := (rows 97 262 38 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 16 49 0 136 264), good := (rows 33 262 38 446 177 33 0 128 256) }] }

theorem u29010 : Upper (D 7) (R 7) [96,260,34,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29011 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 38, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 97 262 38 88 145 34 201 137 393), lower := (rows 97 262 38 88 145 34 64 128 256), losses := [] }

theorem u29011 : Upper (D 7) (R 7) [96,260,34,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29012 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 38 88 145 40 195 131 387), lower := (rows 97 262 38 88 145 40 64 128 256), losses := [] }

theorem u29012 : Upper (D 7) (R 7) [96,260,34,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29012 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29013 : Route 9 := (fun mask => (mask,id))

def c29013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29013 : Upper (D 7) (R 7) [96,260,34,80,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,80,129,128] 13 (by decide) (choices 1) [1,2,8] r29013 c29013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11003
  · exact u11004
  · exact u11005

def r29014 : Route 9 := (fun mask => (mask,id))

def c29014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29014 : Upper (D 7) (R 7) [96,260,34,80,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,34,80,130,1] 13 (by decide) (choices 1) [1,8,128] r29014 c29014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11006
  · exact u11007
  · exact u11008

def b29015 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 38 88 146 40 193 129 385), lower := (rows 97 262 38 88 146 40 64 128 256), losses := [] }

theorem u29015 : Upper (D 7) (R 7) [96,260,34,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29015 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29016 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 36, targets := 65 },{ cop := 4, region := 105, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(3,1)], upper := (rows 97 262 38 88 146 160 73 137 265), lower := (rows 97 262 38 88 146 160 64 128 256), losses := [] }

theorem u29016 : Upper (D 7) (R 7) [96,260,34,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29017 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(2,6)], upper := (rows 97 262 38 88 152 33 195 131 387), lower := (rows 97 262 38 88 152 33 64 128 256), losses := [] }

theorem u29017 : Upper (D 7) (R 7) [96,260,34,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29018 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 38, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 97 262 38 88 152 34 193 129 385), lower := (rows 97 262 38 88 152 34 64 128 256), losses := [] }

theorem u29018 : Upper (D 7) (R 7) [96,260,34,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29019 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 262, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 97 262 38 88 152 160 67 131 259), lower := (rows 97 262 38 88 152 160 64 128 256), losses := [] }

theorem u29019 : Upper (D 7) (R 7) [96,260,34,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29020 : Route 9 := (fun mask => (mask,id))

def c29020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29020 : Upper (D 7) (R 7) [96,260,34,129,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,34,129,130,1] 13 (by decide) (choices 1) [8,16] r29020 c29020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11009
  · exact u11010

def r29021 : Route 9 := (fun mask => (mask,id))

def c29021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29021 : Upper (D 7) (R 7) [96,260,34,129,130,8] 13 := by
  apply FastRouting.sound _ _ [96,260,34,129,130,8] 13 (by decide) (choices 1) [1,16] r29021 c29021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11011
  · exact u11012

def b29022 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 262 38 137 146 48 73 201 329), lower := (rows 97 262 38 137 146 48 64 128 256), losses := [] }

theorem u29022 : Upper (D 7) (R 7) [96,260,34,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29022 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29023 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 38 137 146 96 89 153 281), lower := (rows 97 262 38 137 146 96 64 128 256), losses := [] }

theorem u29023 : Upper (D 7) (R 7) [96,260,34,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29024 : Route 9 := (fun mask => (mask,id))

def c29024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29024 : Upper (D 7) (R 7) [96,260,34,129,192,1] 13 := by
  apply FastRouting.sound _ _ [96,260,34,129,192,1] 13 (by decide) (choices 1) [2,8,16] r29024 c29024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11013
  · exact u11014
  · exact u11015

def b29025 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 38, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 97 262 38 137 208 34 89 153 281), lower := (rows 97 262 38 137 208 34 64 128 256), losses := [] }

theorem u29025 : Upper (D 7) (R 7) [96,260,34,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29026 : Route 9 := (fun mask => (mask,id))

def c29026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29026 : Upper (D 7) (R 7) [96,260,34,129,192,8] 13 := by
  apply FastRouting.sound _ _ [96,260,34,129,192,8] 13 (by decide) (choices 1) [1,2,16] r29026 c29026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11016
  · exact u11017
  · exact u11018

def b29027 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 38 137 208 48 75 139 267), lower := (rows 97 262 38 137 208 48 64 128 256), losses := [] }

theorem u29027 : Upper (D 7) (R 7) [96,260,34,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29027 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29028 : Route 9 := (fun mask => (mask,id))

def c29028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29028 : Upper (D 7) (R 7) [96,260,34,130,192,1] 13 := by
  apply FastRouting.sound _ _ [96,260,34,130,192,1] 13 (by decide) (choices 1) [1,8,16] r29028 c29028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11019
  · exact u11020
  · exact u11021

def b29029 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 262 38 138 208 40 81 145 273), lower := (rows 97 262 38 138 208 40 64 128 256), losses := [] }

theorem u29029 : Upper (D 7) (R 7) [96,260,34,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29029 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29030 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 38 138 208 48 73 137 265), lower := (rows 97 262 38 138 208 48 64 128 256), losses := [] }

theorem u29030 : Upper (D 7) (R 7) [96,260,34,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29030 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29031 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 44 11 82 33 208 144 400), lower := (rows 97 262 44 11 82 33 64 128 256), losses := [] }

theorem u29031 : Upper (D 7) (R 7) [96,260,40,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29032 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 11 82 48 193 129 385), lower := (rows 97 262 44 11 82 48 64 128 256), losses := [] }

theorem u29032 : Upper (D 7) (R 7) [96,260,40,3,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29032 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29033 : Route 9 := (fun mask => (mask,id))

def c29033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29033 : Upper (D 7) (R 7) [96,260,40,3,66,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,3,66,128] 13 (by decide) (choices 1) [1,16,128] r29033 c29033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11022
  · exact u11023
  · exact u11024

def b29034 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 36, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,0),(2,6),(2,7),(4,1)], upper := (rows 97 262 44 11 145 34 208 208 464), lower := (rows 97 262 44 11 145 34 64 128 256), losses := [] }

theorem u29034 : Upper (D 7) (R 7) [96,260,40,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29035 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 3, region := 208, targets := 32 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 97 262 44 11 145 48 194 194 450), lower := (rows 97 262 44 11 145 48 64 128 256), losses := [] }

theorem u29035 : Upper (D 7) (R 7) [96,260,40,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29035 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29036 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 44 11 145 96 210 146 402), lower := (rows 97 262 44 11 145 96 64 128 256), losses := [] }

theorem u29036 : Upper (D 7) (R 7) [96,260,40,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29037 : Route 9 := (fun mask => (mask,id))

def c29037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29037 : Upper (D 7) (R 7) [96,260,40,3,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,3,129,128] 13 (by decide) (choices 1) [2,16] r29037 c29037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11025
  · exact u11026

def b29038 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 44 11 146 33 208 208 464), lower := (rows 97 262 44 11 146 33 64 128 256), losses := [] }

theorem u29038 : Upper (D 7) (R 7) [96,260,40,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29039 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 193, targets := 2 },{ cop := 3, region := 208, targets := 32 }], pairs := [(0,1),(1,5),(4,5)], upper := (rows 97 262 44 11 146 48 193 193 449), lower := (rows 97 262 44 11 146 48 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 28 0 73 137 265), good := (rows 449 278 478 475 146 16 64 128 256) }] }

theorem u29039 : Upper (D 7) (R 7) [96,260,40,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29039 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29039
end Delivery.IrregularNine14.P07
