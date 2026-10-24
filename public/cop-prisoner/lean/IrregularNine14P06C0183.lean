import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0025

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10980 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 388 26 52 96 73 137 265), lower := (rows 7 98 388 26 52 96 64 128 256), losses := [] }

theorem u10980 : Upper (D 6) (R 6) [6,96,384,18,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10980
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10981 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 98 388 28 49 33 74 202 330), lower := (rows 7 98 388 28 49 33 64 128 256), losses := [] }

theorem u10981 : Upper (D 6) (R 6) [6,96,384,20,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10981
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10982 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 98 388 28 49 34 73 201 329), lower := (rows 7 98 388 28 49 34 64 128 256), losses := [] }

theorem u10982 : Upper (D 6) (R 6) [6,96,384,20,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10982
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10983 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 7 98 388 28 49 40 67 195 323), lower := (rows 7 98 388 28 49 40 64 128 256), losses := [] }

theorem u10983 : Upper (D 6) (R 6) [6,96,384,20,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10983
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10984 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 388 28 49 96 75 139 267), lower := (rows 7 98 388 28 49 96 64 128 256), losses := [] }

theorem u10984 : Upper (D 6) (R 6) [6,96,384,20,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10984
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10985 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 388 41 81 34 92 156 284), lower := (rows 7 98 388 41 81 34 64 128 256), losses := [] }

theorem u10985 : Upper (D 6) (R 6) [6,96,384,33,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10985
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10986 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 82, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 98 388 41 81 36 90 154 282), lower := (rows 7 98 388 41 81 36 64 128 256), losses := [] }

theorem u10986 : Upper (D 6) (R 6) [6,96,384,33,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10986
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10987 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 388 41 81 40 86 150 278), lower := (rows 7 98 388 41 81 40 64 128 256), losses := [] }

theorem u10987 : Upper (D 6) (R 6) [6,96,384,33,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10987
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10988 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 388 41 81 48 78 142 270), lower := (rows 7 98 388 41 81 48 64 128 256), losses := [] }

theorem u10988 : Upper (D 6) (R 6) [6,96,384,33,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10988
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10989 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 98 388 41 84 33 90 154 282), lower := (rows 7 98 388 41 84 33 64 128 256), losses := [] }

theorem u10989 : Upper (D 6) (R 6) [6,96,384,33,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10989
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10990 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 388 41 84 34 89 153 281), lower := (rows 7 98 388 41 84 34 64 128 256), losses := [] }

theorem u10990 : Upper (D 6) (R 6) [6,96,384,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10990
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10991 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 388 41 84 40 83 147 275), lower := (rows 7 98 388 41 84 40 64 128 256), losses := [] }

theorem u10991 : Upper (D 6) (R 6) [6,96,384,33,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10991
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10992 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 388 41 84 48 75 139 267), lower := (rows 7 98 388 41 84 48 64 128 256), losses := [] }

theorem u10992 : Upper (D 6) (R 6) [6,96,384,33,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10992
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10993 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 98 388 41 88 33 86 150 278), lower := (rows 7 98 388 41 88 33 64 128 256), losses := [] }

theorem u10993 : Upper (D 6) (R 6) [6,96,384,33,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10993
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10994 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 388 41 88 34 85 149 277), lower := (rows 7 98 388 41 88 34 64 128 256), losses := [] }

theorem u10994 : Upper (D 6) (R 6) [6,96,384,33,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10994
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10995 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 82, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 98 388 41 88 36 83 147 275), lower := (rows 7 98 388 41 88 36 64 128 256), losses := [] }

theorem u10995 : Upper (D 6) (R 6) [6,96,384,33,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10995
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10996 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 388 41 88 48 71 135 263), lower := (rows 7 98 388 41 88 48 64 128 256), losses := [] }

theorem u10996 : Upper (D 6) (R 6) [6,96,384,33,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10996
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10997 : Route 9 := (fun mask => (mask,id))

def c10997 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10997 : Upper (D 6) (R 6) [6,96,384,36,72,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,36,72,1] 13 (by decide) (choices 1) [1,2,16] r10997 c10997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1518
  · exact u1519
  · exact u1520

def b10998 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 388 44 88 34 81 145 273), lower := (rows 7 98 388 44 88 34 64 128 256), losses := [] }

theorem u10998 : Upper (D 6) (R 6) [6,96,384,36,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10998
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10999 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 388 44 88 48 67 131 259), lower := (rows 7 98 388 44 88 48 64 128 256), losses := [] }

theorem u10999 : Upper (D 6) (R 6) [6,96,384,36,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10999
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11000 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 261 26 52 40 96 224 352), lower := (rows 7 131 261 26 52 40 64 128 256), losses := [] }

theorem u11000 : Upper (D 6) (R 6) [6,129,257,18,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11000
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11001 : Route 9 := (fun mask => (mask,id))

def c11001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11001 : Upper (D 6) (R 6) [6,129,257,18,36,64] 13 := by
  apply FastRouting.sound _ _ [6,129,257,18,36,64] 13 (by decide) (choices 1) [8,32] r11001 c11001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1521
  · exact u1522

def r11002 : Route 9 := (fun mask => (mask,id))

def c11002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11002 : Upper (D 6) (R 6) [6,129,257,18,96,4] 13 := by
  apply FastRouting.sound _ _ [6,129,257,18,96,4] 13 (by decide) (choices 1) [8,32] r11002 c11002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1523
  · exact u1524

def b11003 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 261 26 112 40 100 228 356), lower := (rows 7 131 261 26 112 40 64 128 256), losses := [] }

theorem u11003 : Upper (D 6) (R 6) [6,129,257,18,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11003
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11004 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 261 26 112 96 108 172 300), lower := (rows 7 131 261 26 112 96 64 128 256), losses := [] }

theorem u11004 : Upper (D 6) (R 6) [6,129,257,18,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11004
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11005 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 131 261 42 52 40 80 208 336), lower := (rows 7 131 261 42 52 40 64 128 256), losses := [] }

theorem u11005 : Upper (D 6) (R 6) [6,129,257,34,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11005
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m11006_16 : Upper (D 6) (R 6) [6,129,257,34,36,64,16] 13 :=
  permutation_upper _ _ _ [6,129,257,34,36,64,8] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1525

def r11006 : Route 9 := (fun mask => (mask,id))

def c11006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11006 : Upper (D 6) (R 6) [6,129,257,34,36,64] 13 := by
  apply FastRouting.sound _ _ [6,129,257,34,36,64] 13 (by decide) (choices 1) [8,16] r11006 c11006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1525
  · exact m11006_16

def b11007 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 131 261 42 84 40 112 240 368), lower := (rows 7 131 261 42 84 40 64 128 256), losses := [] }

theorem u11007 : Upper (D 6) (R 6) [6,129,257,34,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11007
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11008 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 261 42 84 48 104 232 360), lower := (rows 7 131 261 42 84 48 64 128 256), losses := [] }

theorem u11008 : Upper (D 6) (R 6) [6,129,257,34,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11008
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m11009_8 : Upper (D 6) (R 6) [6,129,257,34,68,64,8] 13 :=
  permutation_upper _ _ _ [6,129,257,34,68,16,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1527

theorem m11009_16 : Upper (D 6) (R 6) [6,129,257,34,68,64,16] 13 :=
  permutation_upper _ _ _ [6,129,257,34,68,8,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1526

def r11009 : Route 9 := (fun mask => (mask,id))

def c11009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11009 : Upper (D 6) (R 6) [6,129,257,34,68,64] 13 := by
  apply FastRouting.sound _ _ [6,129,257,34,68,64] 13 (by decide) (choices 1) [8,16,32] r11009 c11009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m11009_8
  · exact m11009_16
  · exact u1528

def b11010 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 80, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 261 42 88 36 112 240 368), lower := (rows 7 131 261 42 88 36 64 128 256), losses := [] }

theorem u11010 : Upper (D 6) (R 6) [6,129,257,34,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11010
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11011 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 131 261 42 88 48 100 228 356), lower := (rows 7 131 261 42 88 48 64 128 256), losses := [] }

theorem u11011 : Upper (D 6) (R 6) [6,129,257,34,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11011
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11012 : Route 9 := (fun mask => (mask,id))

def c11012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11012 : Upper (D 6) (R 6) [6,129,257,34,72,64] 13 := by
  apply FastRouting.sound _ _ [6,129,257,34,72,64] 13 (by decide) (choices 1) [4,16,32] r11012 c11012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1529
  · exact u1530
  · exact u1531

def b11013 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 80, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 131 261 42 112 36 88 216 344), lower := (rows 7 131 261 42 112 36 64 128 256), losses := [] }

theorem u11013 : Upper (D 6) (R 6) [6,129,257,34,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11013
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11014 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 131 261 42 112 40 84 212 340), lower := (rows 7 131 261 42 112 40 64 128 256), losses := [] }

theorem u11014 : Upper (D 6) (R 6) [6,129,257,34,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11014
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11015 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 261 42 112 48 76 204 332), lower := (rows 7 131 261 42 112 48 64 128 256), losses := [] }

theorem u11015 : Upper (D 6) (R 6) [6,129,257,34,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11015
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11016 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 261 42 112 96 92 156 284), lower := (rows 7 131 261 42 112 96 64 128 256), losses := [] }

theorem u11016 : Upper (D 6) (R 6) [6,129,257,34,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11016
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11017 : Route 9 := (fun mask => (mask,id))

def c11017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11017 : Upper (D 6) (R 6) [6,129,257,48,72,2] 13 := by
  apply FastRouting.sound _ _ [6,129,257,48,72,2] 13 (by decide) (choices 1) [4,32] r11017 c11017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1532
  · exact u1533

def b11018 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 131 261 56 88 96 102 166 294), lower := (rows 7 131 261 56 88 96 64 128 256), losses := [] }

theorem u11018 : Upper (D 6) (R 6) [6,129,257,48,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11018
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11019 : Route 9 := (fun mask => (mask,id))

def c11019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11019 : Upper (D 6) (R 6) [6,129,264,17,96,2] 13 := by
  apply FastRouting.sound _ _ [6,129,264,17,96,2] 13 (by decide) (choices 1) [4,32] r11019 c11019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1534
  · exact u1535

theorem m11020_2 : Upper (D 6) (R 6) [6,129,264,17,96,4,2] 13 :=
  permutation_upper _ _ _ [6,129,264,17,96,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1534

def r11020 : Route 9 := (fun mask => (mask,id))

def c11020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11020 : Upper (D 6) (R 6) [6,129,264,17,96,4] 13 := by
  apply FastRouting.sound _ _ [6,129,264,17,96,4] 13 (by decide) (choices 1) [2,32] r11020 c11020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11020_2
  · exact u1536

def b11021 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 25 112 96 102 166 294), lower := (rows 7 131 268 25 112 96 64 128 256), losses := [] }

theorem u11021 : Upper (D 6) (R 6) [6,129,264,17,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11021
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11022 : Route 9 := (fun mask => (mask,id))

def c11022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11022 : Upper (D 6) (R 6) [6,129,264,18,96,1] 13 := by
  apply FastRouting.sound _ _ [6,129,264,18,96,1] 13 (by decide) (choices 1) [4,32] r11022 c11022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1537
  · exact u1538

theorem m11023_1 : Upper (D 6) (R 6) [6,129,264,18,96,4,1] 13 :=
  permutation_upper _ _ _ [6,129,264,18,96,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1537

def r11023 : Route 9 := (fun mask => (mask,id))

def c11023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11023 : Upper (D 6) (R 6) [6,129,264,18,96,4] 13 := by
  apply FastRouting.sound _ _ [6,129,264,18,96,4] 13 (by decide) (choices 1) [1,32] r11023 c11023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11023_1
  · exact u1539

def b11024 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 26 112 96 101 165 293), lower := (rows 7 131 268 26 112 96 64 128 256), losses := [] }

theorem u11024 : Upper (D 6) (R 6) [6,129,264,18,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11024
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11025 : Route 9 := (fun mask => (mask,id))

def c11025 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11025 : Upper (D 6) (R 6) [6,129,264,20,96,1] 13 := by
  apply FastRouting.sound _ _ [6,129,264,20,96,1] 13 (by decide) (choices 1) [2,32] r11025 c11025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1540
  · exact u1541

theorem m11026_1 : Upper (D 6) (R 6) [6,129,264,20,96,2,1] 13 :=
  permutation_upper _ _ _ [6,129,264,20,96,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1540

def r11026 : Route 9 := (fun mask => (mask,id))

def c11026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11026 : Upper (D 6) (R 6) [6,129,264,20,96,2] 13 := by
  apply FastRouting.sound _ _ [6,129,264,20,96,2] 13 (by decide) (choices 1) [1,32] r11026 c11026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11026_1
  · exact u1542

def b11027 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 131 268 28 112 96 99 163 291), lower := (rows 7 131 268 28 112 96 64 128 256), losses := [] }

theorem u11027 : Upper (D 6) (R 6) [6,129,264,20,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11027
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11028 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 56, targets := 64 },{ cop := 3, region := 210, targets := 4 }], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 131 268 41 50 36 80 208 336), lower := (rows 7 131 268 41 50 36 64 128 256), losses := [] }

theorem u11028 : Upper (D 6) (R 6) [6,129,264,33,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11028
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11029 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 7 131 268 41 50 48 68 196 324), lower := (rows 7 131 268 41 50 48 64 128 256), losses := [] }

theorem u11029 : Upper (D 6) (R 6) [6,129,264,33,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11029
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11030 : Route 9 := (fun mask => (mask,id))

def c11030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11030 : Upper (D 6) (R 6) [6,129,264,33,34,64] 13 := by
  apply FastRouting.sound _ _ [6,129,264,33,34,64] 13 (by decide) (choices 1) [4,16] r11030 c11030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1543
  · exact u1544

def b11031 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 210, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 131 268 41 82 36 112 240 368), lower := (rows 7 131 268 41 82 36 64 128 256), losses := [] }

theorem u11031 : Upper (D 6) (R 6) [6,129,264,33,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11031
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11032 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 131 268 41 82 48 100 228 356), lower := (rows 7 131 268 41 82 48 64 128 256), losses := [] }

theorem u11032 : Upper (D 6) (R 6) [6,129,264,33,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11032
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11033 : Route 9 := (fun mask => (mask,id))

def c11033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11033 : Upper (D 6) (R 6) [6,129,264,33,66,64] 13 := by
  apply FastRouting.sound _ _ [6,129,264,33,66,64] 13 (by decide) (choices 1) [4,16,32] r11033 c11033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1545
  · exact u1546
  · exact u1547

def b11034 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 268 41 84 34 112 240 368), lower := (rows 7 131 268 41 84 34 64 128 256), losses := [] }

theorem u11034 : Upper (D 6) (R 6) [6,129,264,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11034
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11035 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 112, targets := 1 },{ cop := 3, region := 194, targets := 4 }], pairs := [(1,2),(4,0)], upper := (rows 7 131 268 41 84 48 98 226 354), lower := (rows 7 131 268 41 84 48 64 128 256), losses := [] }

theorem u11035 : Upper (D 6) (R 6) [6,129,264,33,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11035
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11036 : Route 9 := (fun mask => (mask,id))

def c11036 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11036 : Upper (D 6) (R 6) [6,129,264,33,68,64] 13 := by
  apply FastRouting.sound _ _ [6,129,264,33,68,64] 13 (by decide) (choices 1) [2,16,32] r11036 c11036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1548
  · exact u1549
  · exact u1550

def b11037 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 131 268 41 112 34 84 212 340), lower := (rows 7 131 268 41 112 34 64 128 256), losses := [] }

theorem u11037 : Upper (D 6) (R 6) [6,129,264,33,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11037
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11038 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 210, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 131 268 41 112 36 82 210 338), lower := (rows 7 131 268 41 112 36 64 128 256), losses := [] }

theorem u11038 : Upper (D 6) (R 6) [6,129,264,33,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11038
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11039 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 131 268 41 112 48 70 198 326), lower := (rows 7 131 268 41 112 48 64 128 256), losses := [] }

theorem u11039 : Upper (D 6) (R 6) [6,129,264,33,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11039
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11039
end Delivery.IrregularNine14.P06
