import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0499
import IrregularNine14P07C0500
import IrregularNine14P07C0501

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40980 : Route 9 := (fun mask => (mask,id))

def c40980 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40980 : Upper (D 7) (R 7) [96,384,24,34,132] 13 := by
  apply FastRouting.sound _ _ [96,384,24,34,132] 13 (by decide) (choices 1) [1,2,64] r40980 c40980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29999
  · exact u30000
  · exact u30001

def r40981 : Route 9 := (fun mask => (mask,id))

def c40981 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40981 : Upper (D 7) (R 7) [96,384,24,34,192] 13 := by
  apply FastRouting.sound _ _ [96,384,24,34,192] 13 (by decide) (choices 1) [1,2,4] r40981 c40981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u30002
  · exact u30003
  · exact u30004

def r40982 : Route 9 := (fun mask => (mask,id))

def c40982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40982 : Upper (D 7) (R 7) [96,384,24,36,129] 13 := by
  apply FastRouting.sound _ _ [96,384,24,36,129] 13 (by decide) (choices 1) [1,2,64] r40982 c40982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u30005
  · exact u30006
  · exact u30007

def b40983 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 28 44 146 99 67 195 323), lower := (rows 97 386 28 44 146 32 64 128 256), losses := [] }

theorem u40983 : Upper (D 7) (R 7) [96,384,24,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40984 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 386, targets := 64 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(1,6),(4,5)], upper := (rows 97 386 28 44 208 35 67 131 259), lower := (rows 97 386 28 44 208 32 64 128 256), losses := [] }

theorem u40984 : Upper (D 7) (R 7) [96,384,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40985 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 28 104 145 39 71 135 263), lower := (rows 97 386 28 104 145 32 64 128 256), losses := [] }

theorem u40985 : Upper (D 7) (R 7) [96,384,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40986 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 28 104 148 35 67 131 259), lower := (rows 97 386 28 104 148 32 64 128 256), losses := [] }

theorem u40986 : Upper (D 7) (R 7) [96,384,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40987 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 386 37 74 145 62 94 158 286), lower := (rows 97 386 37 74 145 32 64 128 256), losses := [] }

theorem u40987 : Upper (D 7) (R 7) [96,384,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40988 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 386 37 74 148 59 91 155 283), lower := (rows 97 386 37 74 148 32 64 128 256), losses := [] }

theorem u40988 : Upper (D 7) (R 7) [96,384,33,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40989 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 386 37 74 152 55 87 151 279), lower := (rows 97 386 37 74 152 32 64 128 256), losses := [] }

theorem u40989 : Upper (D 7) (R 7) [96,384,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40990 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 37 76 145 58 90 154 282), lower := (rows 97 386 37 76 145 32 64 128 256), losses := [] }

theorem u40990 : Upper (D 7) (R 7) [96,384,33,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40991 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 37 76 152 51 83 147 275), lower := (rows 97 386 37 76 152 32 64 128 256), losses := [] }

theorem u40991 : Upper (D 7) (R 7) [96,384,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40992 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 386 37 88 145 46 78 142 270), lower := (rows 97 386 37 88 145 32 64 128 256), losses := [] }

theorem u40992 : Upper (D 7) (R 7) [96,384,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40993 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 386 37 88 148 43 75 139 267), lower := (rows 97 386 37 88 148 32 64 128 256), losses := [] }

theorem u40993 : Upper (D 7) (R 7) [96,384,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40994 : Route 9 := (fun mask => (mask,id))

def c40994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40994 : Upper (D 7) (R 7) [96,384,34,66,129] 13 := by
  apply FastRouting.sound _ _ [96,384,34,66,129] 13 (by decide) (choices 1) [1,4,8,16] r40994 c40994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30008
  · exact u30009
  · exact u30010
  · exact u30011

def r40995 : Route 9 := (fun mask => (mask,id))

def c40995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40995 : Upper (D 7) (R 7) [96,384,34,66,132] 13 := by
  apply FastRouting.sound _ _ [96,384,34,66,132] 13 (by decide) (choices 1) [1,8,16] r40995 c40995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u30012
  · exact u30013
  · exact u30014

def r40996 : Route 9 := (fun mask => (mask,id))

def c40996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40996 : Upper (D 7) (R 7) [96,384,34,68,129] 13 := by
  apply FastRouting.sound _ _ [96,384,34,68,129] 13 (by decide) (choices 1) [1,2,8,16] r40996 c40996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30015
  · exact u30016
  · exact u30017
  · exact u30018

def b40997 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 38 76 146 57 89 153 281), lower := (rows 97 386 38 76 146 32 64 128 256), losses := [] }

theorem u40997 : Upper (D 7) (R 7) [96,384,34,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40998 : Route 9 := (fun mask => (mask,id))

def c40998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40998 : Upper (D 7) (R 7) [96,384,34,68,136] 13 := by
  apply FastRouting.sound _ _ [96,384,34,68,136] 13 (by decide) (choices 1) [1,2,16] r40998 c40998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u30019
  · exact u30020
  · exact u30021

def r40999 : Route 9 := (fun mask => (mask,id))

def c40999 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40999 : Upper (D 7) (R 7) [96,384,34,80,129] 13 := by
  apply FastRouting.sound _ _ [96,384,34,80,129] 13 (by decide) (choices 1) [1,2,4,8] r40999 c40999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30022
  · exact u30023
  · exact u30024
  · exact u30025

def b41000 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 38 88 146 45 77 141 269), lower := (rows 97 386 38 88 146 32 64 128 256), losses := [] }

theorem u41000 : Upper (D 7) (R 7) [96,384,34,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41001 : Route 9 := (fun mask => (mask,id))

def c41001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u41001 : Upper (D 7) (R 7) [96,384,34,80,132] 13 := by
  apply FastRouting.sound _ _ [96,384,34,80,132] 13 (by decide) (choices 1) [1,2,8] r41001 c41001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u30026
  · exact u30027
  · exact u30028

def b41002 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(2,7)], upper := (rows 97 386 38 88 152 39 71 135 263), lower := (rows 97 386 38 88 152 32 64 128 256), losses := [] }

theorem u41002 : Upper (D 7) (R 7) [96,384,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41003 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 386 44 76 145 51 83 147 275), lower := (rows 97 386 44 76 145 32 64 128 256), losses := [] }

theorem u41003 : Upper (D 7) (R 7) [96,384,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41004 : Route 9 := (fun mask => (mask,id))

def c41004 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u41004 : Upper (D 7) (R 7) [96,384,40,80,129] 13 := by
  apply FastRouting.sound _ _ [96,384,40,80,129] 13 (by decide) (choices 1) [1,2,4] r41004 c41004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u30029
  · exact u30030
  · exact u30031

def b41005 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 386 44 88 146 39 71 135 263), lower := (rows 97 386 44 88 146 32 64 128 256), losses := [] }

theorem u41005 : Upper (D 7) (R 7) [96,384,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41006 : Route 9 := (fun mask => (mask,id))

def c41006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u41006 : Upper (D 7) (R 7) [96,384,40,80,132] 13 := by
  apply FastRouting.sound _ _ [96,384,40,80,132] 13 (by decide) (choices 1) [1,2] r41006 c41006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u30032
  · exact u30033

def b41007 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 7, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(1,5)], upper := (rows 7 11 7 56 496 480 480 480 480), lower := (rows 7 11 7 56 16 32 64 128 256), losses := [] }

theorem u41007 : Upper (D 7) (R 7) [6,9,3,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41008 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 7, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(1,5)], upper := (rows 7 11 7 104 496 496 496 496 496), lower := (rows 7 11 7 104 16 32 64 128 256), losses := [] }

theorem u41008 : Upper (D 7) (R 7) [6,9,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41009 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 7, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(1,5)], upper := (rows 7 11 7 280 240 224 224 224 480), lower := (rows 7 11 7 280 16 32 64 128 256), losses := [] }

theorem u41009 : Upper (D 7) (R 7) [6,9,3,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41010 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 7, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(1,5)], upper := (rows 7 11 7 296 240 240 240 240 496), lower := (rows 7 11 7 296 16 32 64 128 256), losses := [] }

theorem u41010 : Upper (D 7) (R 7) [6,9,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41011 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 11 21 42 496 480 480 480 480), lower := (rows 7 11 21 42 16 32 64 128 256), losses := [] }

theorem u41011 : Upper (D 7) (R 7) [6,9,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41012 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41012 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41012 : Upper (D 7) (R 7) [6,9,17,96] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96] 13 (by decide) (choices 2) [34,96,130,160,258,288,384] r41012 c41012
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30034
  · exact u30035
  · exact u30036
  · exact u30037
  · exact u30038
  · exact u30039
  · exact u30040

def b41013 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 11 21 266 240 224 224 224 480), lower := (rows 7 11 21 266 16 32 64 128 256), losses := [] }

theorem u41013 : Upper (D 7) (R 7) [6,9,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41014 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41014 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41014 : Upper (D 7) (R 7) [6,9,17,288] 13 := by
  apply FastRouting.sound _ _ [6,9,17,288] 13 (by decide) (choices 2) [34,66,96,192] r41014 c41014
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30041
  · exact u30042
  · exact u30043
  · exact u30044

def b41015 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 11 22 104 497 481 481 481 481), lower := (rows 7 11 22 104 16 32 64 128 256), losses := [] }

theorem u41015 : Upper (D 7) (R 7) [6,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41016 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 11 22 296 241 225 225 225 481), lower := (rows 7 11 22 296 16 32 64 128 256), losses := [] }

theorem u41016 : Upper (D 7) (R 7) [6,9,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41017 : PairBound 9 := { available := 464, camps := [{ cop := 5, region := 15, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 42 464 496 464 464 464), lower := (rows 7 11 37 42 16 32 64 128 256), losses := [] }

theorem u41017 : Upper (D 7) (R 7) [6,9,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41018 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 56 466 482 450 450 450), lower := (rows 7 11 37 56 16 32 64 128 256), losses := [] }

theorem u41018 : Upper (D 7) (R 7) [6,9,33,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41019 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 11 37 74 496 496 496 496 496), lower := (rows 7 11 37 74 16 32 64 128 256), losses := [] }

theorem u41019 : Upper (D 7) (R 7) [6,9,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41020 : Route 9 := (fun mask => (mask,id))

def c41020 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41020 : Upper (D 7) (R 7) [6,9,33,80] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41020 c41020
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30045
  · exact u30046
  · exact u30047
  · exact u30048
  · exact u30049
  · exact u30050
  · exact u30051
  · exact u30052
  · exact u30053
  · exact u30054

def b41021 : PairBound 9 := { available := 466, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 104 466 498 466 466 466), lower := (rows 7 11 37 104 16 32 64 128 256), losses := [] }

theorem u41021 : Upper (D 7) (R 7) [6,9,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41022 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41022 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41022 : Upper (D 7) (R 7) [6,9,33,192] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192] 13 (by decide) (choices 2) [34,66,96,192,258,288,320] r41022 c41022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30055
  · exact u30056
  · exact u30057
  · exact u30058
  · exact u30059
  · exact u30060
  · exact u30061

def b41023 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 11 37 266 240 240 240 240 496), lower := (rows 7 11 37 266 16 32 64 128 256), losses := [] }

theorem u41023 : Upper (D 7) (R 7) [6,9,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41024 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41024 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41024 : Upper (D 7) (R 7) [6,9,33,272] 13 := by
  apply FastRouting.sound _ _ [6,9,33,272] 13 (by decide) (choices 2) [34,66,96,192] r41024 c41024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30062
  · exact u30063
  · exact u30064
  · exact u30065

def b41025 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 296 210 242 210 210 466), lower := (rows 7 11 37 296 16 32 64 128 256), losses := [] }

theorem u41025 : Upper (D 7) (R 7) [6,9,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41026 : Route 9 := (fun mask => (mask,id))

def c41026 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41026 : Upper (D 7) (R 7) [6,9,33,320] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41026 c41026
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30066
  · exact u30067
  · exact u30068
  · exact u30069
  · exact u30070
  · exact u30071

def b41027 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 38 56 465 481 449 449 449), lower := (rows 7 11 38 56 16 32 64 128 256), losses := [] }

theorem u41027 : Upper (D 7) (R 7) [6,9,34,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41028 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 11 38 88 497 481 481 481 481), lower := (rows 7 11 38 88 16 32 64 128 256), losses := [] }

theorem u41028 : Upper (D 7) (R 7) [6,9,34,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41029 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 38 104 465 497 465 465 465), lower := (rows 7 11 38 104 16 32 64 128 256), losses := [] }

theorem u41029 : Upper (D 7) (R 7) [6,9,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41030 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 11 38 200 497 497 497 497 497), lower := (rows 7 11 38 200 16 32 64 128 256), losses := [] }

theorem u41030 : Upper (D 7) (R 7) [6,9,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41031 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 11 38 280 241 225 225 225 481), lower := (rows 7 11 38 280 16 32 64 128 256), losses := [] }

theorem u41031 : Upper (D 7) (R 7) [6,9,34,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41032 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 38 296 209 241 209 209 465), lower := (rows 7 11 38 296 16 32 64 128 256), losses := [] }

theorem u41032 : Upper (D 7) (R 7) [6,9,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41033 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 1, targets := 224 },{ cop := 0, region := 504, targets := 2 }], pairs := [(0,5),(0,6),(0,7),(3,1)], upper := (rows 7 11 38 328 241 241 241 241 497), lower := (rows 7 11 38 328 16 32 64 128 256), losses := [] }

theorem u41033 : Upper (D 7) (R 7) [6,9,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41034 : Route 9 := (fun mask => (mask,id))

def c41034 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41034 : Upper (D 7) (R 7) [6,9,48,96] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41034 c41034
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30072
  · exact u30073
  · exact u30074
  · exact u30075
  · exact u30076
  · exact u30077
  · exact u30078
  · exact u30079
  · exact u30080
  · exact u30081

def r41035 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41035 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41035 : Upper (D 7) (R 7) [6,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r41035 c41035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30082
  · exact u30083
  · exact u30084
  · exact u30085
  · exact u30086
  · exact u30087
  · exact u30088
  · exact u30089
  · exact u30090
  · exact u30091
  · exact u30092

def b41036 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 2, targets := 224 },{ cop := 0, region := 244, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(2,0)], upper := (rows 7 11 52 265 242 226 226 226 482), lower := (rows 7 11 52 265 16 32 64 128 256), losses := [] }

theorem u41036 : Upper (D 7) (R 7) [6,9,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41037 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41037 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41037 : Upper (D 7) (R 7) [6,9,48,258] 13 := by
  apply FastRouting.sound _ _ [6,9,48,258] 13 (by decide) (choices 2) [33,65,96,192] r41037 c41037
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30093
  · exact u30094
  · exact u30095
  · exact u30096

def r41038 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41038 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41038 : Upper (D 7) (R 7) [6,9,48,288] 13 := by
  apply FastRouting.sound _ _ [6,9,48,288] 13 (by decide) (choices 2) [3,65,66,192] r41038 c41038
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30097
  · exact u30098
  · exact u30099
  · exact u30100

def r41039 : Route 9 := (fun mask => (mask,id))

def c41039 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41039 : Upper (D 7) (R 7) [6,9,48,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41039 c41039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30101
  · exact u30102
  · exact u30103
  · exact u30104
  · exact u30105
  · exact u30106
  · exact u30107
  · exact u30108
  · exact u30109
  · exact u30110

#print axioms u41039
end Delivery.IrregularNine14.P07
