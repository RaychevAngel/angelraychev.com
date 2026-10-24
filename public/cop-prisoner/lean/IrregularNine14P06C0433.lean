import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0135

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25980 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 26 276 96 69 133 261), lower := (rows 41 98 134 26 276 96 64 128 256), losses := [] }

theorem u25980 : Upper (D 6) (R 6) [40,96,130,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25981 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 134 26 336 33 69 133 261), lower := (rows 41 98 134 26 336 33 64 128 256), losses := [] }

theorem u25981 : Upper (D 6) (R 6) [40,96,130,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25982 : Route 9 := (fun mask => (mask,id))

def c25982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25982 : Upper (D 6) (R 6) [40,96,130,18,320,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,18,320,4] 13 (by decide) (choices 1) [1,4] r25982 c25982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8105
  · exact u8106

def b25983 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 28 81 33 326 390 262), lower := (rows 41 98 134 28 81 33 64 128 256), losses := [] }

theorem u25983 : Upper (D 6) (R 6) [40,96,130,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25984 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 28 81 34 325 389 261), lower := (rows 41 98 134 28 81 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 126 64 128 256), good := (rows 41 98 162 59 115 34 98 128 256) }] }

theorem u25984 : Upper (D 6) (R 6) [40,96,130,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25985 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 134 28 81 36 323 387 259), lower := (rows 41 98 134 28 81 36 64 128 256), losses := [] }

theorem u25985 : Upper (D 6) (R 6) [40,96,130,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25986 : Route 9 := (fun mask => (mask,id))

def c25986 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25986 : Upper (D 6) (R 6) [40,96,130,20,65,256] 13 := by
  apply FastRouting.sound _ _ [40,96,130,20,65,256] 13 (by decide) (choices 1) [1,2,4] r25986 c25986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8107
  · exact u8108
  · exact u8109

def b25987 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 28 273 33 70 198 326), lower := (rows 41 98 134 28 273 33 64 128 256), losses := [] }

theorem u25987 : Upper (D 6) (R 6) [40,96,130,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25988 : PairBound 9 := { available := 69, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 28 273 34 69 197 325), lower := (rows 41 98 134 28 273 34 64 128 256), losses := [{ target := 2, region := (rows 9 66 0 8 16 102 64 128 256), good := (rows 41 98 162 57 273 34 98 128 256) }] }

theorem u25988 : Upper (D 6) (R 6) [40,96,130,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25989 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 134 28 273 36 67 195 323), lower := (rows 41 98 134 28 273 36 64 128 256), losses := [] }

theorem u25989 : Upper (D 6) (R 6) [40,96,130,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25990 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 28 273 96 71 135 263), lower := (rows 41 98 134 28 273 96 64 128 256), losses := [] }

theorem u25990 : Upper (D 6) (R 6) [40,96,130,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25991 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 33, targets := 68 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 28 274 33 69 197 325), lower := (rows 41 98 134 28 274 33 64 128 256), losses := [] }

theorem u25991 : Upper (D 6) (R 6) [40,96,130,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25992 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 134 28 274 36 65 193 321), lower := (rows 41 98 134 28 274 36 64 128 256), losses := [] }

theorem u25992 : Upper (D 6) (R 6) [40,96,130,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25993 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 28 274 96 69 133 261), lower := (rows 41 98 134 28 274 96 64 128 256), losses := [] }

theorem u25993 : Upper (D 6) (R 6) [40,96,130,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25994 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 28 336 33 71 135 263), lower := (rows 41 98 134 28 336 33 64 128 256), losses := [] }

theorem u25994 : Upper (D 6) (R 6) [40,96,130,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25995 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 28 336 34 69 133 261), lower := (rows 41 98 134 28 336 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 126 64 128 256), good := (rows 41 98 162 59 370 34 98 128 256) }] }

theorem u25995 : Upper (D 6) (R 6) [40,96,130,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25996 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 134 28 336 36 67 131 259), lower := (rows 41 98 134 28 336 36 64 128 256), losses := [] }

theorem u25996 : Upper (D 6) (R 6) [40,96,130,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25997 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 98 134 76 21 33 338 402 274), lower := (rows 41 98 134 76 21 33 64 128 256), losses := [] }

theorem u25997 : Upper (D 6) (R 6) [40,96,130,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25998 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 4, region := 328, targets := 2 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 41 98 134 76 21 34 337 401 273), lower := (rows 41 98 134 76 21 34 64 128 256), losses := [] }

theorem u25998 : Upper (D 6) (R 6) [40,96,130,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25999 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 134 76 21 48 323 387 259), lower := (rows 41 98 134 76 21 48 64 128 256), losses := [] }

theorem u25999 : Upper (D 6) (R 6) [40,96,130,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25999 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26000 : Route 9 := (fun mask => (mask,id))

def c26000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26000 : Upper (D 6) (R 6) [40,96,130,68,5,256] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68,5,256] 13 (by decide) (choices 1) [1,2,16] r26000 c26000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8110
  · exact u8111
  · exact u8112

def b26001 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 76 273 33 86 150 278), lower := (rows 41 98 134 76 273 33 64 128 256), losses := [] }

theorem u26001 : Upper (D 6) (R 6) [40,96,130,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26002 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 76 273 34 85 149 277), lower := (rows 41 98 134 76 273 34 64 128 256), losses := [] }

theorem u26002 : Upper (D 6) (R 6) [40,96,130,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26003 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 134 76 273 36 83 147 275), lower := (rows 41 98 134 76 273 36 64 128 256), losses := [] }

theorem u26003 : Upper (D 6) (R 6) [40,96,130,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26004 : Route 9 := (fun mask => (mask,id))

def c26004 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26004 : Upper (D 6) (R 6) [40,96,130,68,257,16] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68,257,16] 13 (by decide) (choices 1) [1,2,4] r26004 c26004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8113
  · exact u8114
  · exact u8115

def b26005 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 76 274 33 85 149 277), lower := (rows 41 98 134 76 274 33 64 128 256), losses := [] }

theorem u26005 : Upper (D 6) (R 6) [40,96,130,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26006 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 134 76 274 36 81 145 273), lower := (rows 41 98 134 76 274 36 64 128 256), losses := [] }

theorem u26006 : Upper (D 6) (R 6) [40,96,130,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26007 : Route 9 := (fun mask => (mask,id))

def c26007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26007 : Upper (D 6) (R 6) [40,96,130,68,258,16] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68,258,16] 13 (by decide) (choices 1) [1,4] r26007 c26007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8116
  · exact u8117

def b26008 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 76 276 33 83 147 275), lower := (rows 41 98 134 76 276 33 64 128 256), losses := [] }

theorem u26008 : Upper (D 6) (R 6) [40,96,130,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26009 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 76 276 34 81 145 273), lower := (rows 41 98 134 76 276 34 64 128 256), losses := [] }

theorem u26009 : Upper (D 6) (R 6) [40,96,130,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26010 : Route 9 := (fun mask => (mask,id))

def c26010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26010 : Upper (D 6) (R 6) [40,96,130,68,260,16] 13 := by
  apply FastRouting.sound _ _ [40,96,130,68,260,16] 13 (by decide) (choices 1) [1,2] r26010 c26010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8118
  · exact u8119

def b26011 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 41 98 134 88 21 33 326 390 262), lower := (rows 41 98 134 88 21 33 64 128 256), losses := [] }

theorem u26011 : Upper (D 6) (R 6) [40,96,130,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26012 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 4, region := 328, targets := 2 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 41 98 134 88 21 34 325 389 261), lower := (rows 41 98 134 88 21 34 64 128 256), losses := [] }

theorem u26012 : Upper (D 6) (R 6) [40,96,130,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26013 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 322, targets := 4 }], pairs := [(0,1),(1,0),(1,2)], upper := (rows 41 98 134 88 21 36 323 387 259), lower := (rows 41 98 134 88 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 52 64 128 256), good := (rows 42 98 166 122 52 36 64 128 256) },{ target := 1, region := (rows 15 0 4 10 52 52 64 128 256), good := (rows 57 121 189 121 53 53 64 128 256) }] }

theorem u26013 : Upper (D 6) (R 6) [40,96,130,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26014 : Route 9 := (fun mask => (mask,id))

def c26014 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26014 : Upper (D 6) (R 6) [40,96,130,80,5,256] 13 := by
  apply FastRouting.sound _ _ [40,96,130,80,5,256] 13 (by decide) (choices 1) [1,2,4] r26014 c26014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8120
  · exact u8121
  · exact u8122

def b26015 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 198, targets := 1 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 41 98 134 88 273 33 70 134 262), lower := (rows 41 98 134 88 273 33 64 128 256), losses := [] }

theorem u26015 : Upper (D 6) (R 6) [40,96,130,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26016 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 88 273 34 69 133 261), lower := (rows 41 98 134 88 273 34 64 128 256), losses := [] }

theorem u26016 : Upper (D 6) (R 6) [40,96,130,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26017 : Route 9 := (fun mask => (mask,id))

def c26017 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26017 : Upper (D 6) (R 6) [40,96,130,80,257,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,80,257,4] 13 (by decide) (choices 1) [1,2,4] r26017 c26017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8123
  · exact u8124
  · exact u8125

def b26018 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 88 274 33 69 133 261), lower := (rows 41 98 134 88 274 33 64 128 256), losses := [] }

theorem u26018 : Upper (D 6) (R 6) [40,96,130,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26019 : Route 9 := (fun mask => (mask,id))

def c26019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26019 : Upper (D 6) (R 6) [40,96,130,80,258,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,80,258,4] 13 (by decide) (choices 1) [1,4] r26019 c26019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8126
  · exact u8127

def b26020 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 88 276 33 71 135 263), lower := (rows 41 98 134 88 276 33 64 128 256), losses := [] }

theorem u26020 : Upper (D 6) (R 6) [40,96,130,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26021 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 134 88 276 34 69 133 261), lower := (rows 41 98 134 88 276 34 64 128 256), losses := [] }

theorem u26021 : Upper (D 6) (R 6) [40,96,130,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26022 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(0,1),(1,0),(1,2)], upper := (rows 41 98 134 88 276 36 67 131 259), lower := (rows 41 98 134 88 276 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 52 64 128 256), good := (rows 42 98 166 122 308 36 64 128 256) },{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 164 121 308 36 64 128 256) }] }

theorem u26022 : Upper (D 6) (R 6) [40,96,130,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26023 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 328, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 41 98 134 265 21 34 84 212 340), lower := (rows 41 98 134 265 21 34 64 128 256), losses := [] }

theorem u26023 : Upper (D 6) (R 6) [40,96,130,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26024 : Route 9 := (fun mask => (mask,id))

def c26024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26024 : Upper (D 6) (R 6) [40,96,130,257,5,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,257,5,4] 13 (by decide) (choices 1) [2,16] r26024 c26024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8128
  · exact u8129

def b26025 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 134 265 21 48 70 198 326), lower := (rows 41 98 134 265 21 48 64 128 256), losses := [] }

theorem u26025 : Upper (D 6) (R 6) [40,96,130,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26025 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26026 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 265 21 96 86 150 278), lower := (rows 41 98 134 265 21 96 64 128 256), losses := [] }

theorem u26026 : Upper (D 6) (R 6) [40,96,130,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26027 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 134 265 81 34 84 148 276), lower := (rows 41 98 134 265 81 34 64 128 256), losses := [] }

theorem u26027 : Upper (D 6) (R 6) [40,96,130,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26028 : Route 9 := (fun mask => (mask,id))

def c26028 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26028 : Upper (D 6) (R 6) [40,96,130,257,65,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,257,65,4] 13 (by decide) (choices 1) [2,4,16] r26028 c26028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8130
  · exact u8131
  · exact u8132

def b26029 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 265 81 48 70 134 262), lower := (rows 41 98 134 265 81 48 64 128 256), losses := [] }

theorem u26029 : Upper (D 6) (R 6) [40,96,130,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26029 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26030 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 265 84 33 86 150 278), lower := (rows 41 98 134 265 84 33 64 128 256), losses := [] }

theorem u26030 : Upper (D 6) (R 6) [40,96,130,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26031 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 41 98 134 265 84 34 85 149 277), lower := (rows 41 98 134 265 84 34 64 128 256), losses := [{ target := 6, region := (rows 17 2 4 24 16 38 0 144 272), good := (rows 41 34 166 265 445 34 0 128 256) }] }

theorem u26031 : Upper (D 6) (R 6) [40,96,130,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26032 : Route 9 := (fun mask => (mask,id))

def c26032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26032 : Upper (D 6) (R 6) [40,96,130,257,68,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,257,68,4] 13 (by decide) (choices 1) [1,2,16] r26032 c26032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8133
  · exact u8134
  · exact u8135

def b26033 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 265 84 48 71 135 263), lower := (rows 41 98 134 265 84 48 64 128 256), losses := [] }

theorem u26033 : Upper (D 6) (R 6) [40,96,130,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26033 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26034 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 266 21 33 84 212 340), lower := (rows 41 98 134 266 21 33 64 128 256), losses := [] }

theorem u26034 : Upper (D 6) (R 6) [40,96,130,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26035 : Route 9 := (fun mask => (mask,id))

def c26035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26035 : Upper (D 6) (R 6) [40,96,130,258,5,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258,5,4] 13 (by decide) (choices 1) [1,16] r26035 c26035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8136
  · exact u8137

def r26036 : Route 9 := (fun mask => (mask,id))

def c26036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26036 : Upper (D 6) (R 6) [40,96,130,258,5,16] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258,5,16] 13 (by decide) (choices 1) [1,4] r26036 c26036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8138
  · exact u8139

def b26037 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 134 266 21 96 85 149 277), lower := (rows 41 98 134 266 21 96 64 128 256), losses := [] }

theorem u26037 : Upper (D 6) (R 6) [40,96,130,258,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26038 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 134 266 81 33 84 148 276), lower := (rows 41 98 134 266 81 33 64 128 256), losses := [] }

theorem u26038 : Upper (D 6) (R 6) [40,96,130,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26039 : Route 9 := (fun mask => (mask,id))

def c26039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26039 : Upper (D 6) (R 6) [40,96,130,258,65,4] 13 := by
  apply FastRouting.sound _ _ [40,96,130,258,65,4] 13 (by decide) (choices 1) [1,4,16] r26039 c26039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8140
  · exact u8141
  · exact u8142

#print axioms u26039
end Delivery.IrregularNine14.P06
