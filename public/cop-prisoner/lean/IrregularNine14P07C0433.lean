import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0153
import IrregularNine14P07C0154

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25980 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 205, targets := 2 },{ cop := 1, region := 48, targets := 64 }], pairs := [(0,1),(2,1),(3,1),(4,6)], upper := (rows 37 259 76 137 50 34 208 208 464), lower := (rows 37 259 76 137 50 34 64 128 256), losses := [] }

theorem u25980 : Upper (D 7) (R 7) [36,257,72,129,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25981 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 76 137 50 48 194 194 450), lower := (rows 37 259 76 137 50 48 64 128 256), losses := [] }

theorem u25981 : Upper (D 7) (R 7) [36,257,72,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25981 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25982 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 137 50 96 210 146 402), lower := (rows 37 259 76 137 50 96 64 128 256), losses := [] }

theorem u25982 : Upper (D 7) (R 7) [36,257,72,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25983 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,1),(1,7),(4,0),(4,7)], upper := (rows 37 259 76 137 50 160 82 210 338), lower := (rows 37 259 76 137 50 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 257 109 169 48 160 64 160 256) }] }

theorem u25983 : Upper (D 7) (R 7) [36,257,72,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25984 : Route 9 := (fun mask => (mask,id))

def c25984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u25984 : Upper (D 7) (R 7) [36,257,72,129,66,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,66,2] 13 (by decide) (choices 1) [16,32,128] r25984 c25984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9208
  · exact u9209
  · exact u9210

def b25985 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 240, targets := 1 }], pairs := [(1,6),(3,6),(4,0)], upper := (rows 37 259 76 137 82 48 226 162 418), lower := (rows 37 259 76 137 82 48 64 128 256), losses := [] }

theorem u25985 : Upper (D 7) (R 7) [36,257,72,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25985 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25986 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,1),(1,7),(4,0),(4,7)], upper := (rows 37 259 76 137 82 160 114 178 306), lower := (rows 37 259 76 137 82 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 257 109 169 80 160 64 160 256) }] }

theorem u25986 : Upper (D 7) (R 7) [36,257,72,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25987 : Route 9 := (fun mask => (mask,id))

def c25987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25987 : Upper (D 7) (R 7) [36,257,72,129,96,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,96,2] 13 (by decide) (choices 1) [2,16,128] r25987 c25987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9211
  · exact u9212
  · exact u9213

def b25988 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 259 76 137 112 48 194 130 386), lower := (rows 37 259 76 137 112 48 64 128 256), losses := [] }

theorem u25988 : Upper (D 7) (R 7) [36,257,72,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25988 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25989 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,1),(1,7),(4,0),(4,7)], upper := (rows 37 259 76 137 112 160 82 146 274), lower := (rows 37 259 76 137 112 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 20 168 64 128 256), good := (rows 53 257 125 169 112 160 64 160 256) }] }

theorem u25989 : Upper (D 7) (R 7) [36,257,72,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25990 : Route 9 := (fun mask => (mask,id))

def c25990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25990 : Upper (D 7) (R 7) [36,257,72,129,130,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,130,2] 13 (by decide) (choices 1) [16,32] r25990 c25990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9214
  · exact u9215

def b25991 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 322, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(1,7),(2,7),(4,0)], upper := (rows 37 259 76 137 146 48 98 226 354), lower := (rows 37 259 76 137 146 48 64 128 256), losses := [{ target := 7, region := (rows 1 11 12 8 16 48 81 0 273), good := (rows 359 323 78 335 370 368 64 0 256) }] }

theorem u25991 : Upper (D 7) (R 7) [36,257,72,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25991 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25992 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 137 146 96 114 178 306), lower := (rows 37 259 76 137 146 96 64 128 256), losses := [] }

theorem u25992 : Upper (D 7) (R 7) [36,257,72,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25993 : Route 9 := (fun mask => (mask,id))

def c25993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25993 : Upper (D 7) (R 7) [36,257,72,129,160,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,160,2] 13 (by decide) (choices 1) [2,16] r25993 c25993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9216
  · exact u9217

def b25994 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 76 137 176 48 66 194 322), lower := (rows 37 259 76 137 176 48 64 128 256), losses := [] }

theorem u25994 : Upper (D 7) (R 7) [36,257,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25994 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25995 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 137 176 96 82 146 274), lower := (rows 37 259 76 137 176 96 64 128 256), losses := [] }

theorem u25995 : Upper (D 7) (R 7) [36,257,72,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25996 : Route 9 := (fun mask => (mask,id))

def c25996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25996 : Upper (D 7) (R 7) [36,257,72,129,192,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,192,2] 13 (by decide) (choices 1) [2,16,32] r25996 c25996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9218
  · exact u9219
  · exact u9220

def b25997 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 259 76 137 208 48 98 162 290), lower := (rows 37 259 76 137 208 48 64 128 256), losses := [] }

theorem u25997 : Upper (D 7) (R 7) [36,257,72,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25997 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25998 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 204, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 259 76 138 50 33 208 208 464), lower := (rows 37 259 76 138 50 33 64 128 256), losses := [] }

theorem u25998 : Upper (D 7) (R 7) [36,257,72,130,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25999 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 76 138 50 48 193 193 449), lower := (rows 37 259 76 138 50 48 64 128 256), losses := [] }

theorem u25999 : Upper (D 7) (R 7) [36,257,72,130,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25999 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26000 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 138 50 96 209 145 401), lower := (rows 37 259 76 138 50 96 64 128 256), losses := [] }

theorem u26000 : Upper (D 7) (R 7) [36,257,72,130,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26001 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 3, region := 48, targets := 65 }], pairs := [(1,7),(4,0),(4,6),(4,7)], upper := (rows 37 259 76 138 50 160 81 209 337), lower := (rows 37 259 76 138 50 160 64 128 256), losses := [] }

theorem u26001 : Upper (D 7) (R 7) [36,257,72,130,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26002 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,6),(3,6),(4,1)], upper := (rows 37 259 76 138 81 34 240 176 432), lower := (rows 37 259 76 138 81 34 64 128 256), losses := [{ target := 6, region := (rows 5 18 4 24 16 58 0 144 272), good := (rows 37 291 45 170 443 34 0 128 256) }] }

theorem u26002 : Upper (D 7) (R 7) [36,257,72,130,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26003 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 259 76 138 81 48 226 162 418), lower := (rows 37 259 76 138 81 48 64 128 256), losses := [] }

theorem u26003 : Upper (D 7) (R 7) [36,257,72,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26003 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26004 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(1,7),(3,6),(4,7)], upper := (rows 37 259 76 138 81 160 114 178 306), lower := (rows 37 259 76 138 81 160 64 128 256), losses := [] }

theorem u26004 : Upper (D 7) (R 7) [36,257,72,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26005 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 259 76 138 82 33 240 176 432), lower := (rows 37 259 76 138 82 33 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 24 16 39 0 144 272), good := (rows 37 291 45 170 442 33 0 128 256) }] }

theorem u26005 : Upper (D 7) (R 7) [36,257,72,130,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26006 : Route 9 := (fun mask => (mask,id))

def c26006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26006 : Upper (D 7) (R 7) [36,257,72,130,66,16] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,66,16] 13 (by decide) (choices 1) [1,32,128] r26006 c26006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9221
  · exact u9222
  · exact u9223

def b26007 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 259 76 138 82 160 113 177 305), lower := (rows 37 259 76 138 82 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 257 109 168 80 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 259 45 170 18 160 0 160 256) }] }

theorem u26007 : Upper (D 7) (R 7) [36,257,72,130,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26008 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 259 76 138 112 33 210 146 402), lower := (rows 37 259 76 138 112 33 64 128 256), losses := [] }

theorem u26008 : Upper (D 7) (R 7) [36,257,72,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26009 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(2,1),(4,0),(4,1)], upper := (rows 37 259 76 138 112 34 209 145 401), lower := (rows 37 259 76 138 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 42 64 128 256), good := (rows 52 290 124 170 112 34 64 128 256) },{ target := 1, region := (rows 1 0 12 8 49 32 67 131 259), good := (rows 501 465 76 460 112 496 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 42 0 128 256), good := (rows 37 291 45 170 48 34 0 128 256) }] }

theorem u26009 : Upper (D 7) (R 7) [36,257,72,130,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26010 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 259 76 138 112 48 195 131 387), lower := (rows 37 259 76 138 112 48 64 128 256), losses := [] }

theorem u26010 : Upper (D 7) (R 7) [36,257,72,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26010 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26011 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(1,7),(4,0),(4,7)], upper := (rows 37 259 76 138 112 160 83 147 275), lower := (rows 37 259 76 138 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 52 258 124 170 112 160 64 160 256) },{ target := 1, region := (rows 5 0 4 8 20 168 64 128 256), good := (rows 53 257 125 168 112 160 64 160 256) }] }

theorem u26011 : Upper (D 7) (R 7) [36,257,72,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26012 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 37 259 76 138 145 34 112 240 368), lower := (rows 37 259 76 138 145 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 42 0 128 256), good := (rows 37 291 45 170 145 34 0 128 256) },{ target := 7, region := (rows 5 18 4 8 16 58 80 0 272), good := (rows 37 291 109 42 371 34 64 0 256) }] }

theorem u26012 : Upper (D 7) (R 7) [36,257,72,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26013 : Route 9 := (fun mask => (mask,id))

def c26013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26013 : Upper (D 7) (R 7) [36,257,72,130,129,16] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,129,16] 13 (by decide) (choices 1) [2,32] r26013 c26013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9224
  · exact u9225

def b26014 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 138 145 96 114 178 306), lower := (rows 37 259 76 138 145 96 64 128 256), losses := [] }

theorem u26014 : Upper (D 7) (R 7) [36,257,72,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26015 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 259 76 138 176 33 82 210 338), lower := (rows 37 259 76 138 176 33 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 24 39 64 128 256), good := (rows 37 289 125 184 176 33 64 128 256) }] }

theorem u26015 : Upper (D 7) (R 7) [36,257,72,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26016 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,1),(4,0),(4,1),(4,6)], upper := (rows 37 259 76 138 176 34 81 209 337), lower := (rows 37 259 76 138 176 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 49 32 67 131 259), good := (rows 501 465 76 460 176 496 64 128 256) }] }

theorem u26016 : Upper (D 7) (R 7) [36,257,72,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26017 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 76 138 176 48 67 195 323), lower := (rows 37 259 76 138 176 48 64 128 256), losses := [] }

theorem u26017 : Upper (D 7) (R 7) [36,257,72,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26017 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26018 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 138 176 96 83 147 275), lower := (rows 37 259 76 138 176 96 64 128 256), losses := [] }

theorem u26018 : Upper (D 7) (R 7) [36,257,72,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26019 : Route 9 := (fun mask => (mask,id))

def c26019 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26019 : Upper (D 7) (R 7) [36,257,72,130,192,1] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,192,1] 13 (by decide) (choices 1) [2,16,32] r26019 c26019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9226
  · exact u9227
  · exact u9228

def r26020 : Route 9 := (fun mask => (mask,id))

def c26020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26020 : Upper (D 7) (R 7) [36,257,72,130,192,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,192,2] 13 (by decide) (choices 1) [1,16,32] r26020 c26020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9229
  · exact u9230
  · exact u9231

def b26021 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 37 259 76 138 208 48 99 163 291), lower := (rows 37 259 76 138 208 48 64 128 256), losses := [] }

theorem u26021 : Upper (D 7) (R 7) [36,257,72,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26021 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26022 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 204, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 259 76 152 50 33 194 194 450), lower := (rows 37 259 76 152 50 33 64 128 256), losses := [] }

theorem u26022 : Upper (D 7) (R 7) [36,257,72,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26023 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 259 76 152 50 34 193 193 449), lower := (rows 37 259 76 152 50 34 64 128 256), losses := [] }

theorem u26023 : Upper (D 7) (R 7) [36,257,72,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26024 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 152 50 96 195 131 387), lower := (rows 37 259 76 152 50 96 64 128 256), losses := [] }

theorem u26024 : Upper (D 7) (R 7) [36,257,72,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26025 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(0,1),(1,5),(1,7),(4,7)], upper := (rows 37 259 76 152 50 160 67 195 323), lower := (rows 37 259 76 152 50 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 257 109 184 48 160 64 160 256) }] }

theorem u26025 : Upper (D 7) (R 7) [36,257,72,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26026 : Route 9 := (fun mask => (mask,id))

def c26026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26026 : Upper (D 7) (R 7) [36,257,72,144,65,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,144,65,2] 13 (by decide) (choices 1) [2,32,128] r26026 c26026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9232
  · exact u9233
  · exact u9234

def b26027 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(4,7)], upper := (rows 37 259 76 152 81 160 98 162 290), lower := (rows 37 259 76 152 81 160 64 128 256), losses := [] }

theorem u26027 : Upper (D 7) (R 7) [36,257,72,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26028 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 259 76 152 82 33 226 162 418), lower := (rows 37 259 76 152 82 33 64 128 256), losses := [] }

theorem u26028 : Upper (D 7) (R 7) [36,257,72,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26029 : Route 9 := (fun mask => (mask,id))

def c26029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26029 : Upper (D 7) (R 7) [36,257,72,144,66,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,144,66,2] 13 (by decide) (choices 1) [1,32,128] r26029 c26029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9235
  · exact u9236
  · exact u9237

def b26030 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(4,7)], upper := (rows 37 259 76 152 82 160 99 163 291), lower := (rows 37 259 76 152 82 160 64 128 256), losses := [] }

theorem u26030 : Upper (D 7) (R 7) [36,257,72,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26031 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 259 76 152 112 33 194 130 386), lower := (rows 37 259 76 152 112 33 64 128 256), losses := [] }

theorem u26031 : Upper (D 7) (R 7) [36,257,72,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26032 : Route 9 := (fun mask => (mask,id))

def c26032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26032 : Upper (D 7) (R 7) [36,257,72,144,96,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,144,96,2] 13 (by decide) (choices 1) [1,2,128] r26032 c26032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9238
  · exact u9239
  · exact u9240

def b26033 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(4,7)], upper := (rows 37 259 76 152 112 160 67 131 259), lower := (rows 37 259 76 152 112 160 64 128 256), losses := [] }

theorem u26033 : Upper (D 7) (R 7) [36,257,72,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26034 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 76 168 82 33 210 146 402), lower := (rows 37 259 76 168 82 33 64 128 256), losses := [] }

theorem u26034 : Upper (D 7) (R 7) [36,257,72,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26035 : Route 9 := (fun mask => (mask,id))

def c26035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26035 : Upper (D 7) (R 7) [36,257,72,160,66,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,160,66,2] 13 (by decide) (choices 1) [1,16,128] r26035 c26035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9241
  · exact u9242
  · exact u9243

def b26036 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 37 259 76 168 82 48 195 131 387), lower := (rows 37 259 76 168 82 48 64 128 256), losses := [] }

theorem u26036 : Upper (D 7) (R 7) [36,257,72,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26036 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26037 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 259 76 168 82 160 83 147 275), lower := (rows 37 259 76 168 82 160 64 128 256), losses := [] }

theorem u26037 : Upper (D 7) (R 7) [36,257,72,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26038 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5),(4,5)], upper := (rows 37 259 76 168 145 34 82 210 338), lower := (rows 37 259 76 168 145 34 64 128 256), losses := [{ target := 5, region := (rows 1 19 12 8 19 0 115 179 307), good := (rows 471 467 76 460 467 466 64 128 256) }] }

theorem u26038 : Upper (D 7) (R 7) [36,257,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26039 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 76 168 145 48 66 194 322), lower := (rows 37 259 76 168 145 48 64 128 256), losses := [] }

theorem u26039 : Upper (D 7) (R 7) [36,257,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26039 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26039
end Delivery.IrregularNine14.P07
