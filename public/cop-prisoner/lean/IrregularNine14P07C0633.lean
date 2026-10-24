import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0416
import IrregularNine14P07C0417

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37980 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37980 : Upper (D 7) (R 7) [36,192,10,17,258] 13 := by
  apply FastRouting.sound _ _ [36,192,10,17,258] 13 (by decide) (choices 1) [1,64] r37980 c37980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24972
  · exact u24973

def r37981 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37981 : Upper (D 7) (R 7) [36,192,10,17,288] 13 := by
  apply FastRouting.sound _ _ [36,192,10,17,288] 13 (by decide) (choices 1) [1,2,64] r37981 c37981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24974
  · exact u24975
  · exact u24976

def r37982 : Route 9 := (fun mask => (mask,id))

def c37982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37982 : Upper (D 7) (R 7) [36,192,10,17,320] 13 := by
  apply FastRouting.sound _ _ [36,192,10,17,320] 13 (by decide) (choices 1) [1,2,128] r37982 c37982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24977
  · exact u24978
  · exact u24979

def b37983 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 481, targets := 2 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(1,5),(3,1),(4,5)], upper := (rows 37 194 14 56 19 481 449 449 449), lower := (rows 37 194 14 56 19 32 64 128 256), losses := [] }

theorem u37983 : Upper (D 7) (R 7) [36,192,10,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37984 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(4,5)], upper := (rows 37 194 14 56 81 419 451 387 387), lower := (rows 37 194 14 56 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 27 12 8 17 0 81 145 273), good := (rows 471 194 14 478 467 0 64 128 256) }] }

theorem u37984 : Upper (D 7) (R 7) [36,192,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37985 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 14 56 82 417 449 385 385), lower := (rows 37 194 14 56 82 32 64 128 256), losses := [] }

theorem u37985 : Upper (D 7) (R 7) [36,192,10,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37986 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,5),(4,0),(4,1),(4,5)], upper := (rows 37 194 14 56 208 291 323 387 259), lower := (rows 37 194 14 56 208 32 64 128 256), losses := [] }

theorem u37986 : Upper (D 7) (R 7) [36,192,10,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37987 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37987 : Upper (D 7) (R 7) [36,192,10,48,257] 13 := by
  apply FastRouting.sound _ _ [36,192,10,48,257] 13 (by decide) (choices 1) [1,2,64] r37987 c37987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24980
  · exact u24981
  · exact u24982

def r37988 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37988 : Upper (D 7) (R 7) [36,192,10,48,258] 13 := by
  apply FastRouting.sound _ _ [36,192,10,48,258] 13 (by decide) (choices 1) [1,64] r37988 c37988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24983
  · exact u24984

def r37989 : Route 9 := (fun mask => (mask,id))

def c37989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37989 : Upper (D 7) (R 7) [36,192,10,48,320] 13 := by
  apply FastRouting.sound _ _ [36,192,10,48,320] 13 (by decide) (choices 1) [1,2,128] r37989 c37989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24985
  · exact u24986
  · exact u24987

def b37990 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 4, region := 482, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,6),(1,0),(3,1),(4,6)], upper := (rows 37 194 14 73 19 432 496 432 432), lower := (rows 37 194 14 73 19 32 64 128 256), losses := [] }

theorem u37990 : Upper (D 7) (R 7) [36,192,10,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37991 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 14 73 49 434 466 402 402), lower := (rows 37 194 14 73 49 32 64 128 256), losses := [] }

theorem u37991 : Upper (D 7) (R 7) [36,192,10,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37992 : Route 9 := (fun mask => (mask,id))

def c37992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u37992 : Upper (D 7) (R 7) [36,192,10,65,34] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,34] 13 (by decide) (choices 1) [1,16,128,256] r37992 c37992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24988
  · exact u24989
  · exact u24990
  · exact u24991

def r37993 : Route 9 := (fun mask => (mask,id))

def c37993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37993 : Upper (D 7) (R 7) [36,192,10,65,129] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,129] 13 (by decide) (choices 1) [2,16,256] r37993 c37993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24992
  · exact u24993
  · exact u24994

def b37994 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 14 73 146 305 369 433 305), lower := (rows 37 194 14 73 146 32 64 128 256), losses := [] }

theorem u37994 : Upper (D 7) (R 7) [36,192,10,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37995 : Route 9 := (fun mask => (mask,id))

def c37995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37995 : Upper (D 7) (R 7) [36,192,10,65,160] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,160] 13 (by decide) (choices 1) [1,2,16,256] r37995 c37995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24995
  · exact u24996
  · exact u24997
  · exact u24998

def r37996 : Route 9 := (fun mask => (mask,id))

def c37996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37996 : Upper (D 7) (R 7) [36,192,10,65,257] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,257] 13 (by decide) (choices 1) [2,16,128] r37996 c37996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24999
  · exact u25000
  · exact u25001

def r37997 : Route 9 := (fun mask => (mask,id))

def c37997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37997 : Upper (D 7) (R 7) [36,192,10,65,258] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,258] 13 (by decide) (choices 1) [1,16,128] r37997 c37997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25002
  · exact u25003
  · exact u25004

def r37998 : Route 9 := (fun mask => (mask,id))

def c37998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37998 : Upper (D 7) (R 7) [36,192,10,65,288] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,288] 13 (by decide) (choices 1) [1,2,16,128] r37998 c37998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25005
  · exact u25006
  · exact u25007
  · exact u25008

def r37999 : Route 9 := (fun mask => (mask,id))

def c37999 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37999 : Upper (D 7) (R 7) [36,192,10,65,384] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,384] 13 (by decide) (choices 1) [1,2,16] r37999 c37999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25009
  · exact u25010
  · exact u25011

def b38000 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 417, targets := 2 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(0,6),(3,1),(4,6)], upper := (rows 37 194 14 88 19 417 481 417 417), lower := (rows 37 194 14 88 19 32 64 128 256), losses := [] }

theorem u38000 : Upper (D 7) (R 7) [36,192,10,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38001 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 14 88 49 419 451 387 387), lower := (rows 37 194 14 88 49 32 64 128 256), losses := [] }

theorem u38001 : Upper (D 7) (R 7) [36,192,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38002 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 450, targets := 32 },{ cop := 2, region := 417, targets := 2 }], pairs := [(0,1),(0,6),(1,5),(4,6)], upper := (rows 37 194 14 88 50 417 449 385 385), lower := (rows 37 194 14 88 50 32 64 128 256), losses := [] }

theorem u38002 : Upper (D 7) (R 7) [36,192,10,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38003 : Route 9 := (fun mask => (mask,id))

def c38003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38003 : Upper (D 7) (R 7) [36,192,10,80,129] 13 := by
  apply FastRouting.sound _ _ [36,192,10,80,129] 13 (by decide) (choices 1) [1,2,256] r38003 c38003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25012
  · exact u25013
  · exact u25014

def b38004 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 28, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 194 14 88 146 289 353 417 289), lower := (rows 37 194 14 88 146 32 64 128 256), losses := [] }

theorem u38004 : Upper (D 7) (R 7) [36,192,10,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38005 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 450, targets := 32 },{ cop := 2, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,6)], upper := (rows 37 194 14 88 176 291 323 387 259), lower := (rows 37 194 14 88 176 32 64 128 256), losses := [] }

theorem u38005 : Upper (D 7) (R 7) [36,192,10,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38006 : Route 9 := (fun mask => (mask,id))

def c38006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38006 : Upper (D 7) (R 7) [36,192,10,80,257] 13 := by
  apply FastRouting.sound _ _ [36,192,10,80,257] 13 (by decide) (choices 1) [1,2,128] r38006 c38006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25015
  · exact u25016
  · exact u25017

def r38007 : Route 9 := (fun mask => (mask,id))

def c38007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38007 : Upper (D 7) (R 7) [36,192,10,80,258] 13 := by
  apply FastRouting.sound _ _ [36,192,10,80,258] 13 (by decide) (choices 1) [1,128] r38007 c38007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25018
  · exact u25019

def r38008 : Route 9 := (fun mask => (mask,id))

def c38008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38008 : Upper (D 7) (R 7) [36,192,10,80,288] 13 := by
  apply FastRouting.sound _ _ [36,192,10,80,288] 13 (by decide) (choices 1) [1,2,128] r38008 c38008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25020
  · exact u25021
  · exact u25022

def r38009 : Route 9 := (fun mask => (mask,id))

def c38009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38009 : Upper (D 7) (R 7) [36,192,10,80,384] 13 := by
  apply FastRouting.sound _ _ [36,192,10,80,384] 13 (by decide) (choices 1) [1,2] r38009 c38009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25023
  · exact u25024

def r38010 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38010 : Upper (D 7) (R 7) [36,192,10,257,3] 13 := by
  apply FastRouting.sound _ _ [36,192,10,257,3] 13 (by decide) (choices 1) [16,64] r38010 c38010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25025
  · exact u25026

def b38011 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 14 265 49 242 210 210 466), lower := (rows 37 194 14 265 49 32 64 128 256), losses := [] }

theorem u38011 : Upper (D 7) (R 7) [36,192,10,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38012 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38012 : Upper (D 7) (R 7) [36,192,10,257,34] 13 := by
  apply FastRouting.sound _ _ [36,192,10,257,34] 13 (by decide) (choices 1) [1,16,64] r38012 c38012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25027
  · exact u25028
  · exact u25029

def r38013 : Route 9 := (fun mask => (mask,id))

def c38013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38013 : Upper (D 7) (R 7) [36,192,10,257,65] 13 := by
  apply FastRouting.sound _ _ [36,192,10,257,65] 13 (by decide) (choices 1) [2,16,128] r38013 c38013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25030
  · exact u25031
  · exact u25032

def b38014 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 14 265 82 177 241 177 433), lower := (rows 37 194 14 265 82 32 64 128 256), losses := [] }

theorem u38014 : Upper (D 7) (R 7) [36,192,10,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38015 : Route 9 := (fun mask => (mask,id))

def c38015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38015 : Upper (D 7) (R 7) [36,192,10,257,96] 13 := by
  apply FastRouting.sound _ _ [36,192,10,257,96] 13 (by decide) (choices 1) [1,2,16,128] r38015 c38015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25033
  · exact u25034
  · exact u25035
  · exact u25036

def b38016 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 14 265 208 51 115 179 307), lower := (rows 37 194 14 265 208 32 64 128 256), losses := [] }

theorem u38016 : Upper (D 7) (R 7) [36,192,10,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38017 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38017 : Upper (D 7) (R 7) [36,192,10,272,3] 13 := by
  apply FastRouting.sound _ _ [36,192,10,272,3] 13 (by decide) (choices 1) [1,64] r38017 c38017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25037
  · exact u25038

def b38018 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 14 280 49 227 195 195 451), lower := (rows 37 194 14 280 49 32 64 128 256), losses := [] }

theorem u38018 : Upper (D 7) (R 7) [36,192,10,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38019 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38019 : Upper (D 7) (R 7) [36,192,10,272,34] 13 := by
  apply FastRouting.sound _ _ [36,192,10,272,34] 13 (by decide) (choices 1) [1,64] r38019 c38019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25039
  · exact u25040

def r38020 : Route 9 := (fun mask => (mask,id))

def c38020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38020 : Upper (D 7) (R 7) [36,192,10,272,65] 13 := by
  apply FastRouting.sound _ _ [36,192,10,272,65] 13 (by decide) (choices 1) [1,2,128] r38020 c38020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25041
  · exact u25042
  · exact u25043

def b38021 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 14 280 82 161 225 161 417), lower := (rows 37 194 14 280 82 32 64 128 256), losses := [] }

theorem u38021 : Upper (D 7) (R 7) [36,192,10,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38022 : Route 9 := (fun mask => (mask,id))

def c38022 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38022 : Upper (D 7) (R 7) [36,192,10,272,96] 13 := by
  apply FastRouting.sound _ _ [36,192,10,272,96] 13 (by decide) (choices 1) [1,2,128] r38022 c38022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25044
  · exact u25045
  · exact u25046

def b38023 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 14 280 208 35 99 163 291), lower := (rows 37 194 14 280 208 32 64 128 256), losses := [] }

theorem u38023 : Upper (D 7) (R 7) [36,192,10,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38024 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38024 : Upper (D 7) (R 7) [36,192,10,288,3] 13 := by
  apply FastRouting.sound _ _ [36,192,10,288,3] 13 (by decide) (choices 1) [1,16,64] r38024 c38024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25047
  · exact u25048
  · exact u25049

def r38025 : Route 9 := (fun mask => (mask,id))

def c38025 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38025 : Upper (D 7) (R 7) [36,192,10,288,65] 13 := by
  apply FastRouting.sound _ _ [36,192,10,288,65] 13 (by decide) (choices 1) [1,2,16,128] r38025 c38025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25050
  · exact u25051
  · exact u25052
  · exact u25053

def b38026 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 14 296 82 177 209 145 401), lower := (rows 37 194 14 296 82 32 64 128 256), losses := [] }

theorem u38026 : Upper (D 7) (R 7) [36,192,10,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38027 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,5),(4,0),(4,1),(4,5)], upper := (rows 37 194 14 296 208 51 83 147 275), lower := (rows 37 194 14 296 208 32 64 128 256), losses := [] }

theorem u38027 : Upper (D 7) (R 7) [36,192,10,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38028 : Route 9 := (fun mask => (mask,id))

def c38028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38028 : Upper (D 7) (R 7) [36,192,10,320,3] 13 := by
  apply FastRouting.sound _ _ [36,192,10,320,3] 13 (by decide) (choices 1) [1,16,128] r38028 c38028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25054
  · exact u25055
  · exact u25056

def b38029 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 14 328 49 179 211 147 403), lower := (rows 37 194 14 328 49 32 64 128 256), losses := [] }

theorem u38029 : Upper (D 7) (R 7) [36,192,10,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38030 : Route 9 := (fun mask => (mask,id))

def c38030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38030 : Upper (D 7) (R 7) [36,192,10,320,34] 13 := by
  apply FastRouting.sound _ _ [36,192,10,320,34] 13 (by decide) (choices 1) [1,16,128] r38030 c38030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25057
  · exact u25058
  · exact u25059

def r38031 : Route 9 := (fun mask => (mask,id))

def c38031 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38031 : Upper (D 7) (R 7) [36,192,10,320,129] 13 := by
  apply FastRouting.sound _ _ [36,192,10,320,129] 13 (by decide) (choices 1) [1,2,16] r38031 c38031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25060
  · exact u25061
  · exact u25062

def b38032 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 14 328 146 49 113 177 305), lower := (rows 37 194 14 328 146 32 64 128 256), losses := [] }

theorem u38032 : Upper (D 7) (R 7) [36,192,10,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38033 : Route 9 := (fun mask => (mask,id))

def c38033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38033 : Upper (D 7) (R 7) [36,192,10,320,160] 13 := by
  apply FastRouting.sound _ _ [36,192,10,320,160] 13 (by decide) (choices 1) [1,2,16] r38033 c38033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25063
  · exact u25064
  · exact u25065

def b38034 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 20, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(4,5)], upper := (rows 37 194 28 11 19 480 480 480 480), lower := (rows 37 194 28 11 19 32 64 128 256), losses := [] }

theorem u38034 : Upper (D 7) (R 7) [36,192,24,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38035 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 28 11 49 482 450 450 450), lower := (rows 37 194 28 11 49 32 64 128 256), losses := [] }

theorem u38035 : Upper (D 7) (R 7) [36,192,24,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38036 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 28 11 50 481 449 449 449), lower := (rows 37 194 28 11 50 32 64 128 256), losses := [] }

theorem u38036 : Upper (D 7) (R 7) [36,192,24,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38037 : Route 9 := (fun mask => (mask,id))

def c38037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u38037 : Upper (D 7) (R 7) [36,192,24,3,65] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,65] 13 (by decide) (choices 1) [2,128,256] r38037 c38037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25066
  · exact u25067
  · exact u25068

def b38038 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 28 11 82 417 481 417 417), lower := (rows 37 194 28 11 82 32 64 128 256), losses := [] }

theorem u38038 : Upper (D 7) (R 7) [36,192,24,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38039 : Route 9 := (fun mask => (mask,id))

def c38039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u38039 : Upper (D 7) (R 7) [36,192,24,3,96] 13 := by
  apply FastRouting.sound _ _ [36,192,24,3,96] 13 (by decide) (choices 1) [1,2,128,256] r38039 c38039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25069
  · exact u25070
  · exact u25071
  · exact u25072

#print axioms u38039
end Delivery.IrregularNine14.P07
