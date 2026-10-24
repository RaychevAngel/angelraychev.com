import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0141

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24960 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 461, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 194 13 328 50 34 209 145 401), lower := (rows 37 194 13 328 50 34 64 128 256), losses := [] }

theorem u24960 : Upper (D 7) (R 7) [36,192,9,320,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24961 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 13 328 50 48 195 131 387), lower := (rows 37 194 13 328 50 48 64 128 256), losses := [] }

theorem u24961 : Upper (D 7) (R 7) [36,192,9,320,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24961 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24962 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 13 328 50 160 83 147 275), lower := (rows 37 194 13 328 50 160 64 128 256), losses := [] }

theorem u24962 : Upper (D 7) (R 7) [36,192,9,320,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24963 : Route 9 := (fun mask => (mask,id))

def c24963 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24963 : Upper (D 7) (R 7) [36,192,9,320,129,2] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,129,2] 13 (by decide) (choices 1) [2,16,32] r24963 c24963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8487
  · exact u8488
  · exact u8489

def r24964 : Route 9 := (fun mask => (mask,id))

def c24964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24964 : Upper (D 7) (R 7) [36,192,9,320,129,16] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,129,16] 13 (by decide) (choices 1) [2,32] r24964 c24964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8490
  · exact u8491

def b24965 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 13 328 176 33 82 146 274), lower := (rows 37 194 13 328 176 33 64 128 256), losses := [] }

theorem u24965 : Upper (D 7) (R 7) [36,192,9,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24966 : Route 9 := (fun mask => (mask,id))

def c24966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24966 : Upper (D 7) (R 7) [36,192,9,320,160,2] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,160,2] 13 (by decide) (choices 1) [1,2,16] r24966 c24966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8492
  · exact u8493
  · exact u8494

def b24967 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 13 328 176 48 67 131 259), lower := (rows 37 194 13 328 176 48 64 128 256), losses := [] }

theorem u24967 : Upper (D 7) (R 7) [36,192,9,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24967 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24968 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 14 25 112 33 450 386 386), lower := (rows 37 194 14 25 112 33 64 128 256), losses := [] }

theorem u24968 : Upper (D 7) (R 7) [36,192,10,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24969 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 14 25 112 34 449 385 385), lower := (rows 37 194 14 25 112 34 64 128 256), losses := [] }

theorem u24969 : Upper (D 7) (R 7) [36,192,10,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24970 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 48, targets := 1 },{ cop := 1, region := 48, targets := 2 }], pairs := [(1,5),(2,5),(4,0),(4,1)], upper := (rows 37 194 14 25 112 160 323 387 259), lower := (rows 37 194 14 25 112 160 64 128 256), losses := [] }

theorem u24970 : Upper (D 7) (R 7) [36,192,10,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24971 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 198, targets := 32 },{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 37 194 14 25 112 288 195 131 387), lower := (rows 37 194 14 25 112 288 64 128 256), losses := [] }

theorem u24971 : Upper (D 7) (R 7) [36,192,10,17,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24971 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24972 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 14 25 274 33 224 224 480), lower := (rows 37 194 14 25 274 33 64 128 256), losses := [] }

theorem u24972 : Upper (D 7) (R 7) [36,192,10,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24973 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 194 14 25 274 96 225 161 417), lower := (rows 37 194 14 25 274 96 64 128 256), losses := [{ target := 7, region := (rows 21 2 20 24 16 98 64 0 256), good := (rows 37 98 47 29 319 96 96 0 256) }] }

theorem u24973 : Upper (D 7) (R 7) [36,192,10,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24974 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 14 25 304 33 194 194 450), lower := (rows 37 194 14 25 304 33 64 128 256), losses := [] }

theorem u24974 : Upper (D 7) (R 7) [36,192,10,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24975 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 194 14 25 304 34 193 193 449), lower := (rows 37 194 14 25 304 34 64 128 256), losses := [] }

theorem u24975 : Upper (D 7) (R 7) [36,192,10,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24976 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(2,5)], upper := (rows 37 194 14 25 304 96 195 131 387), lower := (rows 37 194 14 25 304 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 224 45 25 304 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 16 98 64 0 256), good := (rows 37 98 47 25 304 96 96 0 256) }] }

theorem u24976 : Upper (D 7) (R 7) [36,192,10,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24977 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 37 194 14 25 336 33 226 162 418), lower := (rows 37 194 14 25 336 33 64 128 256), losses := [] }

theorem u24977 : Upper (D 7) (R 7) [36,192,10,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24978 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 194 14 25 336 34 225 161 417), lower := (rows 37 194 14 25 336 34 64 128 256), losses := [] }

theorem u24978 : Upper (D 7) (R 7) [36,192,10,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24979 : Route 9 := (fun mask => (mask,id))

def c24979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24979 : Upper (D 7) (R 7) [36,192,10,17,320,128] 13 := by
  apply FastRouting.sound _ _ [36,192,10,17,320,128] 13 (by decide) (choices 1) [1,2,32] r24979 c24979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8495
  · exact u8496
  · exact u8497

def b24980 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 14 56 273 33 194 194 450), lower := (rows 37 194 14 56 273 33 64 128 256), losses := [] }

theorem u24980 : Upper (D 7) (R 7) [36,192,10,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24981 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 194 14 56 273 34 193 193 449), lower := (rows 37 194 14 56 273 34 64 128 256), losses := [] }

theorem u24981 : Upper (D 7) (R 7) [36,192,10,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24982 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,5),(4,5)], upper := (rows 37 194 14 56 273 96 195 131 387), lower := (rows 37 194 14 56 273 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 224 45 56 273 96 96 128 256) },{ target := 5, region := (rows 1 27 12 8 17 0 81 145 273), good := (rows 471 194 14 478 467 64 64 128 256) }] }

theorem u24982 : Upper (D 7) (R 7) [36,192,10,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24983 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 14 56 274 33 193 193 449), lower := (rows 37 194 14 56 274 33 64 128 256), losses := [] }

theorem u24983 : Upper (D 7) (R 7) [36,192,10,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24984 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(2,0),(4,5)], upper := (rows 37 194 14 56 274 96 193 129 385), lower := (rows 37 194 14 56 274 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 98 64 128 256), good := (rows 36 226 46 60 318 96 96 128 256) }] }

theorem u24984 : Upper (D 7) (R 7) [36,192,10,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24985 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(4,5)], upper := (rows 37 194 14 56 336 33 195 131 387), lower := (rows 37 194 14 56 336 33 64 128 256), losses := [] }

theorem u24985 : Upper (D 7) (R 7) [36,192,10,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24986 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 194 14 56 336 34 193 129 385), lower := (rows 37 194 14 56 336 34 64 128 256), losses := [] }

theorem u24986 : Upper (D 7) (R 7) [36,192,10,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24987 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(1,5),(4,5)], upper := (rows 37 194 14 56 336 160 67 131 259), lower := (rows 37 194 14 56 336 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 162 64 128 256), good := (rows 37 224 45 56 336 160 64 160 256) }] }

theorem u24987 : Upper (D 7) (R 7) [36,192,10,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24988 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 14 73 50 33 464 400 400), lower := (rows 37 194 14 73 50 33 64 128 256), losses := [] }

theorem u24988 : Upper (D 7) (R 7) [36,192,10,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24989 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 14 73 50 48 449 385 385), lower := (rows 37 194 14 73 50 48 64 128 256), losses := [] }

theorem u24989 : Upper (D 7) (R 7) [36,192,10,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24989 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24990 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 14 73 50 160 337 401 273), lower := (rows 37 194 14 73 50 160 64 128 256), losses := [] }

theorem u24990 : Upper (D 7) (R 7) [36,192,10,65,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24991 : Route 9 := (fun mask => (mask,id))

def c24991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24991 : Upper (D 7) (R 7) [36,192,10,65,34,256] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,34,256] 13 (by decide) (choices 1) [1,16,128] r24991 c24991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8498
  · exact u8499
  · exact u8500

def b24992 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 472, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 37 194 14 73 145 34 368 432 304), lower := (rows 37 194 14 73 145 34 64 128 256), losses := [] }

theorem u24992 : Upper (D 7) (R 7) [36,192,10,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24993 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 194 14 73 145 48 354 418 290), lower := (rows 37 194 14 73 145 48 64 128 256), losses := [] }

theorem u24993 : Upper (D 7) (R 7) [36,192,10,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24993 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24994 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 194 14 73 145 288 114 178 306), lower := (rows 37 194 14 73 145 288 64 128 256), losses := [] }

theorem u24994 : Upper (D 7) (R 7) [36,192,10,65,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24994 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24995 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 14 73 176 33 338 402 274), lower := (rows 37 194 14 73 176 33 64 128 256), losses := [] }

theorem u24995 : Upper (D 7) (R 7) [36,192,10,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24996 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 472, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 37 194 14 73 176 34 337 401 273), lower := (rows 37 194 14 73 176 34 64 128 256), losses := [] }

theorem u24996 : Upper (D 7) (R 7) [36,192,10,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24997 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 14 73 176 48 323 387 259), lower := (rows 37 194 14 73 176 48 64 128 256), losses := [] }

theorem u24997 : Upper (D 7) (R 7) [36,192,10,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24997 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24998 : Route 9 := (fun mask => (mask,id))

def c24998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24998 : Upper (D 7) (R 7) [36,192,10,65,160,256] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,160,256] 13 (by decide) (choices 1) [1,2,16] r24998 c24998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8501
  · exact u8502
  · exact u8503

def b24999 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 472, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 37 194 14 73 273 34 240 176 432), lower := (rows 37 194 14 73 273 34 64 128 256), losses := [] }

theorem u24999 : Upper (D 7) (R 7) [36,192,10,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25000 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 194 14 73 273 48 226 162 418), lower := (rows 37 194 14 73 273 48 64 128 256), losses := [] }

theorem u25000 : Upper (D 7) (R 7) [36,192,10,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25000 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25001 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,1),(0,6),(1,0),(4,6)], upper := (rows 37 194 14 73 273 160 114 178 306), lower := (rows 37 194 14 73 273 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 162 64 128 256), good := (rows 37 224 45 73 273 160 64 160 256) }] }

theorem u25001 : Upper (D 7) (R 7) [36,192,10,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25002 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 14 73 274 33 240 176 432), lower := (rows 37 194 14 73 274 33 64 128 256), losses := [] }

theorem u25002 : Upper (D 7) (R 7) [36,192,10,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25003 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 37 194 14 73 274 48 225 161 417), lower := (rows 37 194 14 73 274 48 64 128 256), losses := [] }

theorem u25003 : Upper (D 7) (R 7) [36,192,10,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25003 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25004 : Route 9 := (fun mask => (mask,id))

def c25004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25004 : Upper (D 7) (R 7) [36,192,10,65,258,128] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,258,128] 13 (by decide) (choices 1) [1,16,32] r25004 c25004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8504
  · exact u8505
  · exact u8506

def b25005 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 14 73 304 33 210 146 402), lower := (rows 37 194 14 73 304 33 64 128 256), losses := [] }

theorem u25005 : Upper (D 7) (R 7) [36,192,10,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25006 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 472, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 37 194 14 73 304 34 209 145 401), lower := (rows 37 194 14 73 304 34 64 128 256), losses := [] }

theorem u25006 : Upper (D 7) (R 7) [36,192,10,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25007 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 194 14 73 304 48 195 131 387), lower := (rows 37 194 14 73 304 48 64 128 256), losses := [] }

theorem u25007 : Upper (D 7) (R 7) [36,192,10,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25007 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25008 : Route 9 := (fun mask => (mask,id))

def c25008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25008 : Upper (D 7) (R 7) [36,192,10,65,288,128] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,288,128] 13 (by decide) (choices 1) [1,2,16] r25008 c25008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8507
  · exact u8508
  · exact u8509

def b25009 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 14 73 400 33 114 178 306), lower := (rows 37 194 14 73 400 33 64 128 256), losses := [] }

theorem u25009 : Upper (D 7) (R 7) [36,192,10,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25010 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 472, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 37 194 14 73 400 34 113 177 305), lower := (rows 37 194 14 73 400 34 64 128 256), losses := [] }

theorem u25010 : Upper (D 7) (R 7) [36,192,10,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25011 : Route 9 := (fun mask => (mask,id))

def c25011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25011 : Upper (D 7) (R 7) [36,192,10,65,384,16] 13 := by
  apply FastRouting.sound _ _ [36,192,10,65,384,16] 13 (by decide) (choices 1) [1,2,32] r25011 c25011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8510
  · exact u8511
  · exact u8512

def b25012 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 450, targets := 1 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(1,0),(4,6)], upper := (rows 37 194 14 88 145 33 354 418 290), lower := (rows 37 194 14 88 145 33 64 128 256), losses := [] }

theorem u25012 : Upper (D 7) (R 7) [36,192,10,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25013 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 194 14 88 145 34 353 417 289), lower := (rows 37 194 14 88 145 34 64 128 256), losses := [] }

theorem u25013 : Upper (D 7) (R 7) [36,192,10,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25014 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 194 14 88 145 288 99 163 291), lower := (rows 37 194 14 88 145 288 64 128 256), losses := [] }

theorem u25014 : Upper (D 7) (R 7) [36,192,10,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25014 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25015 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 194 14 88 273 33 226 162 418), lower := (rows 37 194 14 88 273 33 64 128 256), losses := [] }

theorem u25015 : Upper (D 7) (R 7) [36,192,10,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25016 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 194 14 88 273 34 225 161 417), lower := (rows 37 194 14 88 273 34 64 128 256), losses := [] }

theorem u25016 : Upper (D 7) (R 7) [36,192,10,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25017 : Route 9 := (fun mask => (mask,id))

def c25017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25017 : Upper (D 7) (R 7) [36,192,10,80,257,128] 13 := by
  apply FastRouting.sound _ _ [36,192,10,80,257,128] 13 (by decide) (choices 1) [1,2,32] r25017 c25017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8513
  · exact u8514
  · exact u8515

def b25018 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 33, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 194 14 88 274 33 225 161 417), lower := (rows 37 194 14 88 274 33 64 128 256), losses := [] }

theorem u25018 : Upper (D 7) (R 7) [36,192,10,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25019 : Route 9 := (fun mask => (mask,id))

def c25019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25019 : Upper (D 7) (R 7) [36,192,10,80,258,128] 13 := by
  apply FastRouting.sound _ _ [36,192,10,80,258,128] 13 (by decide) (choices 1) [1,32] r25019 c25019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8516
  · exact u8517

#print axioms u25019
end Delivery.IrregularNine14.P07
