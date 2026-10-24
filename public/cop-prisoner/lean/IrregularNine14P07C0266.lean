import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0057

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r15960 : Route 9 := (fun mask => (mask,id))

def c15960 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15960 : Upper (D 7) (R 7) [12,33,80,192,384,2] 13 := by
  apply FastRouting.sound _ _ [12,33,80,192,384,2] 13 (by decide) (choices 1) [1,2,32] r15960 c15960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3448
  · exact u3449
  · exact u3450

def b15961 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 13 35 84 265 146 34 224 224 480), lower := (rows 13 35 84 265 146 34 64 128 256), losses := [] }

theorem u15961 : Upper (D 7) (R 7) [12,33,80,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15962 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 84 265 146 96 226 162 418), lower := (rows 13 35 84 265 146 96 64 128 256), losses := [] }

theorem u15962 : Upper (D 7) (R 7) [12,33,80,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15963 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 328, targets := 128 }], pairs := [(0,7),(2,0),(3,7),(4,0)], upper := (rows 13 35 84 265 146 160 98 226 354), lower := (rows 13 35 84 265 146 160 64 128 256), losses := [{ target := 7, region := (rows 21 2 20 26 16 32 66 0 258), good := (rows 13 363 93 265 351 32 64 0 256) }] }

theorem u15963 : Upper (D 7) (R 7) [12,33,80,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15964 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 13 35 84 265 176 34 194 194 450), lower := (rows 13 35 84 265 176 34 64 128 256), losses := [] }

theorem u15964 : Upper (D 7) (R 7) [12,33,80,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15965 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 84 265 176 96 194 130 386), lower := (rows 13 35 84 265 176 96 64 128 256), losses := [] }

theorem u15965 : Upper (D 7) (R 7) [12,33,80,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15966 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 84 265 176 160 66 194 322), lower := (rows 13 35 84 265 176 160 64 128 256), losses := [] }

theorem u15966 : Upper (D 7) (R 7) [12,33,80,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15967 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 2 }], pairs := [(1,6),(1,7),(2,1),(4,1)], upper := (rows 13 35 84 266 145 34 224 224 480), lower := (rows 13 35 84 266 145 34 64 128 256), losses := [] }

theorem u15967 : Upper (D 7) (R 7) [12,33,80,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15968 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 1, region := 392, targets := 1 }], pairs := [(1,7),(3,0),(3,6),(4,6)], upper := (rows 13 35 84 266 145 96 226 162 418), lower := (rows 13 35 84 266 145 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 16 100 64 0 256), good := (rows 47 35 116 266 19 96 96 0 256) }] }

theorem u15968 : Upper (D 7) (R 7) [12,33,80,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15969 : Route 9 := (fun mask => (mask,id))

def c15969 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15969 : Upper (D 7) (R 7) [12,33,80,258,129,128] 13 := by
  apply FastRouting.sound _ _ [12,33,80,258,129,128] 13 (by decide) (choices 1) [2,32] r15969 c15969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3451
  · exact u3452

def b15970 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 266 146 33 224 224 480), lower := (rows 13 35 84 266 146 33 64 128 256), losses := [] }

theorem u15970 : Upper (D 7) (R 7) [12,33,80,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15971 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(0,6),(2,1),(3,6),(4,6)], upper := (rows 13 35 84 266 146 96 225 161 417), lower := (rows 13 35 84 266 146 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 127 67 131 259), good := (rows 493 481 116 488 500 96 96 128 256) },{ target := 6, region := (rows 5 2 4 26 26 32 0 130 258), good := (rows 29 443 29 410 410 32 0 128 256) }] }

theorem u15971 : Upper (D 7) (R 7) [12,33,80,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15972 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 328, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(3,7)], upper := (rows 13 35 84 266 146 160 97 225 353), lower := (rows 13 35 84 266 146 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 187 67 131 259), good := (rows 493 481 116 488 500 160 64 160 256) },{ target := 7, region := (rows 21 2 20 26 16 32 66 0 258), good := (rows 13 363 93 330 351 32 64 0 256) }] }

theorem u15972 : Upper (D 7) (R 7) [12,33,80,258,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15973 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 266 176 33 194 194 450), lower := (rows 13 35 84 266 176 33 64 128 256), losses := [] }

theorem u15973 : Upper (D 7) (R 7) [12,33,80,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15974 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 2 }], pairs := [(1,6),(1,7),(2,1),(4,1)], upper := (rows 13 35 84 266 176 34 193 193 449), lower := (rows 13 35 84 266 176 34 64 128 256), losses := [] }

theorem u15974 : Upper (D 7) (R 7) [12,33,80,258,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15975 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,7),(3,5),(3,6),(4,6)], upper := (rows 13 35 84 266 176 96 195 131 387), lower := (rows 13 35 84 266 176 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 16 100 64 0 256), good := (rows 47 35 116 266 48 96 96 0 256) }] }

theorem u15975 : Upper (D 7) (R 7) [12,33,80,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15976 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 84 266 176 160 67 195 323), lower := (rows 13 35 84 266 176 160 64 128 256), losses := [] }

theorem u15976 : Upper (D 7) (R 7) [12,33,80,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15977 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 32 }], pairs := [(1,6),(1,7),(2,5),(4,5)], upper := (rows 13 35 84 296 145 34 194 194 450), lower := (rows 13 35 84 296 145 34 64 128 256), losses := [] }

theorem u15977 : Upper (D 7) (R 7) [12,33,80,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15978 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 84 296 145 96 194 130 386), lower := (rows 13 35 84 296 145 96 64 128 256), losses := [] }

theorem u15978 : Upper (D 7) (R 7) [12,33,80,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15979 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 328, targets := 1 },{ cop := 1, region := 328, targets := 128 }], pairs := [(2,5),(3,0),(3,7),(4,5)], upper := (rows 13 35 84 296 145 160 66 194 322), lower := (rows 13 35 84 296 145 160 64 128 256), losses := [] }

theorem u15979 : Upper (D 7) (R 7) [12,33,80,288,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15980 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 296 146 33 194 194 450), lower := (rows 13 35 84 296 146 33 64 128 256), losses := [] }

theorem u15980 : Upper (D 7) (R 7) [12,33,80,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15981 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 32 }], pairs := [(1,6),(1,7),(2,5),(4,5)], upper := (rows 13 35 84 296 146 34 193 193 449), lower := (rows 13 35 84 296 146 34 64 128 256), losses := [] }

theorem u15981 : Upper (D 7) (R 7) [12,33,80,288,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15982 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 84 296 146 96 195 131 387), lower := (rows 13 35 84 296 146 96 64 128 256), losses := [] }

theorem u15982 : Upper (D 7) (R 7) [12,33,80,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15983 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 328, targets := 128 }], pairs := [(0,7),(2,5),(3,7),(4,5)], upper := (rows 13 35 84 296 146 160 67 195 323), lower := (rows 13 35 84 296 146 160 64 128 256), losses := [{ target := 7, region := (rows 17 2 20 10 16 32 82 0 274), good := (rows 13 363 341 296 351 32 64 0 256) }] }

theorem u15983 : Upper (D 7) (R 7) [12,33,80,288,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15984 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 456, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,6)], upper := (rows 13 35 84 328 145 34 226 162 418), lower := (rows 13 35 84 328 145 34 64 128 256), losses := [] }

theorem u15984 : Upper (D 7) (R 7) [12,33,80,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15985 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 328, targets := 1 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(3,0),(3,7),(4,6)], upper := (rows 13 35 84 328 145 160 98 162 290), lower := (rows 13 35 84 328 145 160 64 128 256), losses := [] }

theorem u15985 : Upper (D 7) (R 7) [12,33,80,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15986 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 328 146 33 226 162 418), lower := (rows 13 35 84 328 146 33 64 128 256), losses := [] }

theorem u15986 : Upper (D 7) (R 7) [12,33,80,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15987 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 456, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,6)], upper := (rows 13 35 84 328 146 34 225 161 417), lower := (rows 13 35 84 328 146 34 64 128 256), losses := [] }

theorem u15987 : Upper (D 7) (R 7) [12,33,80,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15988 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 328, targets := 128 }], pairs := [(0,7),(1,6),(3,7),(4,6)], upper := (rows 13 35 84 328 146 160 99 163 291), lower := (rows 13 35 84 328 146 160 64 128 256), losses := [{ target := 7, region := (rows 21 2 20 26 16 32 66 0 258), good := (rows 13 363 93 328 351 32 64 0 256) }] }

theorem u15988 : Upper (D 7) (R 7) [12,33,80,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15989 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 328 176 33 194 130 386), lower := (rows 13 35 84 328 176 33 64 128 256), losses := [] }

theorem u15989 : Upper (D 7) (R 7) [12,33,80,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15990 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,6),(1,7),(3,5),(4,6)], upper := (rows 13 35 84 328 176 34 195 131 387), lower := (rows 13 35 84 328 176 34 64 128 256), losses := [] }

theorem u15990 : Upper (D 7) (R 7) [12,33,80,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15991 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 84 328 176 160 67 131 259), lower := (rows 13 35 84 328 176 160 64 128 256), losses := [] }

theorem u15991 : Upper (D 7) (R 7) [12,33,80,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15992 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 102, targets := 128 },{ cop := 0, region := 34, targets := 64 },{ cop := 1, region := 456, targets := 1 }], pairs := [(1,6),(1,7),(2,7),(3,0)], upper := (rows 13 35 84 392 145 34 98 226 354), lower := (rows 13 35 84 392 145 34 64 128 256), losses := [] }

theorem u15992 : Upper (D 7) (R 7) [12,33,80,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15993 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,7),(2,7),(3,6),(4,6)], upper := (rows 13 35 84 392 145 96 98 162 290), lower := (rows 13 35 84 392 145 96 64 128 256), losses := [] }

theorem u15993 : Upper (D 7) (R 7) [12,33,80,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15994 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 392 146 33 98 226 354), lower := (rows 13 35 84 392 146 33 64 128 256), losses := [] }

theorem u15994 : Upper (D 7) (R 7) [12,33,80,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15995 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 456, targets := 2 }], pairs := [(0,1),(1,6),(1,7),(3,1)], upper := (rows 13 35 84 392 146 34 97 225 353), lower := (rows 13 35 84 392 146 34 64 128 256), losses := [{ target := 1, region := (rows 21 0 20 58 16 32 66 130 258), good := (rows 13 489 93 392 477 488 64 128 256) }] }

theorem u15995 : Upper (D 7) (R 7) [12,33,80,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15996 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 0, region := 98, targets := 128 }], pairs := [(0,6),(1,7),(3,6),(4,6)], upper := (rows 13 35 84 392 146 96 99 163 291), lower := (rows 13 35 84 392 146 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 26 18 32 0 130 258), good := (rows 13 443 29 392 410 32 0 128 256) }] }

theorem u15996 : Upper (D 7) (R 7) [12,33,80,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15997 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 392 176 33 66 194 322), lower := (rows 13 35 84 392 176 33 64 128 256), losses := [] }

theorem u15997 : Upper (D 7) (R 7) [12,33,80,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15998 : Route 9 := (fun mask => (mask,id))

def c15998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15998 : Upper (D 7) (R 7) [12,33,80,384,160,2] 13 := by
  apply FastRouting.sound _ _ [12,33,80,384,160,2] 13 (by decide) (choices 1) [1,2] r15998 c15998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3453
  · exact u3454

def b15999 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 0, region := 98, targets := 128 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,7),(3,5),(3,6),(4,6)], upper := (rows 13 35 84 392 176 96 67 131 259), lower := (rows 13 35 84 392 176 96 64 128 256), losses := [] }

theorem u15999 : Upper (D 7) (R 7) [12,33,80,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16000 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 100 266 82 33 208 144 400), lower := (rows 13 35 100 266 82 33 64 128 256), losses := [] }

theorem u16000 : Upper (D 7) (R 7) [12,33,96,258,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16001 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 100 266 82 48 193 129 385), lower := (rows 13 35 100 266 82 48 64 128 256), losses := [] }

theorem u16001 : Upper (D 7) (R 7) [12,33,96,258,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16001 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16002 : Route 9 := (fun mask => (mask,id))

def c16002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16002 : Upper (D 7) (R 7) [12,33,96,258,66,128] 13 := by
  apply FastRouting.sound _ _ [12,33,96,258,66,128] 13 (by decide) (choices 1) [1,16,128] r16002 c16002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3455
  · exact u3456
  · exact u3457

def b16003 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 100 266 145 34 208 208 464), lower := (rows 13 35 100 266 145 34 64 128 256), losses := [] }

theorem u16003 : Upper (D 7) (R 7) [12,33,96,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16004 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 1, region := 456, targets := 32 }], pairs := [(2,0),(3,0),(3,5)], upper := (rows 13 35 100 266 145 48 194 194 450), lower := (rows 13 35 100 266 145 48 64 128 256), losses := [] }

theorem u16004 : Upper (D 7) (R 7) [12,33,96,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16004 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16005 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 35 100 266 145 96 210 146 402), lower := (rows 13 35 100 266 145 96 64 128 256), losses := [] }

theorem u16005 : Upper (D 7) (R 7) [12,33,96,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16006 : Route 9 := (fun mask => (mask,id))

def c16006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16006 : Upper (D 7) (R 7) [12,33,96,258,129,128] 13 := by
  apply FastRouting.sound _ _ [12,33,96,258,129,128] 13 (by decide) (choices 1) [2,16] r16006 c16006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3458
  · exact u3459

def b16007 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 100 266 146 33 208 208 464), lower := (rows 13 35 100 266 146 33 64 128 256), losses := [] }

theorem u16007 : Upper (D 7) (R 7) [12,33,96,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16008 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 196, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 13 35 100 266 146 48 193 193 449), lower := (rows 13 35 100 266 146 48 64 128 256), losses := [] }

theorem u16008 : Upper (D 7) (R 7) [12,33,96,258,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16008 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16009 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 35 100 266 146 96 209 145 401), lower := (rows 13 35 100 266 146 96 64 128 256), losses := [] }

theorem u16009 : Upper (D 7) (R 7) [12,33,96,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16010 : Route 9 := (fun mask => (mask,id))

def c16010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16010 : Upper (D 7) (R 7) [12,33,96,258,130,128] 13 := by
  apply FastRouting.sound _ _ [12,33,96,258,130,128] 13 (by decide) (choices 1) [1,16] r16010 c16010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3460
  · exact u3461

def b16011 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 100 266 208 33 210 146 402), lower := (rows 13 35 100 266 208 33 64 128 256), losses := [] }

theorem u16011 : Upper (D 7) (R 7) [12,33,96,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16012 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 100 266 208 34 209 145 401), lower := (rows 13 35 100 266 208 34 64 128 256), losses := [] }

theorem u16012 : Upper (D 7) (R 7) [12,33,96,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16013 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 35 100 266 208 48 195 131 387), lower := (rows 13 35 100 266 208 48 64 128 256), losses := [] }

theorem u16013 : Upper (D 7) (R 7) [12,33,96,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16013 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16014 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 13 35 100 266 208 160 83 147 275), lower := (rows 13 35 100 266 208 160 64 128 256), losses := [] }

theorem u16014 : Upper (D 7) (R 7) [12,33,96,258,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16015 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(1,7),(3,5),(4,5)], upper := (rows 13 35 100 280 145 34 194 194 450), lower := (rows 13 35 100 280 145 34 64 128 256), losses := [] }

theorem u16015 : Upper (D 7) (R 7) [12,33,96,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16016 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 35 100 280 145 96 194 130 386), lower := (rows 13 35 100 280 145 96 64 128 256), losses := [] }

theorem u16016 : Upper (D 7) (R 7) [12,33,96,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16017 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 68, targets := 1 },{ cop := 1, region := 68, targets := 128 }], pairs := [(2,0),(2,7),(3,5),(4,5)], upper := (rows 13 35 100 280 145 160 66 194 322), lower := (rows 13 35 100 280 145 160 64 128 256), losses := [] }

theorem u16017 : Upper (D 7) (R 7) [12,33,96,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16018 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 100 280 146 33 194 194 450), lower := (rows 13 35 100 280 146 33 64 128 256), losses := [] }

theorem u16018 : Upper (D 7) (R 7) [12,33,96,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16019 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(1,7),(3,5),(4,5)], upper := (rows 13 35 100 280 146 34 193 193 449), lower := (rows 13 35 100 280 146 34 64 128 256), losses := [] }

theorem u16019 : Upper (D 7) (R 7) [12,33,96,272,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16019
end Delivery.IrregularNine14.P07
