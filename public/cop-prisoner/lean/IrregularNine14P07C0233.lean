import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0036
import IrregularNine14P07C0037

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13980 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 280 146 96 193 129 385), lower := (rows 7 98 44 280 146 96 64 128 256), losses := [] }

theorem u13980 : Upper (D 7) (R 7) [6,96,40,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13981 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 280 146 160 65 193 321), lower := (rows 7 98 44 280 146 160 64 128 256), losses := [] }

theorem u13981 : Upper (D 7) (R 7) [6,96,40,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13982 : Route 9 := (fun mask => (mask,id))

def c13982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13982 : Upper (D 7) (R 7) [6,96,40,272,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,40,272,192,1] 13 (by decide) (choices 1) [1,2,128] r13982 c13982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2194
  · exact u2195
  · exact u2196

def b13983 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 280 208 34 193 129 385), lower := (rows 7 98 44 280 208 34 64 128 256), losses := [] }

theorem u13983 : Upper (D 7) (R 7) [6,96,40,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13984 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 280 208 160 67 131 259), lower := (rows 7 98 44 280 208 160 64 128 256), losses := [] }

theorem u13984 : Upper (D 7) (R 7) [6,96,40,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13985 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 328 145 33 210 146 402), lower := (rows 7 98 44 328 145 33 64 128 256), losses := [] }

theorem u13985 : Upper (D 7) (R 7) [6,96,40,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13986 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 328 145 34 209 145 401), lower := (rows 7 98 44 328 145 34 64 128 256), losses := [] }

theorem u13986 : Upper (D 7) (R 7) [6,96,40,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13987 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 98 44 328 145 48 195 131 387), lower := (rows 7 98 44 328 145 48 64 128 256), losses := [] }

theorem u13987 : Upper (D 7) (R 7) [6,96,40,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13987 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13988 : Route 9 := (fun mask => (mask,id))

def c13988 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13988 : Upper (D 7) (R 7) [6,96,40,320,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,320,129,128] 13 (by decide) (choices 1) [1,2,16] r13988 c13988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2197
  · exact u2198
  · exact u2199

def b13989 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 328 146 33 209 145 401), lower := (rows 7 98 44 328 146 33 64 128 256), losses := [] }

theorem u13989 : Upper (D 7) (R 7) [6,96,40,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13990 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 98 44 328 146 48 193 129 385), lower := (rows 7 98 44 328 146 48 64 128 256), losses := [] }

theorem u13990 : Upper (D 7) (R 7) [6,96,40,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13990 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13991 : Route 9 := (fun mask => (mask,id))

def c13991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13991 : Upper (D 7) (R 7) [6,96,40,320,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,320,130,128] 13 (by decide) (choices 1) [1,16] r13991 c13991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2200
  · exact u2201

def r13992 : Route 9 := (fun mask => (mask,id))

def c13992 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13992 : Upper (D 7) (R 7) [6,96,40,384,65,1] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384,65,1] 13 (by decide) (choices 1) [2,16,128] r13992 c13992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2202
  · exact u2203
  · exact u2204

def b13993 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 392 81 34 209 145 401), lower := (rows 7 98 44 392 81 34 64 128 256), losses := [] }

theorem u13993 : Upper (D 7) (R 7) [6,96,40,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13994 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 392 81 48 195 131 387), lower := (rows 7 98 44 392 81 48 64 128 256), losses := [] }

theorem u13994 : Upper (D 7) (R 7) [6,96,40,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13994 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13995 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 83, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 98 44 392 81 160 83 147 275), lower := (rows 7 98 44 392 81 160 64 128 256), losses := [] }

theorem u13995 : Upper (D 7) (R 7) [6,96,40,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13996 : Route 9 := (fun mask => (mask,id))

def c13996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13996 : Upper (D 7) (R 7) [6,96,40,384,129,1] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384,129,1] 13 (by decide) (choices 1) [2,16] r13996 c13996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2205
  · exact u2206

def b13997 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 392 145 34 81 209 337), lower := (rows 7 98 44 392 145 34 64 128 256), losses := [] }

theorem u13997 : Upper (D 7) (R 7) [6,96,40,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13998 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 44 392 145 48 67 195 323), lower := (rows 7 98 44 392 145 48 64 128 256), losses := [] }

theorem u13998 : Upper (D 7) (R 7) [6,96,40,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13998 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13999 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 392 145 96 83 147 275), lower := (rows 7 98 44 392 145 96 64 128 256), losses := [] }

theorem u13999 : Upper (D 7) (R 7) [6,96,40,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14000 : Route 9 := (fun mask => (mask,id))

def c14000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14000 : Upper (D 7) (R 7) [6,96,40,384,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384,130,1] 13 (by decide) (choices 1) [1,16] r14000 c14000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2207
  · exact u2208

def b14001 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 44 392 146 48 65 193 321), lower := (rows 7 98 44 392 146 48 64 128 256), losses := [] }

theorem u14001 : Upper (D 7) (R 7) [6,96,40,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14001 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14002 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 392 146 96 81 145 273), lower := (rows 7 98 44 392 146 96 64 128 256), losses := [] }

theorem u14002 : Upper (D 7) (R 7) [6,96,40,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14003 : Route 9 := (fun mask => (mask,id))

def c14003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14003 : Upper (D 7) (R 7) [6,96,40,384,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384,192,1] 13 (by decide) (choices 1) [1,2,16] r14003 c14003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2209
  · exact u2210
  · exact u2211

def b14004 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 392 208 34 81 145 273), lower := (rows 7 98 44 392 208 34 64 128 256), losses := [] }

theorem u14004 : Upper (D 7) (R 7) [6,96,40,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14005 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 392 208 48 67 131 259), lower := (rows 7 98 44 392 208 48 64 128 256), losses := [] }

theorem u14005 : Upper (D 7) (R 7) [6,96,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14005 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14006 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 452, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(4,0)], upper := (rows 7 98 133 25 176 34 328 456 328), lower := (rows 7 98 133 25 176 34 64 128 256), losses := [] }

theorem u14006 : Upper (D 7) (R 7) [6,96,129,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14007 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 98 133 25 176 40 322 450 322), lower := (rows 7 98 133 25 176 40 64 128 256), losses := [] }

theorem u14007 : Upper (D 7) (R 7) [6,96,129,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14007 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14008 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 25 176 96 330 394 266), lower := (rows 7 98 133 25 176 96 64 128 256), losses := [] }

theorem u14008 : Upper (D 7) (R 7) [6,96,129,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14009 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 98 133 25 176 288 74 202 330), lower := (rows 7 98 133 25 176 288 64 128 256), losses := [] }

theorem u14009 : Upper (D 7) (R 7) [6,96,129,17,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14009 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14010 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 98 133 25 274 40 224 224 480), lower := (rows 7 98 133 25 274 40 64 128 256), losses := [] }

theorem u14010 : Upper (D 7) (R 7) [6,96,129,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14010 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14011 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 25 274 96 232 168 424), lower := (rows 7 98 133 25 274 96 64 128 256), losses := [] }

theorem u14011 : Upper (D 7) (R 7) [6,96,129,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14012_8 : Upper (D 7) (R 7) [6,96,129,17,258,128,8] 13 :=
  permutation_upper _ _ _ [6,96,129,17,258,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2212

theorem m14012_32 : Upper (D 7) (R 7) [6,96,129,17,258,128,32] 13 :=
  permutation_upper _ _ _ [6,96,129,17,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2213

def r14012 : Route 9 := (fun mask => (mask,id))

def c14012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14012 : Upper (D 7) (R 7) [6,96,129,17,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,258,128] 13 (by decide) (choices 1) [8,32] r14012 c14012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14012_8
  · exact m14012_32

def b14013 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(4,0)], upper := (rows 7 98 133 25 280 34 224 224 480), lower := (rows 7 98 133 25 280 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 13 17 32 98 162 290), good := (rows 477 480 157 29 280 480 64 128 256) }] }

theorem u14013 : Upper (D 7) (R 7) [6,96,129,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14014 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 25 280 96 226 162 418), lower := (rows 7 98 133 25 280 96 64 128 256), losses := [] }

theorem u14014 : Upper (D 7) (R 7) [6,96,129,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14015 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,7),(4,0)], upper := (rows 7 98 133 25 280 160 98 226 354), lower := (rows 7 98 133 25 280 160 64 128 256), losses := [{ target := 7, region := (rows 1 34 4 13 17 32 98 0 290), good := (rows 351 354 29 25 280 354 64 0 256) }] }

theorem u14015 : Upper (D 7) (R 7) [6,96,129,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14016 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 196, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(4,0)], upper := (rows 7 98 133 25 304 34 200 200 456), lower := (rows 7 98 133 25 304 34 64 128 256), losses := [] }

theorem u14016 : Upper (D 7) (R 7) [6,96,129,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14017 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 133, targets := 32 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 25 304 40 194 194 450), lower := (rows 7 98 133 25 304 40 64 128 256), losses := [] }

theorem u14017 : Upper (D 7) (R 7) [6,96,129,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14017 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14018 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 25 304 96 202 138 394), lower := (rows 7 98 133 25 304 96 64 128 256), losses := [] }

theorem u14018 : Upper (D 7) (R 7) [6,96,129,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14019 : Route 9 := (fun mask => (mask,id))

def c14019 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14019 : Upper (D 7) (R 7) [6,96,129,17,288,128] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,288,128] 13 (by decide) (choices 1) [2,8] r14019 c14019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2214
  · exact u2215

def r14020 : Route 9 := (fun mask => (mask,id))

def c14020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14020 : Upper (D 7) (R 7) [6,96,129,17,384,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,384,2] 13 (by decide) (choices 1) [8,32] r14020 c14020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2216
  · exact u2217

def b14021 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 98 133 25 400 40 98 226 354), lower := (rows 7 98 133 25 400 40 64 128 256), losses := [] }

theorem u14021 : Upper (D 7) (R 7) [6,96,129,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14021 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14022 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 25 400 96 106 170 298), lower := (rows 7 98 133 25 400 96 64 128 256), losses := [] }

theorem u14022 : Upper (D 7) (R 7) [6,96,129,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14023 : PairBound 9 := { available := 328, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 7 98 133 26 176 33 328 456 328), lower := (rows 7 98 133 26 176 33 64 128 256), losses := [] }

theorem u14023 : Upper (D 7) (R 7) [6,96,129,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14024 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(2,1),(2,5)], upper := (rows 7 98 133 26 176 40 321 449 321), lower := (rows 7 98 133 26 176 40 64 128 256), losses := [] }

theorem u14024 : Upper (D 7) (R 7) [6,96,129,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14024 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14025 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 26 176 96 329 393 265), lower := (rows 7 98 133 26 176 96 64 128 256), losses := [] }

theorem u14025 : Upper (D 7) (R 7) [6,96,129,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14026 : Route 9 := (fun mask => (mask,id))

def c14026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14026 : Upper (D 7) (R 7) [6,96,129,18,160,256] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,160,256] 13 (by decide) (choices 1) [1,8] r14026 c14026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2218
  · exact u2219

def b14027 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 7 98 133 26 273 40 224 224 480), lower := (rows 7 98 133 26 273 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 40 106 170 298), good := (rows 469 480 149 504 277 488 64 128 256) }] }

theorem u14027 : Upper (D 7) (R 7) [6,96,129,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14027 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14028 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 26 273 96 232 168 424), lower := (rows 7 98 133 26 273 96 64 128 256), losses := [] }

theorem u14028 : Upper (D 7) (R 7) [6,96,129,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14029_8 : Upper (D 7) (R 7) [6,96,129,18,257,128,8] 13 :=
  permutation_upper _ _ _ [6,96,129,18,257,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2220

theorem m14029_32 : Upper (D 7) (R 7) [6,96,129,18,257,128,32] 13 :=
  permutation_upper _ _ _ [6,96,129,18,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2221

def r14029 : Route 9 := (fun mask => (mask,id))

def c14029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14029 : Upper (D 7) (R 7) [6,96,129,18,257,128] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,257,128] 13 (by decide) (choices 1) [8,32] r14029 c14029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14029_8
  · exact m14029_32

def b14030 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 98 133 26 280 33 224 224 480), lower := (rows 7 98 133 26 280 33 64 128 256), losses := [] }

theorem u14030 : Upper (D 7) (R 7) [6,96,129,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14031 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 26 280 96 225 161 417), lower := (rows 7 98 133 26 280 96 64 128 256), losses := [] }

theorem u14031 : Upper (D 7) (R 7) [6,96,129,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14032_1 : Upper (D 7) (R 7) [6,96,129,18,264,128,1] 13 :=
  permutation_upper _ _ _ [6,96,129,18,264,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2222

theorem m14032_32 : Upper (D 7) (R 7) [6,96,129,18,264,128,32] 13 :=
  permutation_upper _ _ _ [6,96,129,18,264,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2223

def r14032 : Route 9 := (fun mask => (mask,id))

def c14032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14032 : Upper (D 7) (R 7) [6,96,129,18,264,128] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,264,128] 13 (by decide) (choices 1) [1,32] r14032 c14032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14032_1
  · exact m14032_32

def b14033 : PairBound 9 := { available := 200, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 98 133 26 304 33 200 200 456), lower := (rows 7 98 133 26 304 33 64 128 256), losses := [] }

theorem u14033 : Upper (D 7) (R 7) [6,96,129,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14034 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,1),(2,5)], upper := (rows 7 98 133 26 304 40 193 193 449), lower := (rows 7 98 133 26 304 40 64 128 256), losses := [] }

theorem u14034 : Upper (D 7) (R 7) [6,96,129,18,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14034 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14035 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 26 304 96 201 137 393), lower := (rows 7 98 133 26 304 96 64 128 256), losses := [] }

theorem u14035 : Upper (D 7) (R 7) [6,96,129,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14036 : Route 9 := (fun mask => (mask,id))

def c14036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14036 : Upper (D 7) (R 7) [6,96,129,18,288,128] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,288,128] 13 (by decide) (choices 1) [1,8] r14036 c14036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2224
  · exact u2225

def r14037 : Route 9 := (fun mask => (mask,id))

def c14037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14037 : Upper (D 7) (R 7) [6,96,129,18,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,384,1] 13 (by decide) (choices 1) [8,32] r14037 c14037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2226
  · exact u2227

theorem m14038_1 : Upper (D 7) (R 7) [6,96,129,18,384,8,1] 13 :=
  permutation_upper _ _ _ [6,96,129,18,384,1,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2226

def r14038 : Route 9 := (fun mask => (mask,id))

def c14038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14038 : Upper (D 7) (R 7) [6,96,129,18,384,8] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,384,8] 13 (by decide) (choices 1) [1,32] r14038 c14038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14038_1
  · exact u2228

def b14039 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 26 400 96 105 169 297), lower := (rows 7 98 133 26 400 96 64 128 256), losses := [] }

theorem u14039 : Upper (D 7) (R 7) [6,96,129,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14039
end Delivery.IrregularNine14.P07
