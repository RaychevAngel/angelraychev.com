import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0174
import IrregularNine14P07C0175

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28200 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,0),(4,0),(4,7)], upper := (rows 97 162 13 140 82 33 338 402 274), lower := (rows 97 162 13 140 82 33 64 128 256), losses := [] }

theorem u28200 : Upper (D 7) (R 7) [96,160,9,132,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28201 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(4,7)], upper := (rows 97 162 13 140 82 34 337 401 273), lower := (rows 97 162 13 140 82 34 64 128 256), losses := [] }

theorem u28201 : Upper (D 7) (R 7) [96,160,9,132,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28202 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 140 82 48 323 387 259), lower := (rows 97 162 13 140 82 48 64 128 256), losses := [] }

theorem u28202 : Upper (D 7) (R 7) [96,160,9,132,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28202 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28203 : Route 9 := (fun mask => (mask,id))

def c28203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28203 : Upper (D 7) (R 7) [96,160,9,132,66,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,132,66,256] 13 (by decide) (choices 1) [1,2,16] r28203 c28203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10482
  · exact u10483
  · exact u10484

def b28204 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(4,7)], upper := (rows 97 162 13 140 273 34 82 210 338), lower := (rows 97 162 13 140 273 34 64 128 256), losses := [] }

theorem u28204 : Upper (D 7) (R 7) [96,160,9,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28205 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 0, region := 130, targets := 1 }], pairs := [(0,7),(1,0),(4,7)], upper := (rows 97 162 13 140 273 48 66 194 322), lower := (rows 97 162 13 140 273 48 64 128 256), losses := [] }

theorem u28205 : Upper (D 7) (R 7) [96,160,9,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28205 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28206 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 140 273 96 82 146 274), lower := (rows 97 162 13 140 273 96 64 128 256), losses := [] }

theorem u28206 : Upper (D 7) (R 7) [96,160,9,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28207 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,0),(4,0),(4,7)], upper := (rows 97 162 13 140 274 33 82 210 338), lower := (rows 97 162 13 140 274 33 64 128 256), losses := [] }

theorem u28207 : Upper (D 7) (R 7) [96,160,9,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28208 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(4,7)], upper := (rows 97 162 13 140 274 34 81 209 337), lower := (rows 97 162 13 140 274 34 64 128 256), losses := [] }

theorem u28208 : Upper (D 7) (R 7) [96,160,9,132,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28209 : Route 9 := (fun mask => (mask,id))

def c28209 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28209 : Upper (D 7) (R 7) [96,160,9,132,258,16] 13 := by
  apply FastRouting.sound _ _ [96,160,9,132,258,16] 13 (by decide) (choices 1) [1,2] r28209 c28209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10485
  · exact u10486

def b28210 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 140 274 96 83 147 275), lower := (rows 97 162 13 140 274 96 64 128 256), losses := [] }

theorem u28210 : Upper (D 7) (R 7) [96,160,9,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28211 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,0),(4,0),(4,7)], upper := (rows 97 162 13 140 336 33 82 146 274), lower := (rows 97 162 13 140 336 33 64 128 256), losses := [] }

theorem u28211 : Upper (D 7) (R 7) [96,160,9,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28212 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(4,7)], upper := (rows 97 162 13 140 336 34 83 147 275), lower := (rows 97 162 13 140 336 34 64 128 256), losses := [] }

theorem u28212 : Upper (D 7) (R 7) [96,160,9,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28213 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 140 336 48 67 131 259), lower := (rows 97 162 13 140 336 48 64 128 256), losses := [] }

theorem u28213 : Upper (D 7) (R 7) [96,160,9,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28213 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28214 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 2, region := 418, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(2,1)], upper := (rows 97 162 13 152 82 33 326 390 262), lower := (rows 97 162 13 152 82 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 125 64 128 256), good := (rows 97 160 45 189 113 33 97 128 256) }] }

theorem u28214 : Upper (D 7) (R 7) [96,160,9,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28215 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 97 162 13 152 82 34 325 389 261), lower := (rows 97 162 13 152 82 34 64 128 256), losses := [{ target := 7, region := (rows 25 2 12 8 16 50 76 0 268), good := (rows 97 34 333 381 115 34 64 0 256) }] }

theorem u28215 : Upper (D 7) (R 7) [96,160,9,144,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28216 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,7),(1,6),(4,7)], upper := (rows 97 162 13 152 82 36 323 387 259), lower := (rows 97 162 13 152 82 36 64 128 256), losses := [] }

theorem u28216 : Upper (D 7) (R 7) [96,160,9,144,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28216 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28217 : Route 9 := (fun mask => (mask,id))

def c28217 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28217 : Upper (D 7) (R 7) [96,160,9,144,66,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,66,256] 13 (by decide) (choices 1) [1,2,4] r28217 c28217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10487
  · exact u10488
  · exact u10489

def b28218 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 162 13 152 84 33 322 386 258), lower := (rows 97 162 13 152 84 33 64 128 256), losses := [] }

theorem u28218 : Upper (D 7) (R 7) [96,160,9,144,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28219 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(3,6)], upper := (rows 97 162 13 152 84 34 323 387 259), lower := (rows 97 162 13 152 84 34 64 128 256), losses := [{ target := 6, region := (rows 1 159 4 24 16 191 0 133 261), good := (rows 419 162 431 186 446 34 0 162 256) }] }

theorem u28219 : Upper (D 7) (R 7) [96,160,9,144,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28220 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 64 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 97 162 13 152 84 288 67 131 259), lower := (rows 97 162 13 152 84 288 64 128 256), losses := [{ target := 6, region := (rows 1 31 4 24 16 309 0 133 261), good := (rows 419 162 431 186 446 288 0 128 288) }] }

theorem u28220 : Upper (D 7) (R 7) [96,160,9,144,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28220 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28221 : Route 9 := (fun mask => (mask,id))

def c28221 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28221 : Upper (D 7) (R 7) [96,160,9,144,257,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,257,2] 13 (by decide) (choices 1) [2,4] r28221 c28221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10490
  · exact u10491

def b28222 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 0, region := 130, targets := 1 }], pairs := [(0,7),(1,0),(4,7)], upper := (rows 97 162 13 152 273 36 66 194 322), lower := (rows 97 162 13 152 273 36 64 128 256), losses := [] }

theorem u28222 : Upper (D 7) (R 7) [96,160,9,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28222 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28223 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 152 273 96 70 134 262), lower := (rows 97 162 13 152 273 96 64 128 256), losses := [] }

theorem u28223 : Upper (D 7) (R 7) [96,160,9,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28224 : Route 9 := (fun mask => (mask,id))

def c28224 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28224 : Upper (D 7) (R 7) [96,160,9,144,258,1] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,258,1] 13 (by decide) (choices 1) [2,4] r28224 c28224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10492
  · exact u10493

def b28225 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 97 162 13 152 274 34 69 197 325), lower := (rows 97 162 13 152 274 34 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 16 50 76 0 268), good := (rows 97 34 333 381 306 34 64 0 256) }] }

theorem u28225 : Upper (D 7) (R 7) [96,160,9,144,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28226 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 13 152 274 36 67 195 323), lower := (rows 97 162 13 152 274 36 64 128 256), losses := [{ target := 7, region := (rows 11 2 12 8 18 44 82 0 274), good := (rows 97 371 45 381 339 36 64 0 256) }] }

theorem u28226 : Upper (D 7) (R 7) [96,160,9,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28226 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28227 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 152 274 96 71 135 263), lower := (rows 97 162 13 152 274 96 64 128 256), losses := [] }

theorem u28227 : Upper (D 7) (R 7) [96,160,9,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28228 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 130, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 97 162 13 152 276 33 66 194 322), lower := (rows 97 162 13 152 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 35 4 28 20 32 103 167 295), good := (rows 482 482 478 152 476 482 64 128 256) }] }

theorem u28228 : Upper (D 7) (R 7) [96,160,9,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28229 : Route 9 := (fun mask => (mask,id))

def c28229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28229 : Upper (D 7) (R 7) [96,160,9,144,260,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,260,2] 13 (by decide) (choices 1) [1,2] r28229 c28229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10494
  · exact u10495

def b28230 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 152 276 96 67 131 259), lower := (rows 97 162 13 152 276 96 64 128 256), losses := [] }

theorem u28230 : Upper (D 7) (R 7) [96,160,9,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28231 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 2, region := 162, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(2,1)], upper := (rows 97 162 13 152 336 33 70 134 262), lower := (rows 97 162 13 152 336 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 125 64 128 256), good := (rows 97 160 45 189 369 33 97 128 256) }] }

theorem u28231 : Upper (D 7) (R 7) [96,160,9,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28232 : Route 9 := (fun mask => (mask,id))

def c28232 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28232 : Upper (D 7) (R 7) [96,160,9,144,320,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,320,2] 13 (by decide) (choices 1) [1,2,4] r28232 c28232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10496
  · exact u10497
  · exact u10498

def b28233 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,7),(1,6),(4,7)], upper := (rows 97 162 13 152 336 36 67 131 259), lower := (rows 97 162 13 152 336 36 64 128 256), losses := [] }

theorem u28233 : Upper (D 7) (R 7) [96,160,9,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28233 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28234 : Route 9 := (fun mask => (mask,id))

def c28234 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28234 : Upper (D 7) (R 7) [96,160,9,192,257,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,192,257,2] 13 (by decide) (choices 1) [2,4,16] r28234 c28234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10499
  · exact u10500
  · exact u10501

def b28235 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 200 273 36 82 146 274), lower := (rows 97 162 13 200 273 36 64 128 256), losses := [] }

theorem u28235 : Upper (D 7) (R 7) [96,160,9,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28235 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28236 : Route 9 := (fun mask => (mask,id))

def c28236 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28236 : Upper (D 7) (R 7) [96,160,9,192,257,16] 13 := by
  apply FastRouting.sound _ _ [96,160,9,192,257,16] 13 (by decide) (choices 1) [2,4] r28236 c28236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10502
  · exact u10503

def b28237 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 200 274 33 86 150 278), lower := (rows 97 162 13 200 274 33 64 128 256), losses := [] }

theorem u28237 : Upper (D 7) (R 7) [96,160,9,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28238 : Route 9 := (fun mask => (mask,id))

def c28238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28238 : Upper (D 7) (R 7) [96,160,9,192,258,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,192,258,2] 13 (by decide) (choices 1) [1,4,16] r28238 c28238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10504
  · exact u10505
  · exact u10506

def b28239 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 200 274 36 83 147 275), lower := (rows 97 162 13 200 274 36 64 128 256), losses := [] }

theorem u28239 : Upper (D 7) (R 7) [96,160,9,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28239 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28240 : Route 9 := (fun mask => (mask,id))

def c28240 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28240 : Upper (D 7) (R 7) [96,160,9,192,258,16] 13 := by
  apply FastRouting.sound _ _ [96,160,9,192,258,16] 13 (by decide) (choices 1) [1,2,4] r28240 c28240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10507
  · exact u10508
  · exact u10509

def b28241 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 162 13 200 276 33 82 146 274), lower := (rows 97 162 13 200 276 33 64 128 256), losses := [] }

theorem u28241 : Upper (D 7) (R 7) [96,160,9,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28242 : Route 9 := (fun mask => (mask,id))

def c28242 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28242 : Upper (D 7) (R 7) [96,160,9,192,260,2] 13 := by
  apply FastRouting.sound _ _ [96,160,9,192,260,2] 13 (by decide) (choices 1) [1,2,16] r28242 c28242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10510
  · exact u10511
  · exact u10512

def b28243 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,6),(4,6)], upper := (rows 97 162 13 200 276 48 67 131 259), lower := (rows 97 162 13 200 276 48 64 128 256), losses := [] }

theorem u28243 : Upper (D 7) (R 7) [96,160,9,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28243 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28244 : Route 9 := (fun mask => (mask,id))

def c28244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28244 : Upper (D 7) (R 7) [96,160,9,258,66,1] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,66,1] 13 (by decide) (choices 1) [4,16,128] r28244 c28244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10513
  · exact u10514
  · exact u10515

def r28245 : Route 9 := (fun mask => (mask,id))

def c28245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28245 : Upper (D 7) (R 7) [96,160,9,258,66,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,66,4] 13 (by decide) (choices 1) [1,16,128] r28245 c28245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10516
  · exact u10517
  · exact u10518

def b28246 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 266 82 48 197 133 389), lower := (rows 97 162 13 266 82 48 64 128 256), losses := [] }

theorem u28246 : Upper (D 7) (R 7) [96,160,9,258,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28246 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28247 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 266 82 160 85 149 277), lower := (rows 97 162 13 266 82 160 64 128 256), losses := [] }

theorem u28247 : Upper (D 7) (R 7) [96,160,9,258,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28248 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(3,6)], upper := (rows 97 162 13 266 84 33 210 146 402), lower := (rows 97 162 13 266 84 33 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 37 0 144 272), good := (rows 33 162 45 266 446 33 0 128 256) }] }

theorem u28248 : Upper (D 7) (R 7) [96,160,9,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28249 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 208, targets := 34 },{ cop := 7, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 266 84 34 209 145 401), lower := (rows 97 162 13 266 84 34 64 128 256), losses := [] }

theorem u28249 : Upper (D 7) (R 7) [96,160,9,258,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28250 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 266 84 48 195 131 387), lower := (rows 97 162 13 266 84 48 64 128 256), losses := [] }

theorem u28250 : Upper (D 7) (R 7) [96,160,9,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28250 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28251 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 266 84 160 83 147 275), lower := (rows 97 162 13 266 84 160 64 128 256), losses := [] }

theorem u28251 : Upper (D 7) (R 7) [96,160,9,258,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28252 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 266 145 34 84 212 340), lower := (rows 97 162 13 266 145 34 64 128 256), losses := [] }

theorem u28252 : Upper (D 7) (R 7) [96,160,9,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28253 : Route 9 := (fun mask => (mask,id))

def c28253 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28253 : Upper (D 7) (R 7) [96,160,9,258,129,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,129,4] 13 (by decide) (choices 1) [2,16] r28253 c28253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10519
  · exact u10520

def b28254 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 266 145 48 70 198 326), lower := (rows 97 162 13 266 145 48 64 128 256), losses := [] }

theorem u28254 : Upper (D 7) (R 7) [96,160,9,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28254 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28255 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 266 145 96 86 150 278), lower := (rows 97 162 13 266 145 96 64 128 256), losses := [] }

theorem u28255 : Upper (D 7) (R 7) [96,160,9,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28256 : Route 9 := (fun mask => (mask,id))

def c28256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28256 : Upper (D 7) (R 7) [96,160,9,258,132,1] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,132,1] 13 (by decide) (choices 1) [2,16] r28256 c28256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10521
  · exact u10522

def b28257 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 266 148 34 81 209 337), lower := (rows 97 162 13 266 148 34 64 128 256), losses := [] }

theorem u28257 : Upper (D 7) (R 7) [96,160,9,258,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28258 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 266 148 48 67 195 323), lower := (rows 97 162 13 266 148 48 64 128 256), losses := [] }

theorem u28258 : Upper (D 7) (R 7) [96,160,9,258,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28258 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28259 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 266 148 96 83 147 275), lower := (rows 97 162 13 266 148 96 64 128 256), losses := [] }

theorem u28259 : Upper (D 7) (R 7) [96,160,9,258,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28259
end Delivery.IrregularNine14.P07
