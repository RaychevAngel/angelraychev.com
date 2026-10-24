import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0252
import IrregularNine14P06C0253

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32580 : Route 9 := (fun mask => (mask,id))

def c32580 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32580 : Upper (D 6) (R 6) [10,96,384,5,33] 13 := by
  apply FastRouting.sound _ _ [10,96,384,5,33] 13 (by decide) (choices 1) [2,4,16,64] r32580 c32580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15169
  · exact u15170
  · exact u15171
  · exact u15172

def b32581 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 98 388 13 50 117 85 213 341), lower := (rows 11 98 388 13 50 32 64 128 256), losses := [] }

theorem u32581 : Upper (D 6) (R 6) [10,96,384,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32582 : Route 9 := (fun mask => (mask,id))

def c32582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32582 : Upper (D 6) (R 6) [10,96,384,5,36] 13 := by
  apply FastRouting.sound _ _ [10,96,384,5,36] 13 (by decide) (choices 1) [1,2,16,64] r32582 c32582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15173
  · exact u15174
  · exact u15175
  · exact u15176

def b32583 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 388 13 112 55 87 151 279), lower := (rows 11 98 388 13 112 32 64 128 256), losses := [] }

theorem u32583 : Upper (D 6) (R 6) [10,96,384,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32584 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 388 25 19 100 100 228 356), lower := (rows 11 98 388 25 19 32 64 128 256), losses := [] }

theorem u32584 : Upper (D 6) (R 6) [10,96,384,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32585 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 98 388 25 21 102 102 230 358), lower := (rows 11 98 388 25 21 32 64 128 256), losses := [] }

theorem u32585 : Upper (D 6) (R 6) [10,96,384,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32586 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 388 25 22 101 101 229 357), lower := (rows 11 98 388 25 22 32 64 128 256), losses := [] }

theorem u32586 : Upper (D 6) (R 6) [10,96,384,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32587 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 388 25 49 102 70 198 326), lower := (rows 11 98 388 25 49 32 64 128 256), losses := [] }

theorem u32587 : Upper (D 6) (R 6) [10,96,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32588 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 388 25 50 101 69 197 325), lower := (rows 11 98 388 25 50 32 64 128 256), losses := [] }

theorem u32588 : Upper (D 6) (R 6) [10,96,384,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32589 : Route 9 := (fun mask => (mask,id))

def c32589 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32589 : Upper (D 6) (R 6) [10,96,384,17,36] 13 := by
  apply FastRouting.sound _ _ [10,96,384,17,36] 13 (by decide) (choices 1) [1,2,4,64] r32589 c32589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15177
  · exact u15178
  · exact u15179
  · exact u15180

def b32590 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 388 25 112 39 71 135 263), lower := (rows 11 98 388 25 112 32 64 128 256), losses := [] }

theorem u32590 : Upper (D 6) (R 6) [10,96,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32591 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 388 28 19 101 101 229 357), lower := (rows 11 98 388 28 19 32 64 128 256), losses := [] }

theorem u32591 : Upper (D 6) (R 6) [10,96,384,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32592 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 388 28 21 99 99 227 355), lower := (rows 11 98 388 28 21 32 64 128 256), losses := [] }

theorem u32592 : Upper (D 6) (R 6) [10,96,384,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32593 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 388 28 22 97 97 225 353), lower := (rows 11 98 388 28 22 32 64 128 256), losses := [] }

theorem u32593 : Upper (D 6) (R 6) [10,96,384,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32594 : Route 9 := (fun mask => (mask,id))

def c32594 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32594 : Upper (D 6) (R 6) [10,96,384,20,33] 13 := by
  apply FastRouting.sound _ _ [10,96,384,20,33] 13 (by decide) (choices 1) [1,2,4,64] r32594 c32594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15181
  · exact u15182
  · exact u15183
  · exact u15184

def b32595 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 98 388 28 50 101 69 197 325), lower := (rows 11 98 388 28 50 32 64 128 256), losses := [] }

theorem u32595 : Upper (D 6) (R 6) [10,96,384,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32596 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 388 28 52 99 67 195 323), lower := (rows 11 98 388 28 52 32 64 128 256), losses := [] }

theorem u32596 : Upper (D 6) (R 6) [10,96,384,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32597 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 388 28 112 39 71 135 263), lower := (rows 11 98 388 28 112 32 64 128 256), losses := [] }

theorem u32597 : Upper (D 6) (R 6) [10,96,384,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32598 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 98 388 44 19 117 85 213 341), lower := (rows 11 98 388 44 19 32 64 128 256), losses := [] }

theorem u32598 : Upper (D 6) (R 6) [10,96,384,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32599 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 98 388 44 21 115 83 211 339), lower := (rows 11 98 388 44 21 32 64 128 256), losses := [] }

theorem u32599 : Upper (D 6) (R 6) [10,96,384,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32600 : Route 9 := (fun mask => (mask,id))

def c32600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32600 : Upper (D 6) (R 6) [10,96,384,36,6] 13 := by
  apply FastRouting.sound _ _ [10,96,384,36,6] 13 (by decide) (choices 1) [1,16,64] r32600 c32600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15185
  · exact u15186
  · exact u15187

def r32601 : Route 9 := (fun mask => (mask,id))

def c32601 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32601 : Upper (D 6) (R 6) [10,96,384,36,65] 13 := by
  apply FastRouting.sound _ _ [10,96,384,36,65] 13 (by decide) (choices 1) [1,2,4,16] r32601 c32601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15188
  · exact u15189
  · exact u15190
  · exact u15191

def b32602 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 388 44 82 53 85 149 277), lower := (rows 11 98 388 44 82 32 64 128 256), losses := [] }

theorem u32602 : Upper (D 6) (R 6) [10,96,384,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32603 : Route 9 := (fun mask => (mask,id))

def c32603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32603 : Upper (D 6) (R 6) [10,96,384,36,68] 13 := by
  apply FastRouting.sound _ _ [10,96,384,36,68] 13 (by decide) (choices 1) [1,2,16] r32603 c32603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15192
  · exact u15193
  · exact u15194

def b32604 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 388 56 19 101 69 197 325), lower := (rows 11 98 388 56 19 32 64 128 256), losses := [] }

theorem u32604 : Upper (D 6) (R 6) [10,96,384,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32605 : Route 9 := (fun mask => (mask,id))

def c32605 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32605 : Upper (D 6) (R 6) [10,96,384,48,5] 13 := by
  apply FastRouting.sound _ _ [10,96,384,48,5] 13 (by decide) (choices 1) [1,2,4,64] r32605 c32605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15195
  · exact u15196
  · exact u15197
  · exact u15198

def b32606 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 98 388 56 22 101 69 197 325), lower := (rows 11 98 388 56 22 32 64 128 256), losses := [] }

theorem u32606 : Upper (D 6) (R 6) [10,96,384,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32607 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 388 56 81 39 71 135 263), lower := (rows 11 98 388 56 81 32 64 128 256), losses := [] }

theorem u32607 : Upper (D 6) (R 6) [10,96,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32608 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 388 56 82 37 69 133 261), lower := (rows 11 98 388 56 82 32 64 128 256), losses := [] }

theorem u32608 : Upper (D 6) (R 6) [10,96,384,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32609 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 388 56 84 39 71 135 263), lower := (rows 11 98 388 56 84 32 64 128 256), losses := [] }

theorem u32609 : Upper (D 6) (R 6) [10,96,384,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32610 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 20, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 131 22 44 21 352 352 480 352), lower := (rows 11 131 22 44 21 32 64 128 256), losses := [] }

theorem u32610 : Upper (D 6) (R 6) [10,129,18,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32611 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 360, targets := 3 },{ cop := 3, region := 451, targets := 32 }], pairs := [(0,5),(3,0),(3,1)], upper := (rows 11 131 22 44 49 356 324 452 324), lower := (rows 11 131 22 44 49 32 64 128 256), losses := [] }

theorem u32611 : Upper (D 6) (R 6) [10,129,18,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32612 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 22 44 52 353 321 449 321), lower := (rows 11 131 22 44 52 32 64 128 256), losses := [] }

theorem u32612 : Upper (D 6) (R 6) [10,129,18,36,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32613 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 360, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 131 22 44 81 356 356 484 356), lower := (rows 11 131 22 44 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 17 44 76 140 268), good := (rows 505 145 508 492 81 32 64 128 256) }] }

theorem u32613 : Upper (D 6) (R 6) [10,129,18,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32614 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 451, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 11 131 22 44 84 353 353 481 353), lower := (rows 11 131 22 44 84 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 35 67 131 259), good := (rows 489 481 508 60 92 32 64 128 256) }] }

theorem u32614 : Upper (D 6) (R 6) [10,129,18,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32615 : Route 9 := (fun mask => (mask,id))

def c32615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32615 : Upper (D 6) (R 6) [10,129,18,36,96] 13 := by
  apply FastRouting.sound _ _ [10,129,18,36,96] 13 (by decide) (choices 1) [1,4,64,256] r32615 c32615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15199
  · exact u15200
  · exact u15201
  · exact u15202

def b32616 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 131 22 44 273 100 100 228 356), lower := (rows 11 131 22 44 273 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 17 44 76 140 268), good := (rows 505 145 508 492 273 32 64 128 256) }] }

theorem u32616 : Upper (D 6) (R 6) [10,129,18,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32617 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 11 131 22 44 276 97 97 225 353), lower := (rows 11 131 22 44 276 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 35 67 131 259), good := (rows 489 481 508 60 284 32 64 128 256) }] }

theorem u32617 : Upper (D 6) (R 6) [10,129,18,36,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32618 : Route 9 := (fun mask => (mask,id))

def c32618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32618 : Upper (D 6) (R 6) [10,129,18,36,288] 13 := by
  apply FastRouting.sound _ _ [10,129,18,36,288] 13 (by decide) (choices 1) [1,4,64] r32618 c32618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15203
  · exact u15204
  · exact u15205

def r32619 : Route 9 := (fun mask => (mask,id))

def c32619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32619 : Upper (D 6) (R 6) [10,129,18,36,320] 13 := by
  apply FastRouting.sound _ _ [10,129,18,36,320] 13 (by decide) (choices 1) [1,4,64] r32619 c32619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15206
  · exact u15207
  · exact u15208

def b32620 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 20, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 131 22 104 21 356 356 484 356), lower := (rows 11 131 22 104 21 32 64 128 256), losses := [] }

theorem u32620 : Upper (D 6) (R 6) [10,129,18,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32621 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 360, targets := 3 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(3,0),(3,1)], upper := (rows 11 131 22 104 49 356 324 452 324), lower := (rows 11 131 22 104 49 32 64 128 256), losses := [] }

theorem u32621 : Upper (D 6) (R 6) [10,129,18,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32622 : Route 9 := (fun mask => (mask,id))

def c32622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32622 : Upper (D 6) (R 6) [10,129,18,96,36] 13 := by
  apply FastRouting.sound _ _ [10,129,18,96,36] 13 (by decide) (choices 1) [1,4,64,256] r32622 c32622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15209
  · exact u15210
  · exact u15211
  · exact u15212

def b32623 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 131 22 104 112 293 325 389 261), lower := (rows 11 131 22 104 112 32 64 128 256), losses := [] }

theorem u32623 : Upper (D 6) (R 6) [10,129,18,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32624 : Route 9 := (fun mask => (mask,id))

def c32624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32624 : Upper (D 6) (R 6) [10,129,18,96,257] 13 := by
  apply FastRouting.sound _ _ [10,129,18,96,257] 13 (by decide) (choices 1) [4,64] r32624 c32624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15213
  · exact u15214

def r32625 : Route 9 := (fun mask => (mask,id))

def c32625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32625 : Upper (D 6) (R 6) [10,129,18,96,260] 13 := by
  apply FastRouting.sound _ _ [10,129,18,96,260] 13 (by decide) (choices 1) [1,4,64] r32625 c32625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15215
  · exact u15216
  · exact u15217

def r32626 : Route 9 := (fun mask => (mask,id))

def c32626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32626 : Upper (D 6) (R 6) [10,129,18,96,288] 13 := by
  apply FastRouting.sound _ _ [10,129,18,96,288] 13 (by decide) (choices 1) [1,4,64] r32626 c32626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15218
  · exact u15219
  · exact u15220

def b32627 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 20, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 131 22 268 21 96 96 224 352), lower := (rows 11 131 22 268 21 32 64 128 256), losses := [] }

theorem u32627 : Upper (D 6) (R 6) [10,129,18,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32628 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 360, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 131 22 268 49 100 100 228 356), lower := (rows 11 131 22 268 49 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 17 44 76 140 268), good := (rows 505 145 508 492 49 32 64 128 256) }] }

theorem u32628 : Upper (D 6) (R 6) [10,129,18,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32629 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 11 131 22 268 52 97 97 225 353), lower := (rows 11 131 22 268 52 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 35 67 131 259), good := (rows 489 481 508 284 60 32 64 128 256) }] }

theorem u32629 : Upper (D 6) (R 6) [10,129,18,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32630 : Route 9 := (fun mask => (mask,id))

def c32630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32630 : Upper (D 6) (R 6) [10,129,18,260,96] 13 := by
  apply FastRouting.sound _ _ [10,129,18,260,96] 13 (by decide) (choices 1) [1,4,64] r32630 c32630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15221
  · exact u15222
  · exact u15223

def b32631 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 20, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 131 22 296 21 100 100 228 356), lower := (rows 11 131 22 296 21 32 64 128 256), losses := [] }

theorem u32631 : Upper (D 6) (R 6) [10,129,18,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32632 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 360, targets := 3 },{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(3,0),(3,1)], upper := (rows 11 131 22 296 49 100 68 196 324), lower := (rows 11 131 22 296 49 32 64 128 256), losses := [] }

theorem u32632 : Upper (D 6) (R 6) [10,129,18,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32633 : Route 9 := (fun mask => (mask,id))

def c32633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32633 : Upper (D 6) (R 6) [10,129,18,288,36] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,36] 13 (by decide) (choices 1) [1,4,64] r32633 c32633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15224
  · exact u15225
  · exact u15226

def r32634 : Route 9 := (fun mask => (mask,id))

def c32634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32634 : Upper (D 6) (R 6) [10,129,18,288,65] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,65] 13 (by decide) (choices 1) [4,64] r32634 c32634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15227
  · exact u15228

def r32635 : Route 9 := (fun mask => (mask,id))

def c32635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32635 : Upper (D 6) (R 6) [10,129,18,288,68] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,68] 13 (by decide) (choices 1) [1,4,64] r32635 c32635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15229
  · exact u15230
  · exact u15231

def r32636 : Route 9 := (fun mask => (mask,id))

def c32636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32636 : Upper (D 6) (R 6) [10,129,18,288,96] 13 := by
  apply FastRouting.sound _ _ [10,129,18,288,96] 13 (by decide) (choices 1) [1,4,64] r32636 c32636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15232
  · exact u15233
  · exact u15234

def b32637 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 37 28 22 352 352 480 352), lower := (rows 11 131 37 28 22 32 64 128 256), losses := [] }

theorem u32637 : Upper (D 6) (R 6) [10,129,33,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32638 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 13, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 131 37 28 50 356 324 452 324), lower := (rows 11 131 37 28 50 32 64 128 256), losses := [] }

theorem u32638 : Upper (D 6) (R 6) [10,129,33,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32639 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 37 28 52 354 322 450 322), lower := (rows 11 131 37 28 52 32 64 128 256), losses := [] }

theorem u32639 : Upper (D 6) (R 6) [10,129,33,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u32639
end Delivery.IrregularNine14.P06
