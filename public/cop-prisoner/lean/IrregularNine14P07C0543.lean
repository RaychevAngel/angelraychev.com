import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0265
import IrregularNine14P07C0266
import IrregularNine14P07C0267

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32580 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 21, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 35 84 200 145 290 354 418 290), lower := (rows 13 35 84 200 145 32 64 128 256), losses := [] }

theorem u32580 : Upper (D 7) (R 7) [12,33,80,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32581 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 0, region := 290, targets := 128 }], pairs := [(1,6),(1,7),(2,7),(4,6)], upper := (rows 13 35 84 200 146 291 355 419 291), lower := (rows 13 35 84 200 146 32 64 128 256), losses := [{ target := 7, region := (rows 1 3 20 8 16 35 67 0 259), good := (rows 367 355 84 72 374 32 64 0 256) }] }

theorem u32581 : Upper (D 7) (R 7) [12,33,80,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32582 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 0, region := 290, targets := 128 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,6),(1,7),(3,5),(4,6)], upper := (rows 13 35 84 200 176 291 323 387 259), lower := (rows 13 35 84 200 176 32 64 128 256), losses := [] }

theorem u32582 : Upper (D 7) (R 7) [12,33,80,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32583 : Route 9 := (fun mask => (mask,id))

def c32583 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32583 : Upper (D 7) (R 7) [12,33,80,192,257] 13 := by
  apply FastRouting.sound _ _ [12,33,80,192,257] 13 (by decide) (choices 1) [2,128] r32583 c32583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15951
  · exact u15952

def r32584 : Route 9 := (fun mask => (mask,id))

def c32584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32584 : Upper (D 7) (R 7) [12,33,80,192,258] 13 := by
  apply FastRouting.sound _ _ [12,33,80,192,258] 13 (by decide) (choices 1) [1,2,128] r32584 c32584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15953
  · exact u15954
  · exact u15955

def r32585 : Route 9 := (fun mask => (mask,id))

def c32585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32585 : Upper (D 7) (R 7) [12,33,80,192,288] 13 := by
  apply FastRouting.sound _ _ [12,33,80,192,288] 13 (by decide) (choices 1) [1,2,128] r32585 c32585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15956
  · exact u15957
  · exact u15958

def r32586 : Route 9 := (fun mask => (mask,id))

def c32586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32586 : Upper (D 7) (R 7) [12,33,80,192,384] 13 := by
  apply FastRouting.sound _ _ [12,33,80,192,384] 13 (by decide) (choices 1) [1,2] r32586 c32586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15959
  · exact u15960

def b32587 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(0,5),(2,0),(2,5),(3,5)], upper := (rows 13 35 84 265 50 226 194 194 450), lower := (rows 13 35 84 265 50 32 64 128 256), losses := [] }

theorem u32587 : Upper (D 7) (R 7) [12,33,80,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32588 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 4, region := 4, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(3,6)], upper := (rows 13 35 84 265 82 162 226 162 418), lower := (rows 13 35 84 265 82 32 64 128 256), losses := [] }

theorem u32588 : Upper (D 7) (R 7) [12,33,80,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32589 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 265 112 162 194 130 386), lower := (rows 13 35 84 265 112 32 64 128 256), losses := [] }

theorem u32589 : Upper (D 7) (R 7) [12,33,80,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32590 : Route 9 := (fun mask => (mask,id))

def c32590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32590 : Upper (D 7) (R 7) [12,33,80,257,130] 13 := by
  apply FastRouting.sound _ _ [12,33,80,257,130] 13 (by decide) (choices 1) [2,64,128] r32590 c32590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15961
  · exact u15962
  · exact u15963

def r32591 : Route 9 := (fun mask => (mask,id))

def c32591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32591 : Upper (D 7) (R 7) [12,33,80,257,160] 13 := by
  apply FastRouting.sound _ _ [12,33,80,257,160] 13 (by decide) (choices 1) [2,64,128] r32591 c32591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15964
  · exact u15965
  · exact u15966

def b32592 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 265 208 162 226 162 418), lower := (rows 13 35 84 265 208 32 64 128 256), losses := [] }

theorem u32592 : Upper (D 7) (R 7) [12,33,80,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32593 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 35 84 266 19 224 224 224 480), lower := (rows 13 35 84 266 19 32 64 128 256), losses := [] }

theorem u32593 : Upper (D 7) (R 7) [12,33,80,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32594 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 35 84 266 49 226 194 194 450), lower := (rows 13 35 84 266 49 32 64 128 256), losses := [] }

theorem u32594 : Upper (D 7) (R 7) [12,33,80,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32595 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 35 84 266 50 225 193 193 449), lower := (rows 13 35 84 266 50 32 64 128 256), losses := [] }

theorem u32595 : Upper (D 7) (R 7) [12,33,80,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32596 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 266 81 162 226 162 418), lower := (rows 13 35 84 266 81 32 64 128 256), losses := [] }

theorem u32596 : Upper (D 7) (R 7) [12,33,80,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32597 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 266 82 161 225 161 417), lower := (rows 13 35 84 266 82 32 64 128 256), losses := [] }

theorem u32597 : Upper (D 7) (R 7) [12,33,80,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32598 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 266 112 163 195 131 387), lower := (rows 13 35 84 266 112 32 64 128 256), losses := [] }

theorem u32598 : Upper (D 7) (R 7) [12,33,80,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32599 : Route 9 := (fun mask => (mask,id))

def c32599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32599 : Upper (D 7) (R 7) [12,33,80,258,129] 13 := by
  apply FastRouting.sound _ _ [12,33,80,258,129] 13 (by decide) (choices 1) [2,64,128] r32599 c32599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15967
  · exact u15968
  · exact u15969

def r32600 : Route 9 := (fun mask => (mask,id))

def c32600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32600 : Upper (D 7) (R 7) [12,33,80,258,130] 13 := by
  apply FastRouting.sound _ _ [12,33,80,258,130] 13 (by decide) (choices 1) [1,64,128] r32600 c32600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15970
  · exact u15971
  · exact u15972

def r32601 : Route 9 := (fun mask => (mask,id))

def c32601 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32601 : Upper (D 7) (R 7) [12,33,80,258,160] 13 := by
  apply FastRouting.sound _ _ [12,33,80,258,160] 13 (by decide) (choices 1) [1,2,64,128] r32601 c32601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15973
  · exact u15974
  · exact u15975
  · exact u15976

def b32602 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 266 208 163 227 163 419), lower := (rows 13 35 84 266 208 32 64 128 256), losses := [] }

theorem u32602 : Upper (D 7) (R 7) [12,33,80,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32603 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 35 84 296 19 226 194 194 450), lower := (rows 13 35 84 296 19 32 64 128 256), losses := [] }

theorem u32603 : Upper (D 7) (R 7) [12,33,80,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32604 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 296 81 162 194 130 386), lower := (rows 13 35 84 296 81 32 64 128 256), losses := [] }

theorem u32604 : Upper (D 7) (R 7) [12,33,80,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32605 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 296 82 163 195 131 387), lower := (rows 13 35 84 296 82 32 64 128 256), losses := [] }

theorem u32605 : Upper (D 7) (R 7) [12,33,80,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32606 : Route 9 := (fun mask => (mask,id))

def c32606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32606 : Upper (D 7) (R 7) [12,33,80,288,129] 13 := by
  apply FastRouting.sound _ _ [12,33,80,288,129] 13 (by decide) (choices 1) [2,64,128] r32606 c32606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15977
  · exact u15978
  · exact u15979

def r32607 : Route 9 := (fun mask => (mask,id))

def c32607 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32607 : Upper (D 7) (R 7) [12,33,80,288,130] 13 := by
  apply FastRouting.sound _ _ [12,33,80,288,130] 13 (by decide) (choices 1) [1,2,64,128] r32607 c32607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15980
  · exact u15981
  · exact u15982
  · exact u15983

def b32608 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 296 208 163 195 131 387), lower := (rows 13 35 84 296 208 32 64 128 256), losses := [] }

theorem u32608 : Upper (D 7) (R 7) [12,33,80,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32609 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 16, targets := 160 }], pairs := [(1,6),(4,5),(4,6),(4,7)], upper := (rows 13 35 84 328 19 162 226 162 418), lower := (rows 13 35 84 328 19 32 64 128 256), losses := [] }

theorem u32609 : Upper (D 7) (R 7) [12,33,80,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32610 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 456, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,6),(3,0),(4,1),(4,6)], upper := (rows 13 35 84 328 49 162 194 130 386), lower := (rows 13 35 84 328 49 32 64 128 256), losses := [] }

theorem u32610 : Upper (D 7) (R 7) [12,33,80,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32611 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 162, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 35 84 328 50 163 195 131 387), lower := (rows 13 35 84 328 50 32 64 128 256), losses := [] }

theorem u32611 : Upper (D 7) (R 7) [12,33,80,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32612 : Route 9 := (fun mask => (mask,id))

def c32612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32612 : Upper (D 7) (R 7) [12,33,80,320,129] 13 := by
  apply FastRouting.sound _ _ [12,33,80,320,129] 13 (by decide) (choices 1) [2,128] r32612 c32612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15984
  · exact u15985

def r32613 : Route 9 := (fun mask => (mask,id))

def c32613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32613 : Upper (D 7) (R 7) [12,33,80,320,130] 13 := by
  apply FastRouting.sound _ _ [12,33,80,320,130] 13 (by decide) (choices 1) [1,2,128] r32613 c32613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15986
  · exact u15987
  · exact u15988

def r32614 : Route 9 := (fun mask => (mask,id))

def c32614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32614 : Upper (D 7) (R 7) [12,33,80,320,160] 13 := by
  apply FastRouting.sound _ _ [12,33,80,320,160] 13 (by decide) (choices 1) [1,2,128] r32614 c32614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15989
  · exact u15990
  · exact u15991

def b32615 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 35 84 392 19 226 226 226 482), lower := (rows 13 35 84 392 19 32 64 128 256), losses := [] }

theorem u32615 : Upper (D 7) (R 7) [12,33,80,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32616 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 35 84 392 49 226 194 194 450), lower := (rows 13 35 84 392 49 32 64 128 256), losses := [] }

theorem u32616 : Upper (D 7) (R 7) [12,33,80,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32617 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 35 84 392 50 227 195 195 451), lower := (rows 13 35 84 392 50 32 64 128 256), losses := [] }

theorem u32617 : Upper (D 7) (R 7) [12,33,80,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32618 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 392 81 162 226 162 418), lower := (rows 13 35 84 392 81 32 64 128 256), losses := [] }

theorem u32618 : Upper (D 7) (R 7) [12,33,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32619 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 392 82 163 227 163 419), lower := (rows 13 35 84 392 82 32 64 128 256), losses := [] }

theorem u32619 : Upper (D 7) (R 7) [12,33,80,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32620 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 392 112 163 195 131 387), lower := (rows 13 35 84 392 112 32 64 128 256), losses := [] }

theorem u32620 : Upper (D 7) (R 7) [12,33,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32621 : Route 9 := (fun mask => (mask,id))

def c32621 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32621 : Upper (D 7) (R 7) [12,33,80,384,129] 13 := by
  apply FastRouting.sound _ _ [12,33,80,384,129] 13 (by decide) (choices 1) [2,64] r32621 c32621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15992
  · exact u15993

def r32622 : Route 9 := (fun mask => (mask,id))

def c32622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32622 : Upper (D 7) (R 7) [12,33,80,384,130] 13 := by
  apply FastRouting.sound _ _ [12,33,80,384,130] 13 (by decide) (choices 1) [1,2,64] r32622 c32622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15994
  · exact u15995
  · exact u15996

def r32623 : Route 9 := (fun mask => (mask,id))

def c32623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32623 : Upper (D 7) (R 7) [12,33,80,384,160] 13 := by
  apply FastRouting.sound _ _ [12,33,80,384,160] 13 (by decide) (choices 1) [1,2,64] r32623 c32623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15997
  · exact u15998
  · exact u15999

def b32624 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 392 208 35 99 163 291), lower := (rows 13 35 84 392 208 32 64 128 256), losses := [] }

theorem u32624 : Upper (D 7) (R 7) [12,33,80,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32625 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 13 35 100 266 19 240 208 208 464), lower := (rows 13 35 100 266 19 32 64 128 256), losses := [] }

theorem u32625 : Upper (D 7) (R 7) [12,33,96,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32626 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 13 35 100 266 81 178 210 146 402), lower := (rows 13 35 100 266 81 32 64 128 256), losses := [] }

theorem u32626 : Upper (D 7) (R 7) [12,33,96,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32627 : Route 9 := (fun mask => (mask,id))

def c32627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32627 : Upper (D 7) (R 7) [12,33,96,258,66] 13 := by
  apply FastRouting.sound _ _ [12,33,96,258,66] 13 (by decide) (choices 1) [1,16,128] r32627 c32627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16000
  · exact u16001
  · exact u16002

def r32628 : Route 9 := (fun mask => (mask,id))

def c32628 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32628 : Upper (D 7) (R 7) [12,33,96,258,129] 13 := by
  apply FastRouting.sound _ _ [12,33,96,258,129] 13 (by decide) (choices 1) [2,16,64,128] r32628 c32628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16003
  · exact u16004
  · exact u16005
  · exact u16006

def r32629 : Route 9 := (fun mask => (mask,id))

def c32629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32629 : Upper (D 7) (R 7) [12,33,96,258,130] 13 := by
  apply FastRouting.sound _ _ [12,33,96,258,130] 13 (by decide) (choices 1) [1,16,64,128] r32629 c32629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16007
  · exact u16008
  · exact u16009
  · exact u16010

def r32630 : Route 9 := (fun mask => (mask,id))

def c32630 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32630 : Upper (D 7) (R 7) [12,33,96,258,192] 13 := by
  apply FastRouting.sound _ _ [12,33,96,258,192] 13 (by decide) (choices 1) [1,2,16,128] r32630 c32630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16011
  · exact u16012
  · exact u16013
  · exact u16014

def b32631 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 13 35 100 280 19 226 194 194 450), lower := (rows 13 35 100 280 19 32 64 128 256), losses := [] }

theorem u32631 : Upper (D 7) (R 7) [12,33,96,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32632 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 13 35 100 280 81 162 194 130 386), lower := (rows 13 35 100 280 81 32 64 128 256), losses := [] }

theorem u32632 : Upper (D 7) (R 7) [12,33,96,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32633 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 13 35 100 280 82 163 195 131 387), lower := (rows 13 35 100 280 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 24 16 35 0 131 259), good := (rows 431 419 36 280 442 32 0 128 256) }] }

theorem u32633 : Upper (D 7) (R 7) [12,33,96,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32634 : Route 9 := (fun mask => (mask,id))

def c32634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32634 : Upper (D 7) (R 7) [12,33,96,272,129] 13 := by
  apply FastRouting.sound _ _ [12,33,96,272,129] 13 (by decide) (choices 1) [2,64,128] r32634 c32634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16015
  · exact u16016
  · exact u16017

def r32635 : Route 9 := (fun mask => (mask,id))

def c32635 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32635 : Upper (D 7) (R 7) [12,33,96,272,130] 13 := by
  apply FastRouting.sound _ _ [12,33,96,272,130] 13 (by decide) (choices 1) [1,2,64,128] r32635 c32635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16018
  · exact u16019
  · exact u16020
  · exact u16021

def r32636 : Route 9 := (fun mask => (mask,id))

def c32636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32636 : Upper (D 7) (R 7) [12,33,96,272,192] 13 := by
  apply FastRouting.sound _ _ [12,33,96,272,192] 13 (by decide) (choices 1) [1,2,128] r32636 c32636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16022
  · exact u16023
  · exact u16024

def b32637 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 13 35 100 392 19 242 210 210 466), lower := (rows 13 35 100 392 19 32 64 128 256), losses := [] }

theorem u32637 : Upper (D 7) (R 7) [12,33,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32638 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 13 35 100 392 81 178 210 146 402), lower := (rows 13 35 100 392 81 32 64 128 256), losses := [] }

theorem u32638 : Upper (D 7) (R 7) [12,33,96,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32639 : Route 9 := (fun mask => (mask,id))

def c32639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32639 : Upper (D 7) (R 7) [12,33,96,384,66] 13 := by
  apply FastRouting.sound _ _ [12,33,96,384,66] 13 (by decide) (choices 1) [1,2,16,128] r32639 c32639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16025
  · exact u16026
  · exact u16027
  · exact u16028

#print axioms u32639
end Delivery.IrregularNine14.P07
