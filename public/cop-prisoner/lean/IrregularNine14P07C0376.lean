import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0114
import IrregularNine14P07C0115

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r22560 : Route 9 := (fun mask => (mask,id))

def c22560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22560 : Upper (D 7) (R 7) [36,72,3,48,320,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,48,320,128] 13 (by decide) (choices 1) [1,2,128] r22560 c22560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6884
  · exact u6885
  · exact u6886

def b22561 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 56 400 33 194 194 450), lower := (rows 37 74 7 56 400 33 64 128 256), losses := [] }

theorem u22561 : Upper (D 7) (R 7) [36,72,3,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22562 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 56 400 34 193 193 449), lower := (rows 37 74 7 56 400 34 64 128 256), losses := [] }

theorem u22562 : Upper (D 7) (R 7) [36,72,3,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22563 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 400, targets := 32 },{ cop := 2, region := 400, targets := 64 }], pairs := [(0,7),(2,7),(4,5),(4,6)], upper := (rows 37 74 7 56 400 96 195 131 387), lower := (rows 37 74 7 56 400 96 64 128 256), losses := [] }

theorem u22563 : Upper (D 7) (R 7) [36,72,3,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22564 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 74 7 56 400 160 67 195 323), lower := (rows 37 74 7 56 400 160 64 128 256), losses := [] }

theorem u22564 : Upper (D 7) (R 7) [36,72,3,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22565 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 137 112 34 464 400 400), lower := (rows 37 74 7 137 112 34 64 128 256), losses := [] }

theorem u22565 : Upper (D 7) (R 7) [36,72,3,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22566 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 137 112 48 450 386 386), lower := (rows 37 74 7 137 112 48 64 128 256), losses := [] }

theorem u22566 : Upper (D 7) (R 7) [36,72,3,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22566 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22567 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(0,6),(1,0),(4,0),(4,1)], upper := (rows 37 74 7 137 112 160 338 402 274), lower := (rows 37 74 7 137 112 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 18 168 64 128 256), good := (rows 37 120 21 169 112 160 64 160 256) },{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 37 47 7 169 48 160 0 160 256) }] }

theorem u22567 : Upper (D 7) (R 7) [36,72,3,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22568 : Route 9 := (fun mask => (mask,id))

def c22568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22568 : Upper (D 7) (R 7) [36,72,3,129,96,256] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,96,256] 13 (by decide) (choices 1) [2,16,128] r22568 c22568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6887
  · exact u6888
  · exact u6889

def b22569 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 137 176 34 336 464 336), lower := (rows 37 74 7 137 176 34 64 128 256), losses := [] }

theorem u22569 : Upper (D 7) (R 7) [36,72,3,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22570 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 137 176 48 322 450 322), lower := (rows 37 74 7 137 176 48 64 128 256), losses := [] }

theorem u22570 : Upper (D 7) (R 7) [36,72,3,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22570 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22571 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 137 176 96 338 402 274), lower := (rows 37 74 7 137 176 96 64 128 256), losses := [] }

theorem u22571 : Upper (D 7) (R 7) [36,72,3,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22572 : Route 9 := (fun mask => (mask,id))

def c22572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22572 : Upper (D 7) (R 7) [36,72,3,129,160,256] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,160,256] 13 (by decide) (choices 1) [2,16] r22572 c22572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6890
  · exact u6891

def b22573 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 137 208 34 368 432 304), lower := (rows 37 74 7 137 208 34 64 128 256), losses := [] }

theorem u22573 : Upper (D 7) (R 7) [36,72,3,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22574 : Route 9 := (fun mask => (mask,id))

def c22574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u22574 : Upper (D 7) (R 7) [36,72,3,129,192,16] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,192,16] 13 (by decide) (choices 1) [2,32,256] r22574 c22574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6892
  · exact u6893
  · exact u6894

def r22575 : Route 9 := (fun mask => (mask,id))

def c22575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22575 : Upper (D 7) (R 7) [36,72,3,129,192,256] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,192,256] 13 (by decide) (choices 1) [2,16,32] r22575 c22575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6895
  · exact u6896
  · exact u6897

def b22576 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 74 7 137 274 48 224 224 480), lower := (rows 37 74 7 137 274 48 64 128 256), losses := [] }

theorem u22576 : Upper (D 7) (R 7) [36,72,3,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22576 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22577 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 137 274 96 240 176 432), lower := (rows 37 74 7 137 274 96 64 128 256), losses := [] }

theorem u22577 : Upper (D 7) (R 7) [36,72,3,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22578 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 74 7 137 274 160 112 240 368), lower := (rows 37 74 7 137 274 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 22 8 16 168 0 128 256), good := (rows 37 47 7 169 279 160 0 160 256) }] }

theorem u22578 : Upper (D 7) (R 7) [36,72,3,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22579 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 137 304 34 208 208 464), lower := (rows 37 74 7 137 304 34 64 128 256), losses := [] }

theorem u22579 : Upper (D 7) (R 7) [36,72,3,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22580 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 74 7 137 304 48 194 194 450), lower := (rows 37 74 7 137 304 48 64 128 256), losses := [] }

theorem u22580 : Upper (D 7) (R 7) [36,72,3,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22580 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22581 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 137 304 96 210 146 402), lower := (rows 37 74 7 137 304 96 64 128 256), losses := [] }

theorem u22581 : Upper (D 7) (R 7) [36,72,3,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22582 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 74 7 137 304 160 82 210 338), lower := (rows 37 74 7 137 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 37 47 7 169 304 160 0 160 256) }] }

theorem u22582 : Upper (D 7) (R 7) [36,72,3,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22583 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 137 336 34 240 176 432), lower := (rows 37 74 7 137 336 34 64 128 256), losses := [] }

theorem u22583 : Upper (D 7) (R 7) [36,72,3,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22584 : Route 9 := (fun mask => (mask,id))

def c22584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22584 : Upper (D 7) (R 7) [36,72,3,129,320,16] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,320,16] 13 (by decide) (choices 1) [2,32,128] r22584 c22584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6898
  · exact u6899
  · exact u6900

def b22585 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 74 7 137 336 160 114 178 306), lower := (rows 37 74 7 137 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 37 47 7 169 272 160 0 160 256) }] }

theorem u22585 : Upper (D 7) (R 7) [36,72,3,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22586 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 137 400 34 112 240 368), lower := (rows 37 74 7 137 400 34 64 128 256), losses := [] }

theorem u22586 : Upper (D 7) (R 7) [36,72,3,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22587 : Route 9 := (fun mask => (mask,id))

def c22587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22587 : Upper (D 7) (R 7) [36,72,3,129,384,16] 13 := by
  apply FastRouting.sound _ _ [36,72,3,129,384,16] 13 (by decide) (choices 1) [2,32] r22587 c22587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6901
  · exact u6902

def b22588 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 137 400 96 114 178 306), lower := (rows 37 74 7 137 400 96 64 128 256), losses := [] }

theorem u22588 : Upper (D 7) (R 7) [36,72,3,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22589 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 138 112 33 464 400 400), lower := (rows 37 74 7 138 112 33 64 128 256), losses := [] }

theorem u22589 : Upper (D 7) (R 7) [36,72,3,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22590 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 138 112 48 449 385 385), lower := (rows 37 74 7 138 112 48 64 128 256), losses := [] }

theorem u22590 : Upper (D 7) (R 7) [36,72,3,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22590 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22591 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,6),(4,1)], upper := (rows 37 74 7 138 112 160 337 401 273), lower := (rows 37 74 7 138 112 160 64 128 256), losses := [] }

theorem u22591 : Upper (D 7) (R 7) [36,72,3,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22592 : Route 9 := (fun mask => (mask,id))

def c22592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22592 : Upper (D 7) (R 7) [36,72,3,130,96,256] 13 := by
  apply FastRouting.sound _ _ [36,72,3,130,96,256] 13 (by decide) (choices 1) [1,16,128] r22592 c22592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6903
  · exact u6904
  · exact u6905

def b22593 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 138 176 33 336 464 336), lower := (rows 37 74 7 138 176 33 64 128 256), losses := [] }

theorem u22593 : Upper (D 7) (R 7) [36,72,3,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22594 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 138 176 48 321 449 321), lower := (rows 37 74 7 138 176 48 64 128 256), losses := [] }

theorem u22594 : Upper (D 7) (R 7) [36,72,3,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22594 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22595 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 74 7 138 176 96 337 401 273), lower := (rows 37 74 7 138 176 96 64 128 256), losses := [] }

theorem u22595 : Upper (D 7) (R 7) [36,72,3,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22596 : Route 9 := (fun mask => (mask,id))

def c22596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22596 : Upper (D 7) (R 7) [36,72,3,130,160,256] 13 := by
  apply FastRouting.sound _ _ [36,72,3,130,160,256] 13 (by decide) (choices 1) [1,16] r22596 c22596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6906
  · exact u6907

def b22597 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 138 304 33 208 208 464), lower := (rows 37 74 7 138 304 33 64 128 256), losses := [] }

theorem u22597 : Upper (D 7) (R 7) [36,72,3,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22598 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 74 7 138 304 48 193 193 449), lower := (rows 37 74 7 138 304 48 64 128 256), losses := [] }

theorem u22598 : Upper (D 7) (R 7) [36,72,3,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22598 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22599 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 74 7 138 304 96 209 145 401), lower := (rows 37 74 7 138 304 96 64 128 256), losses := [] }

theorem u22599 : Upper (D 7) (R 7) [36,72,3,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22600 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,6),(4,1)], upper := (rows 37 74 7 138 304 160 81 209 337), lower := (rows 37 74 7 138 304 160 64 128 256), losses := [] }

theorem u22600 : Upper (D 7) (R 7) [36,72,3,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22601 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 138 336 33 240 176 432), lower := (rows 37 74 7 138 336 33 64 128 256), losses := [] }

theorem u22601 : Upper (D 7) (R 7) [36,72,3,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22602 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(3,6),(4,1)], upper := (rows 37 74 7 138 336 48 225 161 417), lower := (rows 37 74 7 138 336 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 16 48 0 129 257), good := (rows 429 10 399 138 304 48 0 128 256) }] }

theorem u22602 : Upper (D 7) (R 7) [36,72,3,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22602 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22603 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,6),(4,1)], upper := (rows 37 74 7 138 336 160 113 177 305), lower := (rows 37 74 7 138 336 160 64 128 256), losses := [] }

theorem u22603 : Upper (D 7) (R 7) [36,72,3,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22604 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 138 400 33 112 240 368), lower := (rows 37 74 7 138 400 33 64 128 256), losses := [] }

theorem u22604 : Upper (D 7) (R 7) [36,72,3,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22605 : Route 9 := (fun mask => (mask,id))

def c22605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22605 : Upper (D 7) (R 7) [36,72,3,130,384,16] 13 := by
  apply FastRouting.sound _ _ [36,72,3,130,384,16] 13 (by decide) (choices 1) [1,32] r22605 c22605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6908
  · exact u6909

def b22606 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 74 7 138 400 96 113 177 305), lower := (rows 37 74 7 138 400 96 64 128 256), losses := [] }

theorem u22606 : Upper (D 7) (R 7) [36,72,3,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22607 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 7 152 112 33 450 386 386), lower := (rows 37 74 7 152 112 33 64 128 256), losses := [] }

theorem u22607 : Upper (D 7) (R 7) [36,72,3,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22608 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 472, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(4,7)], upper := (rows 37 74 7 152 112 34 449 385 385), lower := (rows 37 74 7 152 112 34 64 128 256), losses := [] }

theorem u22608 : Upper (D 7) (R 7) [36,72,3,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22609 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 37 74 7 152 112 160 323 387 259), lower := (rows 37 74 7 152 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 36 122 22 184 112 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 18 168 64 128 256), good := (rows 37 120 21 184 112 160 64 160 256) }] }

theorem u22609 : Upper (D 7) (R 7) [36,72,3,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22610 : Route 9 := (fun mask => (mask,id))

def c22610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22610 : Upper (D 7) (R 7) [36,72,3,144,96,256] 13 := by
  apply FastRouting.sound _ _ [36,72,3,144,96,256] 13 (by decide) (choices 1) [1,2,128] r22610 c22610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6910
  · exact u6911
  · exact u6912

def b22611 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 152 273 34 224 224 480), lower := (rows 37 74 7 152 273 34 64 128 256), losses := [] }

theorem u22611 : Upper (D 7) (R 7) [36,72,3,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22612 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 7 152 273 96 226 162 418), lower := (rows 37 74 7 152 273 96 64 128 256), losses := [] }

theorem u22612 : Upper (D 7) (R 7) [36,72,3,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22613 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 74 7 152 273 160 98 226 354), lower := (rows 37 74 7 152 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 37 47 7 184 273 160 0 160 256) }] }

theorem u22613 : Upper (D 7) (R 7) [36,72,3,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22614 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 152 274 33 224 224 480), lower := (rows 37 74 7 152 274 33 64 128 256), losses := [] }

theorem u22614 : Upper (D 7) (R 7) [36,72,3,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22615 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 74 7 152 274 96 225 161 417), lower := (rows 37 74 7 152 274 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 13 20 32 0 129 257), good := (rows 445 10 415 152 274 32 0 128 256) }] }

theorem u22615 : Upper (D 7) (R 7) [36,72,3,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22616 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,6),(2,6),(4,7)], upper := (rows 37 74 7 152 274 160 97 225 353), lower := (rows 37 74 7 152 274 160 64 128 256), losses := [{ target := 6, region := (rows 11 2 22 8 16 168 0 128 256), good := (rows 37 47 7 189 279 160 0 160 256) },{ target := 7, region := (rows 1 2 4 8 20 32 65 0 257), good := (rows 373 74 343 24 274 32 64 0 256) }] }

theorem u22616 : Upper (D 7) (R 7) [36,72,3,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22617 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 152 304 33 194 194 450), lower := (rows 37 74 7 152 304 33 64 128 256), losses := [] }

theorem u22617 : Upper (D 7) (R 7) [36,72,3,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22618 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 152 304 34 193 193 449), lower := (rows 37 74 7 152 304 34 64 128 256), losses := [] }

theorem u22618 : Upper (D 7) (R 7) [36,72,3,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22619 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 74 7 152 304 96 195 131 387), lower := (rows 37 74 7 152 304 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 104 37 152 304 96 96 128 256) },{ target := 6, region := (rows 1 2 4 13 17 32 0 132 260), good := (rows 445 10 415 152 304 32 0 128 256) }] }

theorem u22619 : Upper (D 7) (R 7) [36,72,3,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22619
end Delivery.IrregularNine14.P07
