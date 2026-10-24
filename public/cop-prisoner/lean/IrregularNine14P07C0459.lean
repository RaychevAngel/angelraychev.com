import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0169
import IrregularNine14P07C0170

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r27540 : Route 9 := (fun mask => (mask,id))

def c27540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27540 : Upper (D 7) (R 7) [36,320,72,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,320,72,17,130,128] 13 (by decide) (choices 1) [1,2,32] r27540 c27540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10150
  · exact u10151
  · exact u10152

def b27541 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 76 25 176 33 194 130 386), lower := (rows 37 322 76 25 176 33 64 128 256), losses := [] }

theorem u27541 : Upper (D 7) (R 7) [36,320,72,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27542 : Route 9 := (fun mask => (mask,id))

def c27542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27542 : Upper (D 7) (R 7) [36,320,72,17,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,72,17,160,2] 13 (by decide) (choices 1) [1,2,128] r27542 c27542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10153
  · exact u10154
  · exact u10155

def b27543 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 76 25 176 160 67 131 259), lower := (rows 37 322 76 25 176 160 64 128 256), losses := [] }

theorem u27543 : Upper (D 7) (R 7) [36,320,72,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27544 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 76 26 145 33 226 162 418), lower := (rows 37 322 76 26 145 33 64 128 256), losses := [] }

theorem u27544 : Upper (D 7) (R 7) [36,320,72,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27545 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 37 322 76 26 145 34 225 161 417), lower := (rows 37 322 76 26 145 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 21 42 0 133 261), good := (rows 437 290 445 58 401 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 354 109 58 17 34 64 0 256) }] }

theorem u27545 : Upper (D 7) (R 7) [36,320,72,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27546 : Route 9 := (fun mask => (mask,id))

def c27546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27546 : Upper (D 7) (R 7) [36,320,72,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,320,72,18,129,128] 13 (by decide) (choices 1) [1,2,32] r27546 c27546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10156
  · exact u10157
  · exact u10158

def b27547 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 76 26 176 33 195 131 387), lower := (rows 37 322 76 26 176 33 64 128 256), losses := [] }

theorem u27547 : Upper (D 7) (R 7) [36,320,72,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27548 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 2 },{ cop := 0, region := 450, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,6),(1,5),(4,1),(4,6)], upper := (rows 37 322 76 26 176 34 193 129 385), lower := (rows 37 322 76 26 176 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 21 42 0 133 261), good := (rows 437 290 445 58 176 34 0 128 256) }] }

theorem u27548 : Upper (D 7) (R 7) [36,320,72,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27549 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 76 26 176 160 67 131 259), lower := (rows 37 322 76 26 176 160 64 128 256), losses := [] }

theorem u27549 : Upper (D 7) (R 7) [36,320,72,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27550 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 76 42 19 33 208 144 400), lower := (rows 37 322 76 42 19 33 64 128 256), losses := [] }

theorem u27550 : Upper (D 7) (R 7) [36,320,72,34,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27551 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 76 42 19 48 193 129 385), lower := (rows 37 322 76 42 19 48 64 128 256), losses := [] }

theorem u27551 : Upper (D 7) (R 7) [36,320,72,34,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27551 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27552 : Route 9 := (fun mask => (mask,id))

def c27552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27552 : Upper (D 7) (R 7) [36,320,72,34,3,128] 13 := by
  apply FastRouting.sound _ _ [36,320,72,34,3,128] 13 (by decide) (choices 1) [1,16,128] r27552 c27552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10159
  · exact u10160
  · exact u10161

def b27553 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 37 322 76 42 145 33 210 146 402), lower := (rows 37 322 76 42 145 33 64 128 256), losses := [] }

theorem u27553 : Upper (D 7) (R 7) [36,320,72,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27554 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 322 76 42 145 34 209 145 401), lower := (rows 37 322 76 42 145 34 64 128 256), losses := [] }

theorem u27554 : Upper (D 7) (R 7) [36,320,72,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27555 : Route 9 := (fun mask => (mask,id))

def c27555 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27555 : Upper (D 7) (R 7) [36,320,72,34,129,16] 13 := by
  apply FastRouting.sound _ _ [36,320,72,34,129,16] 13 (by decide) (choices 1) [1,2,128] r27555 c27555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10162
  · exact u10163
  · exact u10164

def r27556 : Route 9 := (fun mask => (mask,id))

def c27556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27556 : Upper (D 7) (R 7) [36,320,72,34,129,128] 13 := by
  apply FastRouting.sound _ _ [36,320,72,34,129,128] 13 (by decide) (choices 1) [1,2,16] r27556 c27556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10165
  · exact u10166
  · exact u10167

def b27557 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 37 322 76 42 146 33 209 145 401), lower := (rows 37 322 76 42 146 33 64 128 256), losses := [] }

theorem u27557 : Upper (D 7) (R 7) [36,320,72,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27558 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 322 76 42 146 48 193 129 385), lower := (rows 37 322 76 42 146 48 64 128 256), losses := [] }

theorem u27558 : Upper (D 7) (R 7) [36,320,72,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27558 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27559 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 65 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 37 322 76 42 146 160 81 145 273), lower := (rows 37 322 76 42 146 160 64 128 256), losses := [] }

theorem u27559 : Upper (D 7) (R 7) [36,320,72,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27560 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 76 56 145 33 194 130 386), lower := (rows 37 322 76 56 145 33 64 128 256), losses := [] }

theorem u27560 : Upper (D 7) (R 7) [36,320,72,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27561 : Route 9 := (fun mask => (mask,id))

def c27561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27561 : Upper (D 7) (R 7) [36,320,72,48,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,72,48,129,2] 13 (by decide) (choices 1) [1,2,128] r27561 c27561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10168
  · exact u10169
  · exact u10170

def b27562 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 322 76 56 145 160 67 131 259), lower := (rows 37 322 76 56 145 160 64 128 256), losses := [] }

theorem u27562 : Upper (D 7) (R 7) [36,320,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27563 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 76 56 146 33 195 131 387), lower := (rows 37 322 76 56 146 33 64 128 256), losses := [] }

theorem u27563 : Upper (D 7) (R 7) [36,320,72,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27564 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(3,7)], upper := (rows 37 322 76 56 146 34 193 129 385), lower := (rows 37 322 76 56 146 34 64 128 256), losses := [] }

theorem u27564 : Upper (D 7) (R 7) [36,320,72,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27565 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 322 76 56 146 160 67 131 259), lower := (rows 37 322 76 56 146 160 64 128 256), losses := [] }

theorem u27565 : Upper (D 7) (R 7) [36,320,72,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27566 : Route 9 := (fun mask => (mask,id))

def c27566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u27566 : Upper (D 7) (R 7) [36,320,72,129,3,2] 13 := by
  apply FastRouting.sound _ _ [36,320,72,129,3,2] 13 (by decide) (choices 1) [16,32,128] r27566 c27566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10171
  · exact u10172
  · exact u10173

def b27567 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 4, region := 168, targets := 64 }], pairs := [(1,0),(2,0),(3,6)], upper := (rows 37 322 76 137 19 48 226 162 418), lower := (rows 37 322 76 137 19 48 64 128 256), losses := [{ target := 0, region := (rows 0 59 12 8 16 48 113 177 305), good := (rows 486 322 78 462 498 498 64 128 256) }] }

theorem u27567 : Upper (D 7) (R 7) [36,320,72,129,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27567 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27568 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 482, targets := 1 },{ cop := 4, region := 168, targets := 64 }], pairs := [(1,0),(1,7),(3,6),(4,7)], upper := (rows 37 322 76 137 19 160 114 178 306), lower := (rows 37 322 76 137 19 160 64 128 256), losses := [] }

theorem u27568 : Upper (D 7) (R 7) [36,320,72,129,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27569 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 76 137 50 33 210 146 402), lower := (rows 37 322 76 137 50 33 64 128 256), losses := [] }

theorem u27569 : Upper (D 7) (R 7) [36,320,72,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27570 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 322 76 137 50 34 209 145 401), lower := (rows 37 322 76 137 50 34 64 128 256), losses := [] }

theorem u27570 : Upper (D 7) (R 7) [36,320,72,129,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27571 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 76 137 50 48 195 131 387), lower := (rows 37 322 76 137 50 48 64 128 256), losses := [] }

theorem u27571 : Upper (D 7) (R 7) [36,320,72,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27571 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27572 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 322 76 137 50 160 83 147 275), lower := (rows 37 322 76 137 50 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 320 109 169 48 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 258 45 169 50 160 0 160 256) }] }

theorem u27572 : Upper (D 7) (R 7) [36,320,72,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27573 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 76 137 146 33 114 178 306), lower := (rows 37 322 76 137 146 33 64 128 256), losses := [] }

theorem u27573 : Upper (D 7) (R 7) [36,320,72,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27574 : Route 9 := (fun mask => (mask,id))

def c27574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27574 : Upper (D 7) (R 7) [36,320,72,129,130,2] 13 := by
  apply FastRouting.sound _ _ [36,320,72,129,130,2] 13 (by decide) (choices 1) [1,16,32] r27574 c27574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10174
  · exact u10175
  · exact u10176

def r27575 : Route 9 := (fun mask => (mask,id))

def c27575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27575 : Upper (D 7) (R 7) [36,320,72,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,320,72,129,130,16] 13 (by decide) (choices 1) [1,2,32] r27575 c27575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10177
  · exact u10178
  · exact u10179

def b27576 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 76 137 176 33 82 146 274), lower := (rows 37 322 76 137 176 33 64 128 256), losses := [] }

theorem u27576 : Upper (D 7) (R 7) [36,320,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27577 : Route 9 := (fun mask => (mask,id))

def c27577 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27577 : Upper (D 7) (R 7) [36,320,72,129,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,72,129,160,2] 13 (by decide) (choices 1) [1,2,16] r27577 c27577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10180
  · exact u10181
  · exact u10182

def b27578 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 76 137 176 48 67 131 259), lower := (rows 37 322 76 137 176 48 64 128 256), losses := [] }

theorem u27578 : Upper (D 7) (R 7) [36,320,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27578 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27579 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 168, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 322 76 138 19 33 240 176 432), lower := (rows 37 322 76 138 19 33 64 128 256), losses := [] }

theorem u27579 : Upper (D 7) (R 7) [36,320,72,130,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27580 : Route 9 := (fun mask => (mask,id))

def c27580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27580 : Upper (D 7) (R 7) [36,320,72,130,3,16] 13 := by
  apply FastRouting.sound _ _ [36,320,72,130,3,16] 13 (by decide) (choices 1) [1,32,128] r27580 c27580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10183
  · exact u10184
  · exact u10185

def b27581 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 168, targets := 64 }], pairs := [(0,1),(1,7),(3,6),(4,7)], upper := (rows 37 322 76 138 19 160 113 177 305), lower := (rows 37 322 76 138 19 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 184 80 144 272), good := (rows 37 320 109 168 497 160 64 160 256) }] }

theorem u27581 : Upper (D 7) (R 7) [36,320,72,130,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27582 : Route 9 := (fun mask => (mask,id))

def c27582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27582 : Upper (D 7) (R 7) [36,320,72,130,34,1] 13 := by
  apply FastRouting.sound _ _ [36,320,72,130,34,1] 13 (by decide) (choices 1) [1,16,128] r27582 c27582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10186
  · exact u10187
  · exact u10188

def b27583 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 76 138 50 48 193 129 385), lower := (rows 37 322 76 138 50 48 64 128 256), losses := [] }

theorem u27583 : Upper (D 7) (R 7) [36,320,72,130,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27583 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27584 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 3, region := 48, targets := 65 }], pairs := [(1,7),(4,0),(4,6),(4,7)], upper := (rows 37 322 76 138 50 160 81 145 273), lower := (rows 37 322 76 138 50 160 64 128 256), losses := [] }

theorem u27584 : Upper (D 7) (R 7) [36,320,72,130,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27585 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 322 76 138 145 33 114 178 306), lower := (rows 37 322 76 138 145 33 64 128 256), losses := [] }

theorem u27585 : Upper (D 7) (R 7) [36,320,72,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27586 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 144, targets := 2 },{ cop := 0, region := 144, targets := 64 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,6),(1,7),(4,1),(4,6)], upper := (rows 37 322 76 138 145 34 113 177 305), lower := (rows 37 322 76 138 145 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 21 42 0 133 261), good := (rows 437 290 445 170 401 34 0 128 256) }] }

theorem u27586 : Upper (D 7) (R 7) [36,320,72,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27587 : Route 9 := (fun mask => (mask,id))

def c27587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27587 : Upper (D 7) (R 7) [36,320,72,130,129,16] 13 := by
  apply FastRouting.sound _ _ [36,320,72,130,129,16] 13 (by decide) (choices 1) [1,2,32] r27587 c27587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10189
  · exact u10190
  · exact u10191

def r27588 : Route 9 := (fun mask => (mask,id))

def c27588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27588 : Upper (D 7) (R 7) [36,320,72,130,160,1] 13 := by
  apply FastRouting.sound _ _ [36,320,72,130,160,1] 13 (by decide) (choices 1) [1,2,16] r27588 c27588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10192
  · exact u10193
  · exact u10194

def b27589 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 0, region := 144, targets := 2 }], pairs := [(0,6),(4,0),(4,1),(4,6)], upper := (rows 37 322 76 138 176 34 81 145 273), lower := (rows 37 322 76 138 176 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 29 42 0 133 261), good := (rows 437 290 445 186 176 34 0 128 256) }] }

theorem u27589 : Upper (D 7) (R 7) [36,320,72,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27590 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 76 138 176 48 67 131 259), lower := (rows 37 322 76 138 176 48 64 128 256), losses := [] }

theorem u27590 : Upper (D 7) (R 7) [36,320,72,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27590 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27591 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 76 152 19 33 226 162 418), lower := (rows 37 322 76 152 19 33 64 128 256), losses := [] }

theorem u27591 : Upper (D 7) (R 7) [36,320,72,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27592 : Route 9 := (fun mask => (mask,id))

def c27592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27592 : Upper (D 7) (R 7) [36,320,72,144,3,2] 13 := by
  apply FastRouting.sound _ _ [36,320,72,144,3,2] 13 (by decide) (choices 1) [1,32,128] r27592 c27592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10195
  · exact u10196
  · exact u10197

def b27593 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 168, targets := 64 }], pairs := [(0,1),(1,7),(3,6),(4,7)], upper := (rows 37 322 76 152 19 160 99 163 291), lower := (rows 37 322 76 152 19 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 320 109 184 17 160 64 160 256) }] }

theorem u27593 : Upper (D 7) (R 7) [36,320,72,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27594 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 76 152 50 33 195 131 387), lower := (rows 37 322 76 152 50 33 64 128 256), losses := [] }

theorem u27594 : Upper (D 7) (R 7) [36,320,72,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27595 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 322 76 152 50 34 193 129 385), lower := (rows 37 322 76 152 50 34 64 128 256), losses := [] }

theorem u27595 : Upper (D 7) (R 7) [36,320,72,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27596 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(0,1),(1,5),(1,7),(4,7)], upper := (rows 37 322 76 152 50 160 67 131 259), lower := (rows 37 322 76 152 50 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 320 109 184 48 160 64 160 256) }] }

theorem u27596 : Upper (D 7) (R 7) [36,320,72,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27597 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 76 168 19 33 210 146 402), lower := (rows 37 322 76 168 19 33 64 128 256), losses := [] }

theorem u27597 : Upper (D 7) (R 7) [36,320,72,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27598 : Route 9 := (fun mask => (mask,id))

def c27598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27598 : Upper (D 7) (R 7) [36,320,72,160,3,2] 13 := by
  apply FastRouting.sound _ _ [36,320,72,160,3,2] 13 (by decide) (choices 1) [1,16,128] r27598 c27598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10198
  · exact u10199
  · exact u10200

def b27599 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 168, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 37 322 76 168 19 48 195 131 387), lower := (rows 37 322 76 168 19 48 64 128 256), losses := [] }

theorem u27599 : Upper (D 7) (R 7) [36,320,72,160,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27599 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27599
end Delivery.IrregularNine14.P07
