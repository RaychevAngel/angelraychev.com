import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0189
import IrregularNine14P07C0190

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29580 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 13 140 82 34 209 145 401), lower := (rows 97 290 13 140 82 34 64 128 256), losses := [] }

theorem u29580 : Upper (D 7) (R 7) [96,288,9,132,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29581 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 140 82 48 195 131 387), lower := (rows 97 290 13 140 82 48 64 128 256), losses := [] }

theorem u29581 : Upper (D 7) (R 7) [96,288,9,132,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29581 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29582 : Route 9 := (fun mask => (mask,id))

def c29582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29582 : Upper (D 7) (R 7) [96,288,9,132,66,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,132,66,128] 13 (by decide) (choices 1) [1,2,16] r29582 c29582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11385
  · exact u11386
  · exact u11387

def b29583 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 97 290 13 140 146 33 82 210 338), lower := (rows 97 290 13 140 146 33 64 128 256), losses := [] }

theorem u29583 : Upper (D 7) (R 7) [96,288,9,132,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29584 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 13 140 146 34 81 209 337), lower := (rows 97 290 13 140 146 34 64 128 256), losses := [] }

theorem u29584 : Upper (D 7) (R 7) [96,288,9,132,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29585 : Route 9 := (fun mask => (mask,id))

def c29585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29585 : Upper (D 7) (R 7) [96,288,9,132,130,16] 13 := by
  apply FastRouting.sound _ _ [96,288,9,132,130,16] 13 (by decide) (choices 1) [1,2] r29585 c29585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11388
  · exact u11389

def b29586 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 140 146 96 83 147 275), lower := (rows 97 290 13 140 146 96 64 128 256), losses := [] }

theorem u29586 : Upper (D 7) (R 7) [96,288,9,132,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29587 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 0, region := 402, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 97 290 13 140 208 33 82 146 274), lower := (rows 97 290 13 140 208 33 64 128 256), losses := [] }

theorem u29587 : Upper (D 7) (R 7) [96,288,9,132,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29588 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 13 140 208 34 83 147 275), lower := (rows 97 290 13 140 208 34 64 128 256), losses := [] }

theorem u29588 : Upper (D 7) (R 7) [96,288,9,132,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29589 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 140 208 48 67 131 259), lower := (rows 97 290 13 140 208 48 64 128 256), losses := [] }

theorem u29589 : Upper (D 7) (R 7) [96,288,9,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29589 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29590 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 200, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,0),(3,5)], upper := (rows 97 290 13 152 22 33 194 194 450), lower := (rows 97 290 13 152 22 33 64 128 256), losses := [] }

theorem u29590 : Upper (D 7) (R 7) [96,288,9,144,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29591 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(1,7)], upper := (rows 97 290 13 152 22 34 193 193 449), lower := (rows 97 290 13 152 22 34 64 128 256), losses := [] }

theorem u29591 : Upper (D 7) (R 7) [96,288,9,144,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29592 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 152 22 96 195 131 387), lower := (rows 97 290 13 152 22 96 64 128 256), losses := [] }

theorem u29592 : Upper (D 7) (R 7) [96,288,9,144,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29593 : Route 9 := (fun mask => (mask,id))

def c29593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29593 : Upper (D 7) (R 7) [96,288,9,144,6,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,144,6,128] 13 (by decide) (choices 1) [1,2] r29593 c29593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11390
  · exact u11391

def b29594 : PairBound 9 := { available := 134, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 2, region := 418, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(2,1)], upper := (rows 97 290 13 152 82 33 198 134 390), lower := (rows 97 290 13 152 82 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 125 64 128 256), good := (rows 97 288 45 189 113 33 97 128 256) }] }

theorem u29594 : Upper (D 7) (R 7) [96,288,9,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29595 : PairBound 9 := { available := 133, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 290 13 152 82 34 197 133 389), lower := (rows 97 290 13 152 82 34 64 128 256), losses := [] }

theorem u29595 : Upper (D 7) (R 7) [96,288,9,144,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29596 : Route 9 := (fun mask => (mask,id))

def c29596 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29596 : Upper (D 7) (R 7) [96,288,9,144,66,4] 13 := by
  apply FastRouting.sound _ _ [96,288,9,144,66,4] 13 (by decide) (choices 1) [1,2,128] r29596 c29596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11392
  · exact u11393
  · exact u11394

def r29597 : Route 9 := (fun mask => (mask,id))

def c29597 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29597 : Upper (D 7) (R 7) [96,288,9,144,66,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,144,66,128] 13 (by decide) (choices 1) [1,2,4] r29597 c29597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11395
  · exact u11396
  · exact u11397

def b29598 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 290 13 152 84 33 194 130 386), lower := (rows 97 290 13 152 84 33 64 128 256), losses := [] }

theorem u29598 : Upper (D 7) (R 7) [96,288,9,144,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29599 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 97 290 13 152 84 34 195 131 387), lower := (rows 97 290 13 152 84 34 64 128 256), losses := [{ target := 6, region := (rows 1 279 4 24 16 319 0 133 261), good := (rows 419 290 431 186 446 34 0 128 290) }] }

theorem u29599 : Upper (D 7) (R 7) [96,288,9,144,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29600 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 0, region := 258, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,6)], upper := (rows 97 290 13 152 84 160 67 131 259), lower := (rows 97 290 13 152 84 160 64 128 256), losses := [{ target := 6, region := (rows 1 23 4 24 16 189 0 133 261), good := (rows 419 290 431 186 446 160 0 160 256) }] }

theorem u29600 : Upper (D 7) (R 7) [96,288,9,144,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29601 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 290 13 200 22 33 210 146 402), lower := (rows 97 290 13 200 22 33 64 128 256), losses := [] }

theorem u29601 : Upper (D 7) (R 7) [96,288,9,192,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29602 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 97 290 13 200 22 34 209 145 401), lower := (rows 97 290 13 200 22 34 64 128 256), losses := [] }

theorem u29602 : Upper (D 7) (R 7) [96,288,9,192,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29603 : Route 9 := (fun mask => (mask,id))

def c29603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29603 : Upper (D 7) (R 7) [96,288,9,192,6,16] 13 := by
  apply FastRouting.sound _ _ [96,288,9,192,6,16] 13 (by decide) (choices 1) [1,2,128] r29603 c29603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11398
  · exact u11399
  · exact u11400

def b29604 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 3, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(4,6)], upper := (rows 97 290 13 200 22 160 83 147 275), lower := (rows 97 290 13 200 22 160 64 128 256), losses := [] }

theorem u29604 : Upper (D 7) (R 7) [96,288,9,192,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29605 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 97 290 13 200 145 34 86 150 278), lower := (rows 97 290 13 200 145 34 64 128 256), losses := [] }

theorem u29605 : Upper (D 7) (R 7) [96,288,9,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29606 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 290 13 200 145 36 82 146 274), lower := (rows 97 290 13 200 145 36 64 128 256), losses := [] }

theorem u29606 : Upper (D 7) (R 7) [96,288,9,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29606 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29607 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 290 13 200 145 48 70 134 262), lower := (rows 97 290 13 200 145 48 64 128 256), losses := [] }

theorem u29607 : Upper (D 7) (R 7) [96,288,9,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29607 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29608 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 290 13 200 146 33 86 150 278), lower := (rows 97 290 13 200 146 33 64 128 256), losses := [] }

theorem u29608 : Upper (D 7) (R 7) [96,288,9,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29609 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 97 290 13 200 146 34 85 149 277), lower := (rows 97 290 13 200 146 34 64 128 256), losses := [] }

theorem u29609 : Upper (D 7) (R 7) [96,288,9,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29610 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 290 13 200 146 36 83 147 275), lower := (rows 97 290 13 200 146 36 64 128 256), losses := [] }

theorem u29610 : Upper (D 7) (R 7) [96,288,9,192,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29610 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29611 : Route 9 := (fun mask => (mask,id))

def c29611 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29611 : Upper (D 7) (R 7) [96,288,9,192,130,16] 13 := by
  apply FastRouting.sound _ _ [96,288,9,192,130,16] 13 (by decide) (choices 1) [1,2,4] r29611 c29611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11401
  · exact u11402
  · exact u11403

def b29612 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(2,0)], upper := (rows 97 290 14 28 145 33 194 194 450), lower := (rows 97 290 14 28 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 35 20 24 16 32 119 183 311), good := (rows 482 482 462 476 478 482 64 128 256) }] }

theorem u29612 : Upper (D 7) (R 7) [96,288,10,20,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29613 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 14 28 145 34 193 193 449), lower := (rows 97 290 14 28 145 34 64 128 256), losses := [] }

theorem u29613 : Upper (D 7) (R 7) [96,288,10,20,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29614 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 14 28 145 96 195 131 387), lower := (rows 97 290 14 28 145 96 64 128 256), losses := [] }

theorem u29614 : Upper (D 7) (R 7) [96,288,10,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29615 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 290 14 28 145 160 67 195 323), lower := (rows 97 290 14 28 145 160 64 128 256), losses := [{ target := 7, region := (rows 35 35 20 24 16 32 119 0 311), good := (rows 355 355 335 348 351 355 64 0 256) }] }

theorem u29615 : Upper (D 7) (R 7) [96,288,10,20,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29616 : Route 9 := (fun mask => (mask,id))

def c29616 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29616 : Upper (D 7) (R 7) [96,288,10,20,192,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,20,192,1] 13 (by decide) (choices 1) [1,2,128] r29616 c29616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11404
  · exact u11405
  · exact u11406

def b29617 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 14 28 208 34 193 129 385), lower := (rows 97 290 14 28 208 34 64 128 256), losses := [] }

theorem u29617 : Upper (D 7) (R 7) [96,288,10,20,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29618 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 0, region := 258, targets := 64 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,6),(1,7)], upper := (rows 97 290 14 28 208 160 67 131 259), lower := (rows 97 290 14 28 208 160 64 128 256), losses := [] }

theorem u29618 : Upper (D 7) (R 7) [96,288,10,20,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29619 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 97 290 14 76 145 33 210 146 402), lower := (rows 97 290 14 76 145 33 64 128 256), losses := [] }

theorem u29619 : Upper (D 7) (R 7) [96,288,10,68,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29620 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 14 76 145 34 209 145 401), lower := (rows 97 290 14 76 145 34 64 128 256), losses := [] }

theorem u29620 : Upper (D 7) (R 7) [96,288,10,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29621 : Route 9 := (fun mask => (mask,id))

def c29621 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29621 : Upper (D 7) (R 7) [96,288,10,68,129,16] 13 := by
  apply FastRouting.sound _ _ [96,288,10,68,129,16] 13 (by decide) (choices 1) [1,2,128] r29621 c29621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11407
  · exact u11408
  · exact u11409

def r29622 : Route 9 := (fun mask => (mask,id))

def c29622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29622 : Upper (D 7) (R 7) [96,288,10,68,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,10,68,129,128] 13 (by decide) (choices 1) [1,2,16] r29622 c29622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11410
  · exact u11411
  · exact u11412

def b29623 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 97 290 14 76 146 33 209 145 401), lower := (rows 97 290 14 76 146 33 64 128 256), losses := [] }

theorem u29623 : Upper (D 7) (R 7) [96,288,10,68,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29624 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 97 290 14 76 146 48 193 129 385), lower := (rows 97 290 14 76 146 48 64 128 256), losses := [] }

theorem u29624 : Upper (D 7) (R 7) [96,288,10,68,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29624 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29625 : Route 9 := (fun mask => (mask,id))

def c29625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29625 : Upper (D 7) (R 7) [96,288,10,68,130,128] 13 := by
  apply FastRouting.sound _ _ [96,288,10,68,130,128] 13 (by decide) (choices 1) [1,16] r29625 c29625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11413
  · exact u11414

def b29626 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(2,6)], upper := (rows 97 290 14 88 145 33 198 134 390), lower := (rows 97 290 14 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 16 49 0 140 268), good := (rows 33 290 398 446 177 33 0 128 256) }] }

theorem u29626 : Upper (D 7) (R 7) [96,288,10,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29627 : Route 9 := (fun mask => (mask,id))

def c29627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29627 : Upper (D 7) (R 7) [96,288,10,80,129,2] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80,129,2] 13 (by decide) (choices 1) [1,4,128] r29627 c29627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11415
  · exact u11416
  · exact u11417

def b29628 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 402, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 14 88 145 36 195 131 387), lower := (rows 97 290 14 88 145 36 64 128 256), losses := [{ target := 6, region := (rows 1 11 12 8 17 44 0 145 273), good := (rows 435 290 46 446 403 36 0 128 256) }] }

theorem u29628 : Upper (D 7) (R 7) [96,288,10,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29628 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29629 : Route 9 := (fun mask => (mask,id))

def c29629 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29629 : Upper (D 7) (R 7) [96,288,10,80,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80,129,128] 13 (by decide) (choices 1) [1,2,4] r29629 c29629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11418
  · exact u11419
  · exact u11420

def r29630 : Route 9 := (fun mask => (mask,id))

def c29630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29630 : Upper (D 7) (R 7) [96,288,10,80,130,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80,130,1] 13 (by decide) (choices 1) [1,4,128] r29630 c29630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11421
  · exact u11422
  · exact u11423

def b29631 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 97 290 14 88 146 36 193 129 385), lower := (rows 97 290 14 88 146 36 64 128 256), losses := [] }

theorem u29631 : Upper (D 7) (R 7) [96,288,10,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29631 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29632 : Route 9 := (fun mask => (mask,id))

def c29632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29632 : Upper (D 7) (R 7) [96,288,10,80,130,128] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80,130,128] 13 (by decide) (choices 1) [1,4] r29632 c29632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11424
  · exact u11425

def r29633 : Route 9 := (fun mask => (mask,id))

def c29633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29633 : Upper (D 7) (R 7) [96,288,10,80,132,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80,132,1] 13 (by decide) (choices 1) [1,2,128] r29633 c29633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11426
  · exact u11427
  · exact u11428

def b29634 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(1,7)], upper := (rows 97 290 14 88 148 34 193 129 385), lower := (rows 97 290 14 88 148 34 64 128 256), losses := [] }

theorem u29634 : Upper (D 7) (R 7) [96,288,10,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29635 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 0, region := 258, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(1,7)], upper := (rows 97 290 14 88 148 160 67 131 259), lower := (rows 97 290 14 88 148 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 176 64 128 256), good := (rows 97 288 13 121 180 160 64 160 256) }] }

theorem u29635 : Upper (D 7) (R 7) [96,288,10,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29636 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 290 14 137 82 33 212 148 404), lower := (rows 97 290 14 137 82 33 64 128 256), losses := [] }

theorem u29636 : Upper (D 7) (R 7) [96,288,10,129,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29637 : Route 9 := (fun mask => (mask,id))

def c29637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29637 : Upper (D 7) (R 7) [96,288,10,129,66,4] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,66,4] 13 (by decide) (choices 1) [1,16,128] r29637 c29637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11429
  · exact u11430
  · exact u11431

def b29638 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 14 137 82 48 197 133 389), lower := (rows 97 290 14 137 82 48 64 128 256), losses := [] }

theorem u29638 : Upper (D 7) (R 7) [96,288,10,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29638 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29639 : Route 9 := (fun mask => (mask,id))

def c29639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29639 : Upper (D 7) (R 7) [96,288,10,129,66,128] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,66,128] 13 (by decide) (choices 1) [1,4,16] r29639 c29639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11432
  · exact u11433
  · exact u11434

#print axioms u29639
end Delivery.IrregularNine14.P07
