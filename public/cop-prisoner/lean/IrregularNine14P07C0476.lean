import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0179

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28560 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 48, targets := 193 },{ cop := 4, region := 193, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 97 259 14 152 52 34 193 193 449), lower := (rows 97 259 14 152 52 34 64 128 256), losses := [] }

theorem u28560 : Upper (D 7) (R 7) [96,257,10,144,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28561 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 152 52 96 195 131 387), lower := (rows 97 259 14 152 52 96 64 128 256), losses := [] }

theorem u28561 : Upper (D 7) (R 7) [96,257,10,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28562 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 0, region := 258, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(4,0)], upper := (rows 97 259 14 152 52 160 67 195 323), lower := (rows 97 259 14 152 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 96 258 62 184 52 160 64 160 256) }] }

theorem u28562 : Upper (D 7) (R 7) [96,257,10,144,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28563 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 259 14 168 82 33 212 148 404), lower := (rows 97 259 14 168 82 33 64 128 256), losses := [] }

theorem u28563 : Upper (D 7) (R 7) [96,257,10,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28564 : Route 9 := (fun mask => (mask,id))

def c28564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28564 : Upper (D 7) (R 7) [96,257,10,160,66,4] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,66,4] 13 (by decide) (choices 1) [1,16,128] r28564 c28564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10768
  · exact u10769
  · exact u10770

def b28565 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 14 168 82 48 197 133 389), lower := (rows 97 259 14 168 82 48 64 128 256), losses := [] }

theorem u28565 : Upper (D 7) (R 7) [96,257,10,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28565 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28566 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 259 14 168 82 160 85 149 277), lower := (rows 97 259 14 168 82 160 64 128 256), losses := [] }

theorem u28566 : Upper (D 7) (R 7) [96,257,10,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28567 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 259 14 168 84 33 210 146 402), lower := (rows 97 259 14 168 84 33 64 128 256), losses := [] }

theorem u28567 : Upper (D 7) (R 7) [96,257,10,160,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28568 : Route 9 := (fun mask => (mask,id))

def c28568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28568 : Upper (D 7) (R 7) [96,257,10,160,68,2] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,68,2] 13 (by decide) (choices 1) [1,16,128] r28568 c28568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10771
  · exact u10772
  · exact u10773

def b28569 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 14 168 84 48 195 131 387), lower := (rows 97 259 14 168 84 48 64 128 256), losses := [] }

theorem u28569 : Upper (D 7) (R 7) [96,257,10,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28569 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28570 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 259 14 168 84 160 83 147 275), lower := (rows 97 259 14 168 84 160 64 128 256), losses := [] }

theorem u28570 : Upper (D 7) (R 7) [96,257,10,160,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28571 : Route 9 := (fun mask => (mask,id))

def c28571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28571 : Upper (D 7) (R 7) [96,257,10,160,129,2] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,129,2] 13 (by decide) (choices 1) [4,16] r28571 c28571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10774
  · exact u10775

def b28572 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 4, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 97 259 14 168 145 36 82 210 338), lower := (rows 97 259 14 168 145 36 64 128 256), losses := [] }

theorem u28572 : Upper (D 7) (R 7) [96,257,10,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28572 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28573 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 259 14 168 145 48 70 198 326), lower := (rows 97 259 14 168 145 48 64 128 256), losses := [] }

theorem u28573 : Upper (D 7) (R 7) [96,257,10,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28573 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28574 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 168 145 96 86 150 278), lower := (rows 97 259 14 168 145 96 64 128 256), losses := [] }

theorem u28574 : Upper (D 7) (R 7) [96,257,10,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28575 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 259 14 168 146 33 84 212 340), lower := (rows 97 259 14 168 146 33 64 128 256), losses := [] }

theorem u28575 : Upper (D 7) (R 7) [96,257,10,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28576 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 259 14 168 146 36 81 209 337), lower := (rows 97 259 14 168 146 36 64 128 256), losses := [] }

theorem u28576 : Upper (D 7) (R 7) [96,257,10,160,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28576 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28577 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 259 14 168 146 48 69 197 325), lower := (rows 97 259 14 168 146 48 64 128 256), losses := [] }

theorem u28577 : Upper (D 7) (R 7) [96,257,10,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28577 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28578 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 168 146 96 85 149 277), lower := (rows 97 259 14 168 146 96 64 128 256), losses := [] }

theorem u28578 : Upper (D 7) (R 7) [96,257,10,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28579 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 97 259 14 168 148 33 82 210 338), lower := (rows 97 259 14 168 148 33 64 128 256), losses := [] }

theorem u28579 : Upper (D 7) (R 7) [96,257,10,160,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28580 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(3,6)], upper := (rows 97 259 14 168 148 34 81 209 337), lower := (rows 97 259 14 168 148 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 38 64 128 256), good := (rows 96 290 46 168 188 34 64 128 256) },{ target := 6, region := (rows 1 2 4 24 16 38 0 128 256), good := (rows 33 291 46 168 188 34 0 128 256) }] }

theorem u28580 : Upper (D 7) (R 7) [96,257,10,160,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28581 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 259 14 168 148 48 67 195 323), lower := (rows 97 259 14 168 148 48 64 128 256), losses := [] }

theorem u28581 : Upper (D 7) (R 7) [96,257,10,160,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28581 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28582 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 14 168 148 96 83 147 275), lower := (rows 97 259 14 168 148 96 64 128 256), losses := [] }

theorem u28582 : Upper (D 7) (R 7) [96,257,10,160,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28583 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 208, targets := 33 },{ cop := 4, region := 41, targets := 2 }], pairs := [(0,1),(3,1),(4,0),(4,5)], upper := (rows 97 259 14 168 208 33 86 150 278), lower := (rows 97 259 14 168 208 33 64 128 256), losses := [] }

theorem u28583 : Upper (D 7) (R 7) [96,257,10,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28584 : Route 9 := (fun mask => (mask,id))

def c28584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28584 : Upper (D 7) (R 7) [96,257,10,160,192,2] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,192,2] 13 (by decide) (choices 1) [1,4,16] r28584 c28584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10776
  · exact u10777
  · exact u10778

def r28585 : Route 9 := (fun mask => (mask,id))

def c28585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28585 : Upper (D 7) (R 7) [96,257,10,160,192,4] 13 := by
  apply FastRouting.sound _ _ [96,257,10,160,192,4] 13 (by decide) (choices 1) [1,2,16] r28585 c28585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10779
  · exact u10780
  · exact u10781

def b28586 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 14 168 208 48 71 135 263), lower := (rows 97 259 14 168 208 48 64 128 256), losses := [] }

theorem u28586 : Upper (D 7) (R 7) [96,257,10,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28586 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28587 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 97 259 28 42 82 33 196 132 388), lower := (rows 97 259 28 42 82 33 64 128 256), losses := [] }

theorem u28587 : Upper (D 7) (R 7) [96,257,24,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28588 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 259 28 42 82 36 193 129 385), lower := (rows 97 259 28 42 82 36 64 128 256), losses := [] }

theorem u28588 : Upper (D 7) (R 7) [96,257,24,34,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28588 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28589_1 : Upper (D 7) (R 7) [96,257,24,34,66,128,1] 13 :=
  permutation_upper _ _ _ [96,257,24,34,66,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10782

theorem m28589_4 : Upper (D 7) (R 7) [96,257,24,34,66,128,4] 13 :=
  permutation_upper _ _ _ [96,257,24,34,66,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10783

def r28589 : Route 9 := (fun mask => (mask,id))

def c28589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28589 : Upper (D 7) (R 7) [96,257,24,34,66,128] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,66,128] 13 (by decide) (choices 1) [1,4,128] r28589 c28589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m28589_1
  · exact m28589_4
  · exact u10784

def b28590 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 259 28 42 145 34 196 196 452), lower := (rows 97 259 28 42 145 34 64 128 256), losses := [] }

theorem u28590 : Upper (D 7) (R 7) [96,257,24,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28591 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 259 28 42 145 36 194 194 450), lower := (rows 97 259 28 42 145 36 64 128 256), losses := [{ target := 5, region := (rows 1 19 12 8 19 0 95 159 287), good := (rows 467 467 478 478 467 452 64 128 256) }] }

theorem u28591 : Upper (D 7) (R 7) [96,257,24,34,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28591 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28592 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 28 42 145 96 198 134 390), lower := (rows 97 259 28 42 145 96 64 128 256), losses := [] }

theorem u28592 : Upper (D 7) (R 7) [96,257,24,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28593 : Route 9 := (fun mask => (mask,id))

def c28593 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28593 : Upper (D 7) (R 7) [96,257,24,34,129,128] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,129,128] 13 (by decide) (choices 1) [2,4] r28593 c28593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10785
  · exact u10786

def b28594 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 97 259 28 42 146 33 196 196 452), lower := (rows 97 259 28 42 146 33 64 128 256), losses := [] }

theorem u28594 : Upper (D 7) (R 7) [96,257,24,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28595 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 259 28 42 146 36 193 193 449), lower := (rows 97 259 28 42 146 36 64 128 256), losses := [] }

theorem u28595 : Upper (D 7) (R 7) [96,257,24,34,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28595 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28596 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 28 42 146 96 197 133 389), lower := (rows 97 259 28 42 146 96 64 128 256), losses := [] }

theorem u28596 : Upper (D 7) (R 7) [96,257,24,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28597 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 259 28 42 146 160 69 197 325), lower := (rows 97 259 28 42 146 160 64 128 256), losses := [] }

theorem u28597 : Upper (D 7) (R 7) [96,257,24,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28598 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 97 259 28 42 148 33 194 194 450), lower := (rows 97 259 28 42 148 33 64 128 256), losses := [] }

theorem u28598 : Upper (D 7) (R 7) [96,257,24,34,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28599 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 193, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 259 28 42 148 34 193 193 449), lower := (rows 97 259 28 42 148 34 64 128 256), losses := [] }

theorem u28599 : Upper (D 7) (R 7) [96,257,24,34,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28600 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 28 42 148 96 195 131 387), lower := (rows 97 259 28 42 148 96 64 128 256), losses := [] }

theorem u28600 : Upper (D 7) (R 7) [96,257,24,34,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28601 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 331, targets := 128 },{ cop := 0, region := 258, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,7)], upper := (rows 97 259 28 42 148 160 67 195 323), lower := (rows 97 259 28 42 148 160 64 128 256), losses := [] }

theorem u28601 : Upper (D 7) (R 7) [96,257,24,34,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28602 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 97 259 28 42 208 33 198 134 390), lower := (rows 97 259 28 42 208 33 64 128 256), losses := [] }

theorem u28602 : Upper (D 7) (R 7) [96,257,24,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28603 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 259 28 42 208 34 197 133 389), lower := (rows 97 259 28 42 208 34 64 128 256), losses := [] }

theorem u28603 : Upper (D 7) (R 7) [96,257,24,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28604 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 97 259 28 42 208 36 195 131 387), lower := (rows 97 259 28 42 208 36 64 128 256), losses := [] }

theorem u28604 : Upper (D 7) (R 7) [96,257,24,34,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28604 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28605 : Route 9 := (fun mask => (mask,id))

def c28605 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28605 : Upper (D 7) (R 7) [96,257,24,34,192,128] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,192,128] 13 (by decide) (choices 1) [1,2,4] r28605 c28605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10787
  · exact u10788
  · exact u10789

def r28606 : Route 9 := (fun mask => (mask,id))

def c28606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28606 : Upper (D 7) (R 7) [96,257,24,36,129,2] 13 := by
  apply FastRouting.sound _ _ [96,257,24,36,129,2] 13 (by decide) (choices 1) [2,128] r28606 c28606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10790
  · exact u10791

def b28607 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 28 44 145 96 194 130 386), lower := (rows 97 259 28 44 145 96 64 128 256), losses := [] }

theorem u28607 : Upper (D 7) (R 7) [96,257,24,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28608 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 97 259 28 44 145 160 66 194 322), lower := (rows 97 259 28 44 145 160 64 128 256), losses := [] }

theorem u28608 : Upper (D 7) (R 7) [96,257,24,36,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28609 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(4,5)], upper := (rows 97 259 28 44 146 33 194 194 450), lower := (rows 97 259 28 44 146 33 64 128 256), losses := [] }

theorem u28609 : Upper (D 7) (R 7) [96,257,24,36,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28610 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0)], upper := (rows 97 259 28 44 146 34 193 193 449), lower := (rows 97 259 28 44 146 34 64 128 256), losses := [] }

theorem u28610 : Upper (D 7) (R 7) [96,257,24,36,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28611 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 28 44 146 96 195 131 387), lower := (rows 97 259 28 44 146 96 64 128 256), losses := [] }

theorem u28611 : Upper (D 7) (R 7) [96,257,24,36,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28612 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 97 259 28 44 146 160 67 195 323), lower := (rows 97 259 28 44 146 160 64 128 256), losses := [] }

theorem u28612 : Upper (D 7) (R 7) [96,257,24,36,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28613 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 259 28 44 208 33 194 130 386), lower := (rows 97 259 28 44 208 33 64 128 256), losses := [] }

theorem u28613 : Upper (D 7) (R 7) [96,257,24,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28614 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,5),(4,5)], upper := (rows 97 259 28 44 208 34 195 131 387), lower := (rows 97 259 28 44 208 34 64 128 256), losses := [{ target := 5, region := (rows 1 3 12 8 51 0 67 131 259), good := (rows 467 467 28 28 208 466 64 128 256) }] }

theorem u28614 : Upper (D 7) (R 7) [96,257,24,36,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28615 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 259 28 44 208 160 67 131 259), lower := (rows 97 259 28 44 208 160 64 128 256), losses := [] }

theorem u28615 : Upper (D 7) (R 7) [96,257,24,36,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28616 : Route 9 := (fun mask => (mask,id))

def c28616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28616 : Upper (D 7) (R 7) [96,257,24,129,130,2] 13 := by
  apply FastRouting.sound _ _ [96,257,24,129,130,2] 13 (by decide) (choices 1) [4,32] r28616 c28616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10792
  · exact u10793

theorem m28617_2 : Upper (D 7) (R 7) [96,257,24,129,130,4,2] 13 :=
  permutation_upper _ _ _ [96,257,24,129,130,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10792

def r28617 : Route 9 := (fun mask => (mask,id))

def c28617 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28617 : Upper (D 7) (R 7) [96,257,24,129,130,4] 13 := by
  apply FastRouting.sound _ _ [96,257,24,129,130,4] 13 (by decide) (choices 1) [2,32] r28617 c28617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28617_2
  · exact u10794

def b28618 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 28 137 146 96 102 166 294), lower := (rows 97 259 28 137 146 96 64 128 256), losses := [] }

theorem u28618 : Upper (D 7) (R 7) [96,257,24,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28619 : Route 9 := (fun mask => (mask,id))

def c28619 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28619 : Upper (D 7) (R 7) [96,257,24,129,160,2] 13 := by
  apply FastRouting.sound _ _ [96,257,24,129,160,2] 13 (by decide) (choices 1) [2,4] r28619 c28619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10795
  · exact u10796

#print axioms u28619
end Delivery.IrregularNine14.P07
