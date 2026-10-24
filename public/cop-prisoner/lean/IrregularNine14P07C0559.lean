import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0293
import IrregularNine14P07C0294

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33540 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 205, targets := 32 },{ cop := 0, region := 482, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 290 21 73 50 226 194 194 450), lower := (rows 13 290 21 73 50 32 64 128 256), losses := [] }

theorem u33540 : Upper (D 7) (R 7) [12,288,17,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33541 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 13, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 21 73 82 162 226 162 418), lower := (rows 13 290 21 73 82 32 64 128 256), losses := [] }

theorem u33541 : Upper (D 7) (R 7) [12,288,17,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33542 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 13, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 21 73 112 162 194 130 386), lower := (rows 13 290 21 73 112 32 64 128 256), losses := [] }

theorem u33542 : Upper (D 7) (R 7) [12,288,17,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33543 : Route 9 := (fun mask => (mask,id))

def c33543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33543 : Upper (D 7) (R 7) [12,288,17,65,130] 13 := by
  apply FastRouting.sound _ _ [12,288,17,65,130] 13 (by decide) (choices 1) [2,64,128] r33543 c33543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17606
  · exact u17607
  · exact u17608

def r33544 : Route 9 := (fun mask => (mask,id))

def c33544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33544 : Upper (D 7) (R 7) [12,288,17,65,160] 13 := by
  apply FastRouting.sound _ _ [12,288,17,65,160] 13 (by decide) (choices 1) [2,64,128] r33544 c33544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17609
  · exact u17610
  · exact u17611

def b33545 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 13, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 21 73 208 162 226 162 418), lower := (rows 13 290 21 73 208 32 64 128 256), losses := [] }

theorem u33545 : Upper (D 7) (R 7) [12,288,17,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33546 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 21, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 290 21 74 19 224 224 224 480), lower := (rows 13 290 21 74 19 32 64 128 256), losses := [] }

theorem u33546 : Upper (D 7) (R 7) [12,288,17,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33547 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 290 21 74 49 226 194 194 450), lower := (rows 13 290 21 74 49 32 64 128 256), losses := [] }

theorem u33547 : Upper (D 7) (R 7) [12,288,17,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33548 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 21 74 50 225 193 193 449), lower := (rows 13 290 21 74 50 32 64 128 256), losses := [] }

theorem u33548 : Upper (D 7) (R 7) [12,288,17,66,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33549 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 21, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 21 74 81 162 226 162 418), lower := (rows 13 290 21 74 81 32 64 128 256), losses := [] }

theorem u33549 : Upper (D 7) (R 7) [12,288,17,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33550 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 21, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 21 74 82 161 225 161 417), lower := (rows 13 290 21 74 82 32 64 128 256), losses := [] }

theorem u33550 : Upper (D 7) (R 7) [12,288,17,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33551 : Route 9 := (fun mask => (mask,id))

def c33551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33551 : Upper (D 7) (R 7) [12,288,17,66,96] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,96] 13 (by decide) (choices 1) [1,2,128] r33551 c33551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17612
  · exact u17613
  · exact u17614

def b33552 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 290 21 74 145 226 226 226 482), lower := (rows 13 290 21 74 145 32 64 128 256), losses := [] }

theorem u33552 : Upper (D 7) (R 7) [12,288,17,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33553 : Route 9 := (fun mask => (mask,id))

def c33553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33553 : Upper (D 7) (R 7) [12,288,17,66,130] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,130] 13 (by decide) (choices 1) [1,64,128] r33553 c33553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17615
  · exact u17616
  · exact u17617

def r33554 : Route 9 := (fun mask => (mask,id))

def c33554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33554 : Upper (D 7) (R 7) [12,288,17,66,160] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,160] 13 (by decide) (choices 1) [1,2,64,128] r33554 c33554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17618
  · exact u17619
  · exact u17620
  · exact u17621

def r33555 : Route 9 := (fun mask => (mask,id))

def c33555 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33555 : Upper (D 7) (R 7) [12,288,17,66,192] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,192] 13 (by decide) (choices 1) [1,2,128] r33555 c33555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17622
  · exact u17623
  · exact u17624

def b33556 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 194 },{ cop := 0, region := 482, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 13 290 21 104 19 226 194 194 450), lower := (rows 13 290 21 104 19 32 64 128 256), losses := [] }

theorem u33556 : Upper (D 7) (R 7) [12,288,17,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33557 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 21, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 21 104 81 162 194 130 386), lower := (rows 13 290 21 104 81 32 64 128 256), losses := [] }

theorem u33557 : Upper (D 7) (R 7) [12,288,17,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33558 : Route 9 := (fun mask => (mask,id))

def c33558 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33558 : Upper (D 7) (R 7) [12,288,17,96,66] 13 := by
  apply FastRouting.sound _ _ [12,288,17,96,66] 13 (by decide) (choices 1) [1,2,128] r33558 c33558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17625
  · exact u17626
  · exact u17627

def b33559 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 290 21 104 145 226 194 194 450), lower := (rows 13 290 21 104 145 32 64 128 256), losses := [] }

theorem u33559 : Upper (D 7) (R 7) [12,288,17,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33560 : Route 9 := (fun mask => (mask,id))

def c33560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33560 : Upper (D 7) (R 7) [12,288,17,96,130] 13 := by
  apply FastRouting.sound _ _ [12,288,17,96,130] 13 (by decide) (choices 1) [1,2,64,128] r33560 c33560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17628
  · exact u17629
  · exact u17630
  · exact u17631

def r33561 : Route 9 := (fun mask => (mask,id))

def c33561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33561 : Upper (D 7) (R 7) [12,288,17,96,192] 13 := by
  apply FastRouting.sound _ _ [12,288,17,96,192] 13 (by decide) (choices 1) [1,2,128] r33561 c33561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17632
  · exact u17633
  · exact u17634

def b33562 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 290 21 200 19 226 226 226 482), lower := (rows 13 290 21 200 19 32 64 128 256), losses := [] }

theorem u33562 : Upper (D 7) (R 7) [12,288,17,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33563 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 290 21 200 49 226 194 194 450), lower := (rows 13 290 21 200 49 32 64 128 256), losses := [] }

theorem u33563 : Upper (D 7) (R 7) [12,288,17,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33564 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 290 21 200 50 227 195 195 451), lower := (rows 13 290 21 200 50 32 64 128 256), losses := [] }

theorem u33564 : Upper (D 7) (R 7) [12,288,17,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33565 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 21, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 290 21 200 81 162 226 162 418), lower := (rows 13 290 21 200 81 32 64 128 256), losses := [] }

theorem u33565 : Upper (D 7) (R 7) [12,288,17,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33566 : Route 9 := (fun mask => (mask,id))

def c33566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33566 : Upper (D 7) (R 7) [12,288,17,192,66] 13 := by
  apply FastRouting.sound _ _ [12,288,17,192,66] 13 (by decide) (choices 1) [1,2,128] r33566 c33566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17635
  · exact u17636
  · exact u17637

def r33567 : Route 9 := (fun mask => (mask,id))

def c33567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33567 : Upper (D 7) (R 7) [12,288,17,192,96] 13 := by
  apply FastRouting.sound _ _ [12,288,17,192,96] 13 (by decide) (choices 1) [1,2,128] r33567 c33567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17638
  · exact u17639
  · exact u17640

def b33568 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 21, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 21 200 208 35 99 163 291), lower := (rows 13 290 21 200 208 32 64 128 256), losses := [] }

theorem u33568 : Upper (D 7) (R 7) [12,288,17,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33569 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 22 41 19 224 192 192 448), lower := (rows 13 290 22 41 19 32 64 128 256), losses := [] }

theorem u33569 : Upper (D 7) (R 7) [12,288,18,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33570 : Route 9 := (fun mask => (mask,id))

def c33570 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33570 : Upper (D 7) (R 7) [12,288,18,33,65] 13 := by
  apply FastRouting.sound _ _ [12,288,18,33,65] 13 (by decide) (choices 1) [2,64,128] r33570 c33570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17641
  · exact u17642
  · exact u17643

def b33571 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 290 22 41 82 225 193 193 449), lower := (rows 13 290 22 41 82 32 64 128 256), losses := [] }

theorem u33571 : Upper (D 7) (R 7) [12,288,18,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33572 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33572 : Upper (D 7) (R 7) [12,288,18,33,192] 13 := by
  apply FastRouting.sound _ _ [12,288,18,33,192] 13 (by decide) (choices 1) [1,2,64] r33572 c33572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17644
  · exact u17645
  · exact u17646

def b33573 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(2,5),(2,6),(2,7)], upper := (rows 13 290 22 73 19 224 224 224 480), lower := (rows 13 290 22 73 19 32 64 128 256), losses := [] }

theorem u33573 : Upper (D 7) (R 7) [12,288,18,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33574 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 4, region := 454, targets := 1 }], pairs := [(0,5),(1,0),(2,0),(3,5)], upper := (rows 13 290 22 73 49 226 194 194 450), lower := (rows 13 290 22 73 49 32 64 128 256), losses := [] }

theorem u33574 : Upper (D 7) (R 7) [12,288,18,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33575 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 20, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 13 290 22 73 50 225 193 193 449), lower := (rows 13 290 22 73 50 32 64 128 256), losses := [] }

theorem u33575 : Upper (D 7) (R 7) [12,288,18,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33576 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 13 290 22 73 81 162 226 162 418), lower := (rows 13 290 22 73 81 32 64 128 256), losses := [] }

theorem u33576 : Upper (D 7) (R 7) [12,288,18,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33577 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 22 73 82 161 225 161 417), lower := (rows 13 290 22 73 82 32 64 128 256), losses := [] }

theorem u33577 : Upper (D 7) (R 7) [12,288,18,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33578 : Route 9 := (fun mask => (mask,id))

def c33578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33578 : Upper (D 7) (R 7) [12,288,18,65,96] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65,96] 13 (by decide) (choices 1) [1,2,128] r33578 c33578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17647
  · exact u17648
  · exact u17649

def r33579 : Route 9 := (fun mask => (mask,id))

def c33579 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33579 : Upper (D 7) (R 7) [12,288,18,65,129] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65,129] 13 (by decide) (choices 1) [2,64,128] r33579 c33579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17650
  · exact u17651
  · exact u17652

def b33580 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 290 22 73 146 225 225 225 481), lower := (rows 13 290 22 73 146 32 64 128 256), losses := [] }

theorem u33580 : Upper (D 7) (R 7) [12,288,18,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33581 : Route 9 := (fun mask => (mask,id))

def c33581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33581 : Upper (D 7) (R 7) [12,288,18,65,160] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65,160] 13 (by decide) (choices 1) [1,2,64,128] r33581 c33581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17653
  · exact u17654
  · exact u17655
  · exact u17656

def r33582 : Route 9 := (fun mask => (mask,id))

def c33582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33582 : Upper (D 7) (R 7) [12,288,18,65,192] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65,192] 13 (by decide) (choices 1) [1,2,128] r33582 c33582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17657
  · exact u17658
  · exact u17659

def r33583 : Route 9 := (fun mask => (mask,id))

def c33583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33583 : Upper (D 7) (R 7) [12,288,18,66,33] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,33] 13 (by decide) (choices 1) [1,64,128] r33583 c33583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17660
  · exact u17661
  · exact u17662

def b33584 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 21, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 22 74 81 161 225 161 417), lower := (rows 13 290 22 74 81 32 64 128 256), losses := [] }

theorem u33584 : Upper (D 7) (R 7) [12,288,18,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33585 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 240, targets := 2 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,1)], upper := (rows 13 290 22 74 112 161 193 129 385), lower := (rows 13 290 22 74 112 32 64 128 256), losses := [] }

theorem u33585 : Upper (D 7) (R 7) [12,288,18,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33586 : Route 9 := (fun mask => (mask,id))

def c33586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33586 : Upper (D 7) (R 7) [12,288,18,66,129] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,129] 13 (by decide) (choices 1) [1,64,128] r33586 c33586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17663
  · exact u17664
  · exact u17665

def r33587 : Route 9 := (fun mask => (mask,id))

def c33587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33587 : Upper (D 7) (R 7) [12,288,18,66,160] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,160] 13 (by decide) (choices 1) [1,64,128] r33587 c33587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17666
  · exact u17667
  · exact u17668

def r33588 : Route 9 := (fun mask => (mask,id))

def c33588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33588 : Upper (D 7) (R 7) [12,288,18,66,192] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,192] 13 (by decide) (choices 1) [1,128] r33588 c33588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17669
  · exact u17670

def b33589 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 193 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 290 22 104 19 225 193 193 449), lower := (rows 13 290 22 104 19 32 64 128 256), losses := [] }

theorem u33589 : Upper (D 7) (R 7) [12,288,18,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33590 : Route 9 := (fun mask => (mask,id))

def c33590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33590 : Upper (D 7) (R 7) [12,288,18,96,65] 13 := by
  apply FastRouting.sound _ _ [12,288,18,96,65] 13 (by decide) (choices 1) [1,2,128] r33590 c33590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17671
  · exact u17672
  · exact u17673

def b33591 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 290 22 104 82 161 193 129 385), lower := (rows 13 290 22 104 82 32 64 128 256), losses := [] }

theorem u33591 : Upper (D 7) (R 7) [12,288,18,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33592 : Route 9 := (fun mask => (mask,id))

def c33592 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33592 : Upper (D 7) (R 7) [12,288,18,96,129] 13 := by
  apply FastRouting.sound _ _ [12,288,18,96,129] 13 (by decide) (choices 1) [1,2,64,128] r33592 c33592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17674
  · exact u17675
  · exact u17676
  · exact u17677

def b33593 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 290 22 104 146 225 193 193 449), lower := (rows 13 290 22 104 146 32 64 128 256), losses := [] }

theorem u33593 : Upper (D 7) (R 7) [12,288,18,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33594 : Route 9 := (fun mask => (mask,id))

def c33594 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33594 : Upper (D 7) (R 7) [12,288,18,96,192] 13 := by
  apply FastRouting.sound _ _ [12,288,18,96,192] 13 (by decide) (choices 1) [1,2,128] r33594 c33594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17678
  · exact u17679
  · exact u17680

def b33595 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 290 22 200 19 225 225 225 481), lower := (rows 13 290 22 200 19 32 64 128 256), losses := [] }

theorem u33595 : Upper (D 7) (R 7) [12,288,18,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33596 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33596 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33596 : Upper (D 7) (R 7) [12,288,18,192,33] 13 := by
  apply FastRouting.sound _ _ [12,288,18,192,33] 13 (by decide) (choices 1) [1,2,64] r33596 c33596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17681
  · exact u17682
  · exact u17683

def b33597 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 20, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 13 290 22 200 50 225 193 193 449), lower := (rows 13 290 22 200 50 32 64 128 256), losses := [] }

theorem u33597 : Upper (D 7) (R 7) [12,288,18,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33598 : Route 9 := (fun mask => (mask,id))

def c33598 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33598 : Upper (D 7) (R 7) [12,288,18,192,65] 13 := by
  apply FastRouting.sound _ _ [12,288,18,192,65] 13 (by decide) (choices 1) [1,2,128] r33598 c33598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17684
  · exact u17685
  · exact u17686

def b33599 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 290 22 200 82 161 225 161 417), lower := (rows 13 290 22 200 82 32 64 128 256), losses := [] }

theorem u33599 : Upper (D 7) (R 7) [12,288,18,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u33599
end Delivery.IrregularNine14.P07
