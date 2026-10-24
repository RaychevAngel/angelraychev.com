import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0278
import IrregularNine14P06C0279
import IrregularNine14P06C0280

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33600 : Route 9 := (fun mask => (mask,id))

def c33600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33600 : Upper (D 6) (R 6) [10,144,34,68,260] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,260] 13 (by decide) (choices 1) [1,64] r33600 c33600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16726
  · exact u16727

def r33601 : Route 9 := (fun mask => (mask,id))

def c33601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33601 : Upper (D 6) (R 6) [10,144,34,68,288] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,288] 13 (by decide) (choices 1) [1,4,64] r33601 c33601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16728
  · exact u16729
  · exact u16730

def r33602 : Route 9 := (fun mask => (mask,id))

def c33602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33602 : Upper (D 6) (R 6) [10,144,34,68,320] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,320] 13 (by decide) (choices 1) [1,4] r33602 c33602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16731
  · exact u16732

def r33603 : Route 9 := (fun mask => (mask,id))

def c33603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33603 : Upper (D 6) (R 6) [10,144,34,96,5] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,5] 13 (by decide) (choices 1) [1,4,64,256] r33603 c33603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16733
  · exact u16734
  · exact u16735
  · exact u16736

def r33604 : Route 9 := (fun mask => (mask,id))

def c33604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33604 : Upper (D 6) (R 6) [10,144,34,96,65] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,65] 13 (by decide) (choices 1) [1,4,256] r33604 c33604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16737
  · exact u16738
  · exact u16739

def r33605 : Route 9 := (fun mask => (mask,id))

def c33605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33605 : Upper (D 6) (R 6) [10,144,34,96,68] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,68] 13 (by decide) (choices 1) [1,4,256] r33605 c33605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16740
  · exact u16741
  · exact u16742

def r33606 : Route 9 := (fun mask => (mask,id))

def c33606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33606 : Upper (D 6) (R 6) [10,144,34,96,257] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,257] 13 (by decide) (choices 1) [1,4,64] r33606 c33606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16743
  · exact u16744
  · exact u16745

def r33607 : Route 9 := (fun mask => (mask,id))

def c33607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33607 : Upper (D 6) (R 6) [10,144,34,96,260] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,260] 13 (by decide) (choices 1) [1,4,64] r33607 c33607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16746
  · exact u16747
  · exact u16748

def r33608 : Route 9 := (fun mask => (mask,id))

def c33608 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33608 : Upper (D 6) (R 6) [10,144,34,96,320] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,320] 13 (by decide) (choices 1) [1,4] r33608 c33608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16749
  · exact u16750

def b33609 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 146 38 265 21 100 100 228 356), lower := (rows 11 146 38 265 21 32 64 128 256), losses := [] }

theorem u33609 : Upper (D 6) (R 6) [10,144,34,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33610 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 4, region := 198, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 146 38 265 49 100 68 196 324), lower := (rows 11 146 38 265 49 32 64 128 256), losses := [] }

theorem u33610 : Upper (D 6) (R 6) [10,144,34,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33611 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 38 265 52 101 69 197 325), lower := (rows 11 146 38 265 52 32 64 128 256), losses := [] }

theorem u33611 : Upper (D 6) (R 6) [10,144,34,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33612 : Route 9 := (fun mask => (mask,id))

def c33612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33612 : Upper (D 6) (R 6) [10,144,34,257,65] 13 := by
  apply FastRouting.sound _ _ [10,144,34,257,65] 13 (by decide) (choices 1) [4,64] r33612 c33612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16751
  · exact u16752

def r33613 : Route 9 := (fun mask => (mask,id))

def c33613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33613 : Upper (D 6) (R 6) [10,144,34,257,68] 13 := by
  apply FastRouting.sound _ _ [10,144,34,257,68] 13 (by decide) (choices 1) [1,4,64] r33613 c33613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16753
  · exact u16754
  · exact u16755

def r33614 : Route 9 := (fun mask => (mask,id))

def c33614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33614 : Upper (D 6) (R 6) [10,144,34,257,96] 13 := by
  apply FastRouting.sound _ _ [10,144,34,257,96] 13 (by decide) (choices 1) [1,4,64] r33614 c33614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16756
  · exact u16757
  · exact u16758

def r33615 : Route 9 := (fun mask => (mask,id))

def c33615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33615 : Upper (D 6) (R 6) [10,144,34,260,5] 13 := by
  apply FastRouting.sound _ _ [10,144,34,260,5] 13 (by decide) (choices 1) [1,64] r33615 c33615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16759
  · exact u16760

def r33616 : Route 9 := (fun mask => (mask,id))

def c33616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33616 : Upper (D 6) (R 6) [10,144,34,260,33] 13 := by
  apply FastRouting.sound _ _ [10,144,34,260,33] 13 (by decide) (choices 1) [1,4,64] r33616 c33616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16761
  · exact u16762
  · exact u16763

def b33617 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 38 268 52 97 65 193 321), lower := (rows 11 146 38 268 52 32 64 128 256), losses := [] }

theorem u33617 : Upper (D 6) (R 6) [10,144,34,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33618 : Route 9 := (fun mask => (mask,id))

def c33618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33618 : Upper (D 6) (R 6) [10,144,34,260,65] 13 := by
  apply FastRouting.sound _ _ [10,144,34,260,65] 13 (by decide) (choices 1) [1,4,64] r33618 c33618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16764
  · exact u16765
  · exact u16766

def r33619 : Route 9 := (fun mask => (mask,id))

def c33619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33619 : Upper (D 6) (R 6) [10,144,34,260,68] 13 := by
  apply FastRouting.sound _ _ [10,144,34,260,68] 13 (by decide) (choices 1) [1,64] r33619 c33619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16767
  · exact u16768

def r33620 : Route 9 := (fun mask => (mask,id))

def c33620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33620 : Upper (D 6) (R 6) [10,144,34,260,96] 13 := by
  apply FastRouting.sound _ _ [10,144,34,260,96] 13 (by decide) (choices 1) [1,4,64] r33620 c33620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16769
  · exact u16770
  · exact u16771

def r33621 : Route 9 := (fun mask => (mask,id))

def c33621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33621 : Upper (D 6) (R 6) [10,144,34,288,5] 13 := by
  apply FastRouting.sound _ _ [10,144,34,288,5] 13 (by decide) (choices 1) [1,4,64] r33621 c33621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16772
  · exact u16773
  · exact u16774

def r33622 : Route 9 := (fun mask => (mask,id))

def c33622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33622 : Upper (D 6) (R 6) [10,144,34,288,65] 13 := by
  apply FastRouting.sound _ _ [10,144,34,288,65] 13 (by decide) (choices 1) [1,4,64] r33622 c33622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16775
  · exact u16776
  · exact u16777

def r33623 : Route 9 := (fun mask => (mask,id))

def c33623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33623 : Upper (D 6) (R 6) [10,144,34,288,68] 13 := by
  apply FastRouting.sound _ _ [10,144,34,288,68] 13 (by decide) (choices 1) [1,4,64] r33623 c33623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16778
  · exact u16779
  · exact u16780

def r33624 : Route 9 := (fun mask => (mask,id))

def c33624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33624 : Upper (D 6) (R 6) [10,144,34,320,5] 13 := by
  apply FastRouting.sound _ _ [10,144,34,320,5] 13 (by decide) (choices 1) [1,4,64] r33624 c33624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16781
  · exact u16782
  · exact u16783

def r33625 : Route 9 := (fun mask => (mask,id))

def c33625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33625 : Upper (D 6) (R 6) [10,144,34,320,33] 13 := by
  apply FastRouting.sound _ _ [10,144,34,320,33] 13 (by decide) (choices 1) [1,4,64] r33625 c33625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16784
  · exact u16785
  · exact u16786

def b33626 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 38 328 52 101 69 197 325), lower := (rows 11 146 38 328 52 32 64 128 256), losses := [] }

theorem u33626 : Upper (D 6) (R 6) [10,144,34,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33627 : Route 9 := (fun mask => (mask,id))

def c33627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33627 : Upper (D 6) (R 6) [10,144,34,320,65] 13 := by
  apply FastRouting.sound _ _ [10,144,34,320,65] 13 (by decide) (choices 1) [1,4] r33627 c33627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16787
  · exact u16788

def r33628 : Route 9 := (fun mask => (mask,id))

def c33628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33628 : Upper (D 6) (R 6) [10,144,34,320,68] 13 := by
  apply FastRouting.sound _ _ [10,144,34,320,68] 13 (by decide) (choices 1) [1,4] r33628 c33628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16789
  · exact u16790

def b33629 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 146 38 328 112 37 69 133 261), lower := (rows 11 146 38 328 112 32 64 128 256), losses := [] }

theorem u33629 : Upper (D 6) (R 6) [10,144,34,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33630 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 100 13 19 356 356 484 356), lower := (rows 11 146 100 13 19 32 64 128 256), losses := [] }

theorem u33630 : Upper (D 6) (R 6) [10,144,96,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33631 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 146 100 13 21 354 354 482 354), lower := (rows 11 146 100 13 21 32 64 128 256), losses := [] }

theorem u33631 : Upper (D 6) (R 6) [10,144,96,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33632 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 146 100 13 22 353 353 481 353), lower := (rows 11 146 100 13 22 32 64 128 256), losses := [] }

theorem u33632 : Upper (D 6) (R 6) [10,144,96,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33633 : Route 9 := (fun mask => (mask,id))

def c33633 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33633 : Upper (D 6) (R 6) [10,144,96,5,33] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,33] 13 (by decide) (choices 1) [2,4,64,256] r33633 c33633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16791
  · exact u16792
  · exact u16793
  · exact u16794

def r33634 : Route 9 := (fun mask => (mask,id))

def c33634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33634 : Upper (D 6) (R 6) [10,144,96,5,34] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,34] 13 (by decide) (choices 1) [1,4,64,256] r33634 c33634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16795
  · exact u16796
  · exact u16797
  · exact u16798

def b33635 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 100 13 52 355 323 451 323), lower := (rows 11 146 100 13 52 32 64 128 256), losses := [] }

theorem u33635 : Upper (D 6) (R 6) [10,144,96,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33636 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 146 100 13 112 295 327 391 263), lower := (rows 11 146 100 13 112 32 64 128 256), losses := [] }

theorem u33636 : Upper (D 6) (R 6) [10,144,96,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33637 : Route 9 := (fun mask => (mask,id))

def c33637 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33637 : Upper (D 6) (R 6) [10,144,96,5,257] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,257] 13 (by decide) (choices 1) [2,4,64] r33637 c33637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16799
  · exact u16800
  · exact u16801

def r33638 : Route 9 := (fun mask => (mask,id))

def c33638 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33638 : Upper (D 6) (R 6) [10,144,96,5,258] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,258] 13 (by decide) (choices 1) [1,4,64] r33638 c33638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16802
  · exact u16803
  · exact u16804

def r33639 : Route 9 := (fun mask => (mask,id))

def c33639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33639 : Upper (D 6) (R 6) [10,144,96,5,260] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,260] 13 (by decide) (choices 1) [1,2,64] r33639 c33639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16805
  · exact u16806
  · exact u16807

def r33640 : Route 9 := (fun mask => (mask,id))

def c33640 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33640 : Upper (D 6) (R 6) [10,144,96,5,288] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5,288] 13 (by decide) (choices 1) [1,2,4,64] r33640 c33640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16808
  · exact u16809
  · exact u16810
  · exact u16811

def b33641 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 100 41 19 356 324 452 324), lower := (rows 11 146 100 41 19 32 64 128 256), losses := [] }

theorem u33641 : Upper (D 6) (R 6) [10,144,96,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33642 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 146 100 41 21 358 326 454 326), lower := (rows 11 146 100 41 21 32 64 128 256), losses := [] }

theorem u33642 : Upper (D 6) (R 6) [10,144,96,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33643 : Route 9 := (fun mask => (mask,id))

def c33643 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33643 : Upper (D 6) (R 6) [10,144,96,33,6] 13 := by
  apply FastRouting.sound _ _ [10,144,96,33,6] 13 (by decide) (choices 1) [1,4,64,256] r33643 c33643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16812
  · exact u16813
  · exact u16814
  · exact u16815

def r33644 : Route 9 := (fun mask => (mask,id))

def c33644 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33644 : Upper (D 6) (R 6) [10,144,96,33,65] 13 := by
  apply FastRouting.sound _ _ [10,144,96,33,65] 13 (by decide) (choices 1) [2,4,256] r33644 c33644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16816
  · exact u16817
  · exact u16818

def r33645 : Route 9 := (fun mask => (mask,id))

def c33645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33645 : Upper (D 6) (R 6) [10,144,96,33,66] 13 := by
  apply FastRouting.sound _ _ [10,144,96,33,66] 13 (by decide) (choices 1) [1,4,256] r33645 c33645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16819
  · exact u16820
  · exact u16821

def b33646 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 146 100 41 84 295 327 391 263), lower := (rows 11 146 100 41 84 32 64 128 256), losses := [] }

theorem u33646 : Upper (D 6) (R 6) [10,144,96,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33647 : Route 9 := (fun mask => (mask,id))

def c33647 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33647 : Upper (D 6) (R 6) [10,144,96,33,257] 13 := by
  apply FastRouting.sound _ _ [10,144,96,33,257] 13 (by decide) (choices 1) [2,4,64] r33647 c33647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16822
  · exact u16823
  · exact u16824

def r33648 : Route 9 := (fun mask => (mask,id))

def c33648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33648 : Upper (D 6) (R 6) [10,144,96,33,258] 13 := by
  apply FastRouting.sound _ _ [10,144,96,33,258] 13 (by decide) (choices 1) [1,4,64] r33648 c33648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16825
  · exact u16826
  · exact u16827

def r33649 : Route 9 := (fun mask => (mask,id))

def c33649 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33649 : Upper (D 6) (R 6) [10,144,96,33,260] 13 := by
  apply FastRouting.sound _ _ [10,144,96,33,260] 13 (by decide) (choices 1) [1,2,4,64] r33649 c33649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16828
  · exact u16829
  · exact u16830
  · exact u16831

def r33650 : Route 9 := (fun mask => (mask,id))

def c33650 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33650 : Upper (D 6) (R 6) [10,144,96,33,320] 13 := by
  apply FastRouting.sound _ _ [10,144,96,33,320] 13 (by decide) (choices 1) [1,2,4] r33650 c33650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16832
  · exact u16833
  · exact u16834

def b33651 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 100 265 19 100 100 228 356), lower := (rows 11 146 100 265 19 32 64 128 256), losses := [] }

theorem u33651 : Upper (D 6) (R 6) [10,144,96,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33652 : Route 9 := (fun mask => (mask,id))

def c33652 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33652 : Upper (D 6) (R 6) [10,144,96,257,5] 13 := by
  apply FastRouting.sound _ _ [10,144,96,257,5] 13 (by decide) (choices 1) [2,4,64] r33652 c33652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16835
  · exact u16836
  · exact u16837

def r33653 : Route 9 := (fun mask => (mask,id))

def c33653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33653 : Upper (D 6) (R 6) [10,144,96,257,6] 13 := by
  apply FastRouting.sound _ _ [10,144,96,257,6] 13 (by decide) (choices 1) [1,4,64] r33653 c33653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16838
  · exact u16839
  · exact u16840

def r33654 : Route 9 := (fun mask => (mask,id))

def c33654 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33654 : Upper (D 6) (R 6) [10,144,96,257,33] 13 := by
  apply FastRouting.sound _ _ [10,144,96,257,33] 13 (by decide) (choices 1) [2,4,64] r33654 c33654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16841
  · exact u16842
  · exact u16843

def r33655 : Route 9 := (fun mask => (mask,id))

def c33655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33655 : Upper (D 6) (R 6) [10,144,96,257,34] 13 := by
  apply FastRouting.sound _ _ [10,144,96,257,34] 13 (by decide) (choices 1) [1,4,64] r33655 c33655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16844
  · exact u16845
  · exact u16846

def b33656 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 100 265 52 103 71 199 327), lower := (rows 11 146 100 265 52 32 64 128 256), losses := [] }

theorem u33656 : Upper (D 6) (R 6) [10,144,96,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33657 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 146 100 265 112 39 71 135 263), lower := (rows 11 146 100 265 112 32 64 128 256), losses := [] }

theorem u33657 : Upper (D 6) (R 6) [10,144,96,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33658 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 100 268 19 101 101 229 357), lower := (rows 11 146 100 268 19 32 64 128 256), losses := [] }

theorem u33658 : Upper (D 6) (R 6) [10,144,96,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33659 : Route 9 := (fun mask => (mask,id))

def c33659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33659 : Upper (D 6) (R 6) [10,144,96,260,5] 13 := by
  apply FastRouting.sound _ _ [10,144,96,260,5] 13 (by decide) (choices 1) [1,2,64] r33659 c33659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16847
  · exact u16848
  · exact u16849

#print axioms u33659
end Delivery.IrregularNine14.P06
