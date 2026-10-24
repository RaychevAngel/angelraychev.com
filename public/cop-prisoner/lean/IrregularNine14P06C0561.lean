import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0280
import IrregularNine14P06C0281
import IrregularNine14P06C0282

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33660 : Route 9 := (fun mask => (mask,id))

def c33660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33660 : Upper (D 6) (R 6) [10,144,96,260,6] 13 := by
  apply FastRouting.sound _ _ [10,144,96,260,6] 13 (by decide) (choices 1) [1,64] r33660 c33660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16850
  · exact u16851

def r33661 : Route 9 := (fun mask => (mask,id))

def c33661 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33661 : Upper (D 6) (R 6) [10,144,96,260,33] 13 := by
  apply FastRouting.sound _ _ [10,144,96,260,33] 13 (by decide) (choices 1) [1,2,4,64] r33661 c33661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16852
  · exact u16853
  · exact u16854
  · exact u16855

def r33662 : Route 9 := (fun mask => (mask,id))

def c33662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33662 : Upper (D 6) (R 6) [10,144,96,260,34] 13 := by
  apply FastRouting.sound _ _ [10,144,96,260,34] 13 (by decide) (choices 1) [1,4,64] r33662 c33662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16856
  · exact u16857
  · exact u16858

def b33663 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 100 268 52 99 67 195 323), lower := (rows 11 146 100 268 52 32 64 128 256), losses := [] }

theorem u33663 : Upper (D 6) (R 6) [10,144,96,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33664 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 146 100 268 112 39 71 135 263), lower := (rows 11 146 100 268 112 32 64 128 256), losses := [] }

theorem u33664 : Upper (D 6) (R 6) [10,144,96,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33665 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 100 296 19 101 69 197 325), lower := (rows 11 146 100 296 19 32 64 128 256), losses := [] }

theorem u33665 : Upper (D 6) (R 6) [10,144,96,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33666 : Route 9 := (fun mask => (mask,id))

def c33666 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33666 : Upper (D 6) (R 6) [10,144,96,288,5] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,5] 13 (by decide) (choices 1) [1,2,4,64] r33666 c33666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16859
  · exact u16860
  · exact u16861
  · exact u16862

def r33667 : Route 9 := (fun mask => (mask,id))

def c33667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33667 : Upper (D 6) (R 6) [10,144,96,288,6] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,6] 13 (by decide) (choices 1) [1,4,64] r33667 c33667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16863
  · exact u16864
  · exact u16865

def r33668 : Route 9 := (fun mask => (mask,id))

def c33668 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33668 : Upper (D 6) (R 6) [10,144,96,288,65] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,65] 13 (by decide) (choices 1) [1,2,4] r33668 c33668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16866
  · exact u16867
  · exact u16868

def r33669 : Route 9 := (fun mask => (mask,id))

def c33669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33669 : Upper (D 6) (R 6) [10,144,96,288,66] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288,66] 13 (by decide) (choices 1) [1,4] r33669 c33669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16869
  · exact u16870

def b33670 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 146 100 296 84 39 71 135 263), lower := (rows 11 146 100 296 84 32 64 128 256), losses := [] }

theorem u33670 : Upper (D 6) (R 6) [10,144,96,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33671 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 146 261 41 22 100 100 228 356), lower := (rows 11 146 261 41 22 32 64 128 256), losses := [] }

theorem u33671 : Upper (D 6) (R 6) [10,144,257,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33672 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 261 41 50 100 68 196 324), lower := (rows 11 146 261 41 50 32 64 128 256), losses := [] }

theorem u33672 : Upper (D 6) (R 6) [10,144,257,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33673 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 146 261 41 52 102 70 198 326), lower := (rows 11 146 261 41 52 32 64 128 256), losses := [] }

theorem u33673 : Upper (D 6) (R 6) [10,144,257,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33674 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 146 261 41 82 100 100 228 356), lower := (rows 11 146 261 41 82 32 64 128 256), losses := [] }

theorem u33674 : Upper (D 6) (R 6) [10,144,257,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33675 : Route 9 := (fun mask => (mask,id))

def c33675 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33675 : Upper (D 6) (R 6) [10,144,257,33,68] 13 := by
  apply FastRouting.sound _ _ [10,144,257,33,68] 13 (by decide) (choices 1) [2,4,64] r33675 c33675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16871
  · exact u16872
  · exact u16873

def b33676 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 146 261 41 112 102 70 198 326), lower := (rows 11 146 261 41 112 32 64 128 256), losses := [] }

theorem u33676 : Upper (D 6) (R 6) [10,144,257,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33677 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 261 44 19 100 100 228 356), lower := (rows 11 146 261 44 19 32 64 128 256), losses := [] }

theorem u33677 : Upper (D 6) (R 6) [10,144,257,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33678 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 146 261 44 21 98 98 226 354), lower := (rows 11 146 261 44 21 32 64 128 256), losses := [] }

theorem u33678 : Upper (D 6) (R 6) [10,144,257,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33679 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 146 261 44 22 97 97 225 353), lower := (rows 11 146 261 44 22 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 69 133 261), good := (rows 491 146 481 488 498 32 64 128 256) }] }

theorem u33679 : Upper (D 6) (R 6) [10,144,257,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33680 : Route 9 := (fun mask => (mask,id))

def c33680 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33680 : Upper (D 6) (R 6) [10,144,257,36,33] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36,33] 13 (by decide) (choices 1) [2,4,64] r33680 c33680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16874
  · exact u16875
  · exact u16876

def b33681 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 146 261 44 50 101 69 197 325), lower := (rows 11 146 261 44 50 32 64 128 256), losses := [] }

theorem u33681 : Upper (D 6) (R 6) [10,144,257,36,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33682 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 261 44 52 99 67 195 323), lower := (rows 11 146 261 44 52 32 64 128 256), losses := [] }

theorem u33682 : Upper (D 6) (R 6) [10,144,257,36,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33683 : Route 9 := (fun mask => (mask,id))

def c33683 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33683 : Upper (D 6) (R 6) [10,144,257,36,65] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36,65] 13 (by decide) (choices 1) [2,4,64] r33683 c33683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16877
  · exact u16878
  · exact u16879

def r33684 : Route 9 := (fun mask => (mask,id))

def c33684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33684 : Upper (D 6) (R 6) [10,144,257,36,66] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36,66] 13 (by decide) (choices 1) [1,4,64] r33684 c33684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16880
  · exact u16881
  · exact u16882

def r33685 : Route 9 := (fun mask => (mask,id))

def c33685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33685 : Upper (D 6) (R 6) [10,144,257,36,68] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36,68] 13 (by decide) (choices 1) [1,2,64] r33685 c33685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16883
  · exact u16884
  · exact u16885

def r33686 : Route 9 := (fun mask => (mask,id))

def c33686 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33686 : Upper (D 6) (R 6) [10,144,257,36,96] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36,96] 13 (by decide) (choices 1) [1,2,4,64] r33686 c33686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16886
  · exact u16887
  · exact u16888
  · exact u16889

def b33687 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 261 104 19 100 100 228 356), lower := (rows 11 146 261 104 19 32 64 128 256), losses := [] }

theorem u33687 : Upper (D 6) (R 6) [10,144,257,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33688 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 146 261 104 21 102 102 230 358), lower := (rows 11 146 261 104 21 32 64 128 256), losses := [] }

theorem u33688 : Upper (D 6) (R 6) [10,144,257,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33689 : Route 9 := (fun mask => (mask,id))

def c33689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33689 : Upper (D 6) (R 6) [10,144,257,96,6] 13 := by
  apply FastRouting.sound _ _ [10,144,257,96,6] 13 (by decide) (choices 1) [1,4,64] r33689 c33689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16890
  · exact u16891
  · exact u16892

def r33690 : Route 9 := (fun mask => (mask,id))

def c33690 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33690 : Upper (D 6) (R 6) [10,144,257,96,33] 13 := by
  apply FastRouting.sound _ _ [10,144,257,96,33] 13 (by decide) (choices 1) [2,4,64] r33690 c33690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16893
  · exact u16894
  · exact u16895

def b33691 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 146 261 104 50 101 69 197 325), lower := (rows 11 146 261 104 50 32 64 128 256), losses := [] }

theorem u33691 : Upper (D 6) (R 6) [10,144,257,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33692 : Route 9 := (fun mask => (mask,id))

def c33692 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33692 : Upper (D 6) (R 6) [10,144,257,96,36] 13 := by
  apply FastRouting.sound _ _ [10,144,257,96,36] 13 (by decide) (choices 1) [1,2,4,64] r33692 c33692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16896
  · exact u16897
  · exact u16898
  · exact u16899

def b33693 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 146 261 104 112 39 71 135 263), lower := (rows 11 146 261 104 112 32 64 128 256), losses := [] }

theorem u33693 : Upper (D 6) (R 6) [10,144,257,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33694 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 146 262 41 21 100 100 228 356), lower := (rows 11 146 262 41 21 32 64 128 256), losses := [] }

theorem u33694 : Upper (D 6) (R 6) [10,144,258,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33695 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 146 262 41 49 100 68 196 324), lower := (rows 11 146 262 41 49 32 64 128 256), losses := [] }

theorem u33695 : Upper (D 6) (R 6) [10,144,258,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33696 : Route 9 := (fun mask => (mask,id))

def c33696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33696 : Upper (D 6) (R 6) [10,144,258,33,36] 13 := by
  apply FastRouting.sound _ _ [10,144,258,33,36] 13 (by decide) (choices 1) [1,4,64] r33696 c33696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16900
  · exact u16901
  · exact u16902

def r33697 : Route 9 := (fun mask => (mask,id))

def c33697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33697 : Upper (D 6) (R 6) [10,144,258,33,65] 13 := by
  apply FastRouting.sound _ _ [10,144,258,33,65] 13 (by decide) (choices 1) [4,64] r33697 c33697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16903
  · exact u16904

def r33698 : Route 9 := (fun mask => (mask,id))

def c33698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33698 : Upper (D 6) (R 6) [10,144,258,33,68] 13 := by
  apply FastRouting.sound _ _ [10,144,258,33,68] 13 (by decide) (choices 1) [1,4,64] r33698 c33698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16905
  · exact u16906
  · exact u16907

def r33699 : Route 9 := (fun mask => (mask,id))

def c33699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33699 : Upper (D 6) (R 6) [10,144,258,33,96] 13 := by
  apply FastRouting.sound _ _ [10,144,258,33,96] 13 (by decide) (choices 1) [1,4,64] r33699 c33699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16908
  · exact u16909
  · exact u16910

def r33700 : Route 9 := (fun mask => (mask,id))

def c33700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33700 : Upper (D 6) (R 6) [10,144,258,36,5] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,5] 13 (by decide) (choices 1) [1,64] r33700 c33700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16911
  · exact u16912

def r33701 : Route 9 := (fun mask => (mask,id))

def c33701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33701 : Upper (D 6) (R 6) [10,144,258,36,33] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,33] 13 (by decide) (choices 1) [1,4,64] r33701 c33701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16913
  · exact u16914
  · exact u16915

def b33702 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 262 44 52 97 65 193 321), lower := (rows 11 146 262 44 52 32 64 128 256), losses := [] }

theorem u33702 : Upper (D 6) (R 6) [10,144,258,36,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33703 : Route 9 := (fun mask => (mask,id))

def c33703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33703 : Upper (D 6) (R 6) [10,144,258,36,65] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,65] 13 (by decide) (choices 1) [1,4,64] r33703 c33703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16916
  · exact u16917
  · exact u16918

def r33704 : Route 9 := (fun mask => (mask,id))

def c33704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33704 : Upper (D 6) (R 6) [10,144,258,36,68] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,68] 13 (by decide) (choices 1) [1,64] r33704 c33704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16919
  · exact u16920

def r33705 : Route 9 := (fun mask => (mask,id))

def c33705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33705 : Upper (D 6) (R 6) [10,144,258,36,96] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,96] 13 (by decide) (choices 1) [1,4,64] r33705 c33705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16921
  · exact u16922
  · exact u16923

def r33706 : Route 9 := (fun mask => (mask,id))

def c33706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33706 : Upper (D 6) (R 6) [10,144,258,96,5] 13 := by
  apply FastRouting.sound _ _ [10,144,258,96,5] 13 (by decide) (choices 1) [1,4,64] r33706 c33706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16924
  · exact u16925
  · exact u16926

def r33707 : Route 9 := (fun mask => (mask,id))

def c33707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33707 : Upper (D 6) (R 6) [10,144,258,96,33] 13 := by
  apply FastRouting.sound _ _ [10,144,258,96,33] 13 (by decide) (choices 1) [1,4,64] r33707 c33707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16927
  · exact u16928
  · exact u16929

def r33708 : Route 9 := (fun mask => (mask,id))

def c33708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33708 : Upper (D 6) (R 6) [10,144,258,96,36] 13 := by
  apply FastRouting.sound _ _ [10,144,258,96,36] 13 (by decide) (choices 1) [1,4,64] r33708 c33708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16930
  · exact u16931
  · exact u16932

def b33709 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 146 262 104 112 37 69 133 261), lower := (rows 11 146 262 104 112 32 64 128 256), losses := [] }

theorem u33709 : Upper (D 6) (R 6) [10,144,258,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33710 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 292 13 19 100 100 228 356), lower := (rows 11 146 292 13 19 32 64 128 256), losses := [] }

theorem u33710 : Upper (D 6) (R 6) [10,144,288,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33711 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 146 292 13 21 98 98 226 354), lower := (rows 11 146 292 13 21 32 64 128 256), losses := [] }

theorem u33711 : Upper (D 6) (R 6) [10,144,288,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33712 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 146 292 13 22 97 97 225 353), lower := (rows 11 146 292 13 22 32 64 128 256), losses := [] }

theorem u33712 : Upper (D 6) (R 6) [10,144,288,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33713 : Route 9 := (fun mask => (mask,id))

def c33713 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33713 : Upper (D 6) (R 6) [10,144,288,5,33] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,33] 13 (by decide) (choices 1) [2,4,64] r33713 c33713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16933
  · exact u16934
  · exact u16935

def r33714 : Route 9 := (fun mask => (mask,id))

def c33714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33714 : Upper (D 6) (R 6) [10,144,288,5,34] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,34] 13 (by decide) (choices 1) [1,4,64] r33714 c33714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16936
  · exact u16937
  · exact u16938

def b33715 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 292 13 52 99 67 195 323), lower := (rows 11 146 292 13 52 32 64 128 256), losses := [] }

theorem u33715 : Upper (D 6) (R 6) [10,144,288,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33716 : Route 9 := (fun mask => (mask,id))

def c33716 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33716 : Upper (D 6) (R 6) [10,144,288,5,65] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,65] 13 (by decide) (choices 1) [2,4,64] r33716 c33716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16939
  · exact u16940
  · exact u16941

def r33717 : Route 9 := (fun mask => (mask,id))

def c33717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33717 : Upper (D 6) (R 6) [10,144,288,5,66] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,66] 13 (by decide) (choices 1) [1,4,64] r33717 c33717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16942
  · exact u16943
  · exact u16944

def r33718 : Route 9 := (fun mask => (mask,id))

def c33718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33718 : Upper (D 6) (R 6) [10,144,288,5,68] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,68] 13 (by decide) (choices 1) [1,2,64] r33718 c33718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16945
  · exact u16946
  · exact u16947

def r33719 : Route 9 := (fun mask => (mask,id))

def c33719 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33719 : Upper (D 6) (R 6) [10,144,288,5,96] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,96] 13 (by decide) (choices 1) [1,2,4,64] r33719 c33719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16948
  · exact u16949
  · exact u16950
  · exact u16951

#print axioms u33719
end Delivery.IrregularNine14.P06
