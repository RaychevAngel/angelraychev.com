import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0042

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r12780 : Route 9 := (fun mask => (mask,id))

def c12780 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12780 : Upper (D 6) (R 6) [10,33,160,257,68,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,257,68,64] 13 (by decide) (choices 1) [2,4,16] r12780 c12780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2527
  · exact u2528
  · exact u2529

def b12781 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 164 268 21 34 80 208 336), lower := (rows 11 35 164 268 21 34 64 128 256), losses := [] }

theorem u12781 : Upper (D 6) (R 6) [10,33,160,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12782 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 268 21 48 66 194 322), lower := (rows 11 35 164 268 21 48 64 128 256), losses := [] }

theorem u12782 : Upper (D 6) (R 6) [10,33,160,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12782 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12783 : Route 9 := (fun mask => (mask,id))

def c12783 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12783 : Upper (D 6) (R 6) [10,33,160,260,5,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,5,64] 13 (by decide) (choices 1) [2,16] r12783 c12783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2530
  · exact u2531

def b12784 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 164 268 22 33 80 208 336), lower := (rows 11 35 164 268 22 33 64 128 256), losses := [] }

theorem u12784 : Upper (D 6) (R 6) [10,33,160,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12785 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 268 22 48 65 193 321), lower := (rows 11 35 164 268 22 48 64 128 256), losses := [] }

theorem u12785 : Upper (D 6) (R 6) [10,33,160,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12785 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12786 : Route 9 := (fun mask => (mask,id))

def c12786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12786 : Upper (D 6) (R 6) [10,33,160,260,6,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,6,64] 13 (by decide) (choices 1) [1,16] r12786 c12786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2532
  · exact u2533

def b12787 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 268 81 34 84 212 340), lower := (rows 11 35 164 268 81 34 64 128 256), losses := [] }

theorem u12787 : Upper (D 6) (R 6) [10,33,160,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12788 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 268 81 36 82 210 338), lower := (rows 11 35 164 268 81 36 64 128 256), losses := [] }

theorem u12788 : Upper (D 6) (R 6) [10,33,160,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12789 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 164 268 81 48 70 198 326), lower := (rows 11 35 164 268 81 48 64 128 256), losses := [] }

theorem u12789 : Upper (D 6) (R 6) [10,33,160,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12789 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12790 : Route 9 := (fun mask => (mask,id))

def c12790 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12790 : Upper (D 6) (R 6) [10,33,160,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,65,64] 13 (by decide) (choices 1) [2,4,16] r12790 c12790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2534
  · exact u2535
  · exact u2536

def b12791 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 268 82 33 84 212 340), lower := (rows 11 35 164 268 82 33 64 128 256), losses := [] }

theorem u12791 : Upper (D 6) (R 6) [10,33,160,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12792 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 268 82 36 81 209 337), lower := (rows 11 35 164 268 82 36 64 128 256), losses := [] }

theorem u12792 : Upper (D 6) (R 6) [10,33,160,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12793 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 164 268 82 48 69 197 325), lower := (rows 11 35 164 268 82 48 64 128 256), losses := [] }

theorem u12793 : Upper (D 6) (R 6) [10,33,160,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12793 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12794 : Route 9 := (fun mask => (mask,id))

def c12794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12794 : Upper (D 6) (R 6) [10,33,160,260,66,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,66,64] 13 (by decide) (choices 1) [1,4,16] r12794 c12794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2537
  · exact u2538
  · exact u2539

def b12795 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 268 84 33 82 210 338), lower := (rows 11 35 164 268 84 33 64 128 256), losses := [] }

theorem u12795 : Upper (D 6) (R 6) [10,33,160,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12796 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 268 84 34 81 209 337), lower := (rows 11 35 164 268 84 34 64 128 256), losses := [] }

theorem u12796 : Upper (D 6) (R 6) [10,33,160,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12797 : Route 9 := (fun mask => (mask,id))

def c12797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12797 : Upper (D 6) (R 6) [10,33,160,260,68,16] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,68,16] 13 (by decide) (choices 1) [1,2] r12797 c12797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2540
  · exact u2541

def r12798 : Route 9 := (fun mask => (mask,id))

def c12798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12798 : Upper (D 6) (R 6) [10,33,160,260,68,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,260,68,64] 13 (by decide) (choices 1) [1,2,16] r12798 c12798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2542
  · exact u2543
  · exact u2544

def b12799 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 280 21 34 68 196 324), lower := (rows 11 35 164 280 21 34 64 128 256), losses := [] }

theorem u12799 : Upper (D 6) (R 6) [10,33,160,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12800 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 280 21 36 66 194 322), lower := (rows 11 35 164 280 21 36 64 128 256), losses := [] }

theorem u12800 : Upper (D 6) (R 6) [10,33,160,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12801 : Route 9 := (fun mask => (mask,id))

def c12801 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12801 : Upper (D 6) (R 6) [10,33,160,272,5,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,272,5,64] 13 (by decide) (choices 1) [2,4] r12801 c12801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2545
  · exact u2546

def b12802 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 280 81 34 68 196 324), lower := (rows 11 35 164 280 81 34 64 128 256), losses := [] }

theorem u12802 : Upper (D 6) (R 6) [10,33,160,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12803 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 280 81 36 70 198 326), lower := (rows 11 35 164 280 81 36 64 128 256), losses := [] }

theorem u12803 : Upper (D 6) (R 6) [10,33,160,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12804 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 228, targets := 1 },{ cop := 1, region := 132, targets := 64 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(2,6)], upper := (rows 11 35 164 280 81 96 70 134 262), lower := (rows 11 35 164 280 81 96 64 128 256), losses := [] }

theorem u12804 : Upper (D 6) (R 6) [10,33,160,272,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12805 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 280 82 33 68 196 324), lower := (rows 11 35 164 280 82 33 64 128 256), losses := [] }

theorem u12805 : Upper (D 6) (R 6) [10,33,160,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12806 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 280 82 36 69 197 325), lower := (rows 11 35 164 280 82 36 64 128 256), losses := [] }

theorem u12806 : Upper (D 6) (R 6) [10,33,160,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12807 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 35 164 280 82 96 69 133 261), lower := (rows 11 35 164 280 82 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 115 67 131 259), good := (rows 493 485 164 316 508 96 96 128 256) }] }

theorem u12807 : Upper (D 6) (R 6) [10,33,160,272,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12808 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 280 84 33 70 198 326), lower := (rows 11 35 164 280 84 33 64 128 256), losses := [] }

theorem u12808 : Upper (D 6) (R 6) [10,33,160,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12809 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 280 84 34 69 197 325), lower := (rows 11 35 164 280 84 34 64 128 256), losses := [] }

theorem u12809 : Upper (D 6) (R 6) [10,33,160,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12810 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 280 84 36 67 195 323), lower := (rows 11 35 164 280 84 36 64 128 256), losses := [] }

theorem u12810 : Upper (D 6) (R 6) [10,33,160,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12811 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 132, targets := 64 }], pairs := [(0,2),(1,2),(2,6)], upper := (rows 11 35 164 280 84 96 71 135 263), lower := (rows 11 35 164 280 84 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 112 64 128 256), good := (rows 11 35 160 315 112 96 96 128 256) }] }

theorem u12811 : Upper (D 6) (R 6) [10,33,160,272,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12812 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 328 21 34 84 212 340), lower := (rows 11 35 164 328 21 34 64 128 256), losses := [] }

theorem u12812 : Upper (D 6) (R 6) [10,33,160,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12813 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 328 21 36 82 210 338), lower := (rows 11 35 164 328 21 36 64 128 256), losses := [] }

theorem u12813 : Upper (D 6) (R 6) [10,33,160,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12814 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 164 328 21 48 70 198 326), lower := (rows 11 35 164 328 21 48 64 128 256), losses := [] }

theorem u12814 : Upper (D 6) (R 6) [10,33,160,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12814 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12815 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 328 21 96 86 150 278), lower := (rows 11 35 164 328 21 96 64 128 256), losses := [] }

theorem u12815 : Upper (D 6) (R 6) [10,33,160,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12816 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 328 22 33 84 212 340), lower := (rows 11 35 164 328 22 33 64 128 256), losses := [] }

theorem u12816 : Upper (D 6) (R 6) [10,33,160,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12817 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 164 328 22 36 81 209 337), lower := (rows 11 35 164 328 22 36 64 128 256), losses := [] }

theorem u12817 : Upper (D 6) (R 6) [10,33,160,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12818 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 164 328 22 48 69 197 325), lower := (rows 11 35 164 328 22 48 64 128 256), losses := [] }

theorem u12818 : Upper (D 6) (R 6) [10,33,160,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12818 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12819 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 328 22 96 85 149 277), lower := (rows 11 35 164 328 22 96 64 128 256), losses := [] }

theorem u12819 : Upper (D 6) (R 6) [10,33,160,320,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12820 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 164 328 81 34 84 148 276), lower := (rows 11 35 164 328 81 34 64 128 256), losses := [] }

theorem u12820 : Upper (D 6) (R 6) [10,33,160,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12821 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 328 81 36 86 150 278), lower := (rows 11 35 164 328 81 36 64 128 256), losses := [] }

theorem u12821 : Upper (D 6) (R 6) [10,33,160,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12822 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 164 328 81 48 70 134 262), lower := (rows 11 35 164 328 81 48 64 128 256), losses := [] }

theorem u12822 : Upper (D 6) (R 6) [10,33,160,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12822 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12823 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 164 328 82 33 84 148 276), lower := (rows 11 35 164 328 82 33 64 128 256), losses := [] }

theorem u12823 : Upper (D 6) (R 6) [10,33,160,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12824 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 328 82 36 85 149 277), lower := (rows 11 35 164 328 82 36 64 128 256), losses := [] }

theorem u12824 : Upper (D 6) (R 6) [10,33,160,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12825 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 164 328 82 48 69 133 261), lower := (rows 11 35 164 328 82 48 64 128 256), losses := [] }

theorem u12825 : Upper (D 6) (R 6) [10,33,160,320,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12825 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12826 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 328 84 33 86 150 278), lower := (rows 11 35 164 328 84 33 64 128 256), losses := [] }

theorem u12826 : Upper (D 6) (R 6) [10,33,160,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12827 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 328 84 34 85 149 277), lower := (rows 11 35 164 328 84 34 64 128 256), losses := [] }

theorem u12827 : Upper (D 6) (R 6) [10,33,160,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12828 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 328 84 36 83 147 275), lower := (rows 11 35 164 328 84 36 64 128 256), losses := [] }

theorem u12828 : Upper (D 6) (R 6) [10,33,160,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12829 : Route 9 := (fun mask => (mask,id))

def c12829 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12829 : Upper (D 6) (R 6) [10,33,160,320,68,16] 13 := by
  apply FastRouting.sound _ _ [10,33,160,320,68,16] 13 (by decide) (choices 1) [1,2,4] r12829 c12829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2547
  · exact u2548
  · exact u2549

def b12830 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 13 112 34 340 404 276), lower := (rows 11 35 196 13 112 34 64 128 256), losses := [] }

theorem u12830 : Upper (D 6) (R 6) [10,33,192,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12831 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 196 13 112 36 338 402 274), lower := (rows 11 35 196 13 112 36 64 128 256), losses := [] }

theorem u12831 : Upper (D 6) (R 6) [10,33,192,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12832 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 196 13 112 48 326 390 262), lower := (rows 11 35 196 13 112 48 64 128 256), losses := [] }

theorem u12832 : Upper (D 6) (R 6) [10,33,192,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12832 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12833 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 196 13 112 288 86 150 278), lower := (rows 11 35 196 13 112 288 64 128 256), losses := [] }

theorem u12833 : Upper (D 6) (R 6) [10,33,192,5,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12833 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12834 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 13 276 34 112 240 368), lower := (rows 11 35 196 13 276 34 64 128 256), losses := [] }

theorem u12834 : Upper (D 6) (R 6) [10,33,192,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12835 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 196 13 276 48 98 226 354), lower := (rows 11 35 196 13 276 48 64 128 256), losses := [] }

theorem u12835 : Upper (D 6) (R 6) [10,33,192,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12835 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12836 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 196 13 276 96 114 178 306), lower := (rows 11 35 196 13 276 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 100 64 128 256), good := (rows 11 35 224 43 304 96 96 128 256) }] }

theorem u12836 : Upper (D 6) (R 6) [10,33,192,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12837 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 13 304 34 84 212 340), lower := (rows 11 35 196 13 304 34 64 128 256), losses := [] }

theorem u12837 : Upper (D 6) (R 6) [10,33,192,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12838 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 196 13 304 36 82 210 338), lower := (rows 11 35 196 13 304 36 64 128 256), losses := [] }

theorem u12838 : Upper (D 6) (R 6) [10,33,192,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12839 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 196 13 304 48 70 198 326), lower := (rows 11 35 196 13 304 48 64 128 256), losses := [] }

theorem u12839 : Upper (D 6) (R 6) [10,33,192,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12839 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12839
end Delivery.IrregularNine14.P06
