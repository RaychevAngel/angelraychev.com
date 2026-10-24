import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0258
import IrregularNine14P06C0259
import IrregularNine14P06C0260

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32820 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 268 19 100 100 228 356), lower := (rows 11 131 52 268 19 32 64 128 256), losses := [] }

theorem u32820 : Upper (D 6) (R 6) [10,129,48,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32821 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 52 268 21 98 98 226 354), lower := (rows 11 131 52 268 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 490 482 60 268 508 32 64 128 256) }] }

theorem u32821 : Upper (D 6) (R 6) [10,129,48,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32822 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 131 52 268 22 97 97 225 353), lower := (rows 11 131 52 268 22 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 489 481 60 268 508 32 64 128 256) }] }

theorem u32822 : Upper (D 6) (R 6) [10,129,48,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32823 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 268 49 102 70 198 326), lower := (rows 11 131 52 268 49 32 64 128 256), losses := [] }

theorem u32823 : Upper (D 6) (R 6) [10,129,48,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32824 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 268 50 101 69 197 325), lower := (rows 11 131 52 268 50 32 64 128 256), losses := [] }

theorem u32824 : Upper (D 6) (R 6) [10,129,48,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32825 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 268 52 99 67 195 323), lower := (rows 11 131 52 268 52 32 64 128 256), losses := [] }

theorem u32825 : Upper (D 6) (R 6) [10,129,48,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32826 : Route 9 := (fun mask => (mask,id))

def c32826 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32826 : Upper (D 6) (R 6) [10,129,48,260,65] 13 := by
  apply FastRouting.sound _ _ [10,129,48,260,65] 13 (by decide) (choices 1) [2,4,64] r32826 c32826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15531
  · exact u15532
  · exact u15533

def r32827 : Route 9 := (fun mask => (mask,id))

def c32827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32827 : Upper (D 6) (R 6) [10,129,48,260,66] 13 := by
  apply FastRouting.sound _ _ [10,129,48,260,66] 13 (by decide) (choices 1) [1,4,64] r32827 c32827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15534
  · exact u15535
  · exact u15536

def r32828 : Route 9 := (fun mask => (mask,id))

def c32828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32828 : Upper (D 6) (R 6) [10,129,48,260,68] 13 := by
  apply FastRouting.sound _ _ [10,129,48,260,68] 13 (by decide) (choices 1) [1,2,64] r32828 c32828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15537
  · exact u15538
  · exact u15539

def b32829 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 268 112 103 71 199 327), lower := (rows 11 131 52 268 112 32 64 128 256), losses := [] }

theorem u32829 : Upper (D 6) (R 6) [10,129,48,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32830 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 296 19 100 68 196 324), lower := (rows 11 131 52 296 19 32 64 128 256), losses := [] }

theorem u32830 : Upper (D 6) (R 6) [10,129,48,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32831 : Route 9 := (fun mask => (mask,id))

def c32831 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32831 : Upper (D 6) (R 6) [10,129,48,288,5] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288,5] 13 (by decide) (choices 1) [2,4,64] r32831 c32831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15540
  · exact u15541
  · exact u15542

def r32832 : Route 9 := (fun mask => (mask,id))

def c32832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32832 : Upper (D 6) (R 6) [10,129,48,288,6] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288,6] 13 (by decide) (choices 1) [1,4,64] r32832 c32832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15543
  · exact u15544
  · exact u15545

def r32833 : Route 9 := (fun mask => (mask,id))

def c32833 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32833 : Upper (D 6) (R 6) [10,129,48,288,65] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288,65] 13 (by decide) (choices 1) [2,4,64] r32833 c32833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15546
  · exact u15547
  · exact u15548

def r32834 : Route 9 := (fun mask => (mask,id))

def c32834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32834 : Upper (D 6) (R 6) [10,129,48,288,66] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288,66] 13 (by decide) (choices 1) [1,4,64] r32834 c32834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15549
  · exact u15550
  · exact u15551

def r32835 : Route 9 := (fun mask => (mask,id))

def c32835 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32835 : Upper (D 6) (R 6) [10,129,48,288,68] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288,68] 13 (by decide) (choices 1) [1,2,4,64] r32835 c32835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15552
  · exact u15553
  · exact u15554
  · exact u15555

def b32836 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 328 19 100 100 228 356), lower := (rows 11 131 52 328 19 32 64 128 256), losses := [] }

theorem u32836 : Upper (D 6) (R 6) [10,129,48,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32837 : Route 9 := (fun mask => (mask,id))

def c32837 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32837 : Upper (D 6) (R 6) [10,129,48,320,5] 13 := by
  apply FastRouting.sound _ _ [10,129,48,320,5] 13 (by decide) (choices 1) [2,4,64] r32837 c32837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15556
  · exact u15557
  · exact u15558

def r32838 : Route 9 := (fun mask => (mask,id))

def c32838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32838 : Upper (D 6) (R 6) [10,129,48,320,6] 13 := by
  apply FastRouting.sound _ _ [10,129,48,320,6] 13 (by decide) (choices 1) [1,4,64] r32838 c32838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15559
  · exact u15560
  · exact u15561

def b32839 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 328 49 102 70 198 326), lower := (rows 11 131 52 328 49 32 64 128 256), losses := [] }

theorem u32839 : Upper (D 6) (R 6) [10,129,48,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32840 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 328 50 101 69 197 325), lower := (rows 11 131 52 328 50 32 64 128 256), losses := [] }

theorem u32840 : Upper (D 6) (R 6) [10,129,48,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32841 : PairBound 9 := { available := 71, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 328 52 103 71 199 327), lower := (rows 11 131 52 328 52 32 64 128 256), losses := [] }

theorem u32841 : Upper (D 6) (R 6) [10,129,48,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32842 : Route 9 := (fun mask => (mask,id))

def c32842 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32842 : Upper (D 6) (R 6) [10,129,48,320,65] 13 := by
  apply FastRouting.sound _ _ [10,129,48,320,65] 13 (by decide) (choices 1) [2,4] r32842 c32842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15562
  · exact u15563

def r32843 : Route 9 := (fun mask => (mask,id))

def c32843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32843 : Upper (D 6) (R 6) [10,129,48,320,66] 13 := by
  apply FastRouting.sound _ _ [10,129,48,320,66] 13 (by decide) (choices 1) [1,4] r32843 c32843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15564
  · exact u15565

def r32844 : Route 9 := (fun mask => (mask,id))

def c32844 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32844 : Upper (D 6) (R 6) [10,129,48,320,68] 13 := by
  apply FastRouting.sound _ _ [10,129,48,320,68] 13 (by decide) (choices 1) [1,2,4] r32844 c32844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15566
  · exact u15567
  · exact u15568

def b32845 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 52 328 112 39 71 135 263), lower := (rows 11 131 52 328 112 32 64 128 256), losses := [] }

theorem u32845 : Upper (D 6) (R 6) [10,129,48,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32846 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 100 13 22 368 368 496 368), lower := (rows 11 131 100 13 22 32 64 128 256), losses := [] }

theorem u32846 : Upper (D 6) (R 6) [10,129,96,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32847 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 13 50 372 340 468 340), lower := (rows 11 131 100 13 50 32 64 128 256), losses := [] }

theorem u32847 : Upper (D 6) (R 6) [10,129,96,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32848 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 100 13 52 370 338 466 338), lower := (rows 11 131 100 13 52 32 64 128 256), losses := [] }

theorem u32848 : Upper (D 6) (R 6) [10,129,96,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32849 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 16, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 100 13 112 310 342 406 278), lower := (rows 11 131 100 13 112 32 64 128 256), losses := [] }

theorem u32849 : Upper (D 6) (R 6) [10,129,96,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32850 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 13 274 116 116 244 372), lower := (rows 11 131 100 13 274 32 64 128 256), losses := [] }

theorem u32850 : Upper (D 6) (R 6) [10,129,96,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32851 : Route 9 := (fun mask => (mask,id))

def c32851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32851 : Upper (D 6) (R 6) [10,129,96,5,260] 13 := by
  apply FastRouting.sound _ _ [10,129,96,5,260] 13 (by decide) (choices 1) [2,16,64] r32851 c32851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15569
  · exact u15570
  · exact u15571

def r32852 : Route 9 := (fun mask => (mask,id))

def c32852 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32852 : Upper (D 6) (R 6) [10,129,96,5,288] 13 := by
  apply FastRouting.sound _ _ [10,129,96,5,288] 13 (by decide) (choices 1) [2,4,16,64] r32852 c32852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15572
  · exact u15573
  · exact u15574
  · exact u15575

def b32853 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 100 25 22 356 356 484 356), lower := (rows 11 131 100 25 22 32 64 128 256), losses := [] }

theorem u32853 : Upper (D 6) (R 6) [10,129,96,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32854 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 100 25 50 356 324 452 324), lower := (rows 11 131 100 25 50 32 64 128 256), losses := [] }

theorem u32854 : Upper (D 6) (R 6) [10,129,96,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32855 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 100 25 52 358 326 454 326), lower := (rows 11 131 100 25 52 32 64 128 256), losses := [] }

theorem u32855 : Upper (D 6) (R 6) [10,129,96,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32856 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 16, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 100 25 112 294 326 390 262), lower := (rows 11 131 100 25 112 32 64 128 256), losses := [] }

theorem u32856 : Upper (D 6) (R 6) [10,129,96,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32857 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 100 25 274 100 100 228 356), lower := (rows 11 131 100 25 274 32 64 128 256), losses := [] }

theorem u32857 : Upper (D 6) (R 6) [10,129,96,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32858 : Route 9 := (fun mask => (mask,id))

def c32858 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32858 : Upper (D 6) (R 6) [10,129,96,17,260] 13 := by
  apply FastRouting.sound _ _ [10,129,96,17,260] 13 (by decide) (choices 1) [2,4,64] r32858 c32858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15576
  · exact u15577
  · exact u15578

def r32859 : Route 9 := (fun mask => (mask,id))

def c32859 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32859 : Upper (D 6) (R 6) [10,129,96,17,288] 13 := by
  apply FastRouting.sound _ _ [10,129,96,17,288] 13 (by decide) (choices 1) [2,4,64] r32859 c32859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15579
  · exact u15580
  · exact u15581

def b32860 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 28 19 356 356 484 356), lower := (rows 11 131 100 28 19 32 64 128 256), losses := [] }

theorem u32860 : Upper (D 6) (R 6) [10,129,96,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32861 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 100 28 21 354 354 482 354), lower := (rows 11 131 100 28 21 32 64 128 256), losses := [] }

theorem u32861 : Upper (D 6) (R 6) [10,129,96,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32862 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 100 28 22 353 353 481 353), lower := (rows 11 131 100 28 22 32 64 128 256), losses := [] }

theorem u32862 : Upper (D 6) (R 6) [10,129,96,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32863 : PairBound 9 := { available := 326, camps := [{ cop := 3, region := 451, targets := 32 },{ cop := 0, region := 356, targets := 1 }], pairs := [(0,5),(1,5),(2,0)], upper := (rows 11 131 100 28 49 358 326 454 326), lower := (rows 11 131 100 28 49 32 64 128 256), losses := [] }

theorem u32863 : Upper (D 6) (R 6) [10,129,96,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32864 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 451, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 11 131 100 28 50 357 325 453 325), lower := (rows 11 131 100 28 50 32 64 128 256), losses := [] }

theorem u32864 : Upper (D 6) (R 6) [10,129,96,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32865 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 100 28 52 355 323 451 323), lower := (rows 11 131 100 28 52 32 64 128 256), losses := [] }

theorem u32865 : Upper (D 6) (R 6) [10,129,96,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32866 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 100 28 112 295 327 391 263), lower := (rows 11 131 100 28 112 32 64 128 256), losses := [] }

theorem u32866 : Upper (D 6) (R 6) [10,129,96,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32867 : Route 9 := (fun mask => (mask,id))

def c32867 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32867 : Upper (D 6) (R 6) [10,129,96,20,257] 13 := by
  apply FastRouting.sound _ _ [10,129,96,20,257] 13 (by decide) (choices 1) [2,4,64] r32867 c32867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15582
  · exact u15583
  · exact u15584

def r32868 : Route 9 := (fun mask => (mask,id))

def c32868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32868 : Upper (D 6) (R 6) [10,129,96,20,258] 13 := by
  apply FastRouting.sound _ _ [10,129,96,20,258] 13 (by decide) (choices 1) [1,4,64] r32868 c32868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15585
  · exact u15586
  · exact u15587

def b32869 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 100 28 276 99 99 227 355), lower := (rows 11 131 100 28 276 32 64 128 256), losses := [] }

theorem u32869 : Upper (D 6) (R 6) [10,129,96,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32870 : Route 9 := (fun mask => (mask,id))

def c32870 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32870 : Upper (D 6) (R 6) [10,129,96,20,288] 13 := by
  apply FastRouting.sound _ _ [10,129,96,20,288] 13 (by decide) (choices 1) [1,2,4,64] r32870 c32870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15588
  · exact u15589
  · exact u15590
  · exact u15591

def b32871 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 41 22 372 340 468 340), lower := (rows 11 131 100 41 22 32 64 128 256), losses := [] }

theorem u32871 : Upper (D 6) (R 6) [10,129,96,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32872 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 41 82 308 340 404 276), lower := (rows 11 131 100 41 82 32 64 128 256), losses := [] }

theorem u32872 : Upper (D 6) (R 6) [10,129,96,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32873 : PairBound 9 := { available := 278, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 131 100 41 84 310 342 406 278), lower := (rows 11 131 100 41 84 32 64 128 256), losses := [] }

theorem u32873 : Upper (D 6) (R 6) [10,129,96,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32874 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 41 274 116 84 212 340), lower := (rows 11 131 100 41 274 32 64 128 256), losses := [] }

theorem u32874 : Upper (D 6) (R 6) [10,129,96,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32875 : Route 9 := (fun mask => (mask,id))

def c32875 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32875 : Upper (D 6) (R 6) [10,129,96,33,260] 13 := by
  apply FastRouting.sound _ _ [10,129,96,33,260] 13 (by decide) (choices 1) [2,4,16,64] r32875 c32875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15592
  · exact u15593
  · exact u15594
  · exact u15595

def r32876 : Route 9 := (fun mask => (mask,id))

def c32876 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32876 : Upper (D 6) (R 6) [10,129,96,33,320] 13 := by
  apply FastRouting.sound _ _ [10,129,96,33,320] 13 (by decide) (choices 1) [2,4,16] r32876 c32876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15596
  · exact u15597
  · exact u15598

def b32877 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 56 19 356 324 452 324), lower := (rows 11 131 100 56 19 32 64 128 256), losses := [] }

theorem u32877 : Upper (D 6) (R 6) [10,129,96,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32878 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 356, targets := 1 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 11 131 100 56 21 358 326 454 326), lower := (rows 11 131 100 56 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 494 486 100 60 508 32 64 128 256) }] }

theorem u32878 : Upper (D 6) (R 6) [10,129,96,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32879 : Route 9 := (fun mask => (mask,id))

def c32879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32879 : Upper (D 6) (R 6) [10,129,96,48,6] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,6] 13 (by decide) (choices 1) [1,4,64,256] r32879 c32879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15599
  · exact u15600
  · exact u15601
  · exact u15602

#print axioms u32879
end Delivery.IrregularNine14.P06
