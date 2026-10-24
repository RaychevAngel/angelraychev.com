import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0441
import IrregularNine14P06C0442
import IrregularNine14P06C0443

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39840 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 32 },{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(1,5),(3,5)], upper := (rows 41 131 292 14 21 114 82 210 338), lower := (rows 41 131 292 14 21 32 64 128 256), losses := [] }

theorem u39840 : Upper (D 6) (R 6) [40,129,288,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39841 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 131 292 14 22 113 81 209 337), lower := (rows 41 131 292 14 22 32 64 128 256), losses := [] }

theorem u39841 : Upper (D 6) (R 6) [40,129,288,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39842 : Route 9 := (fun mask => (mask,id))

def c39842 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39842 : Upper (D 6) (R 6) [40,129,288,6,65] 13 := by
  apply FastRouting.sound _ _ [40,129,288,6,65] 13 (by decide) (choices 1) [2,4,16,64] r39842 c39842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26507
  · exact u26508
  · exact u26509
  · exact u26510

def r39843 : Route 9 := (fun mask => (mask,id))

def c39843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39843 : Upper (D 6) (R 6) [40,129,288,6,66] 13 := by
  apply FastRouting.sound _ _ [40,129,288,6,66] 13 (by decide) (choices 1) [1,4,16,64] r39843 c39843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26511
  · exact u26512
  · exact u26513
  · exact u26514

def r39844 : Route 9 := (fun mask => (mask,id))

def c39844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39844 : Upper (D 6) (R 6) [40,129,288,6,68] 13 := by
  apply FastRouting.sound _ _ [40,129,288,6,68] 13 (by decide) (choices 1) [1,2,16,64] r39844 c39844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26515
  · exact u26516
  · exact u26517
  · exact u26518

def b39845 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 41 131 292 25 22 102 70 198 326), lower := (rows 41 131 292 25 22 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 16 0 80 144 272), good := (rows 11 131 260 475 470 0 64 128 256) }] }

theorem u39845 : Upper (D 6) (R 6) [40,129,288,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39846 : Route 9 := (fun mask => (mask,id))

def c39846 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39846 : Upper (D 6) (R 6) [40,129,288,17,66] 13 := by
  apply FastRouting.sound _ _ [40,129,288,17,66] 13 (by decide) (choices 1) [2,4,64] r39846 c39846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26519
  · exact u26520
  · exact u26521

def r39847 : Route 9 := (fun mask => (mask,id))

def c39847 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39847 : Upper (D 6) (R 6) [40,129,288,17,68] 13 := by
  apply FastRouting.sound _ _ [40,129,288,17,68] 13 (by decide) (choices 1) [2,4,64] r39847 c39847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26522
  · exact u26523
  · exact u26524

def b39848 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 41 131 292 26 19 100 68 196 324), lower := (rows 41 131 292 26 19 32 64 128 256), losses := [] }

theorem u39848 : Upper (D 6) (R 6) [40,129,288,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39849 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 32 },{ cop := 1, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(3,5)], upper := (rows 41 131 292 26 21 102 70 198 326), lower := (rows 41 131 292 26 21 32 64 128 256), losses := [] }

theorem u39849 : Upper (D 6) (R 6) [40,129,288,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39850 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 131 292 26 22 101 69 197 325), lower := (rows 41 131 292 26 22 32 64 128 256), losses := [] }

theorem u39850 : Upper (D 6) (R 6) [40,129,288,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39851 : Route 9 := (fun mask => (mask,id))

def c39851 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39851 : Upper (D 6) (R 6) [40,129,288,18,65] 13 := by
  apply FastRouting.sound _ _ [40,129,288,18,65] 13 (by decide) (choices 1) [2,4,64] r39851 c39851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26525
  · exact u26526
  · exact u26527

def b39852 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 131 292 26 82 101 69 197 325), lower := (rows 41 131 292 26 82 32 64 128 256), losses := [] }

theorem u39852 : Upper (D 6) (R 6) [40,129,288,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39853 : Route 9 := (fun mask => (mask,id))

def c39853 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39853 : Upper (D 6) (R 6) [40,129,288,18,68] 13 := by
  apply FastRouting.sound _ _ [40,129,288,18,68] 13 (by decide) (choices 1) [1,2,4,64] r39853 c39853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26528
  · exact u26529
  · exact u26530
  · exact u26531

def b39854 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 292 28 19 102 70 198 326), lower := (rows 41 131 292 28 19 32 64 128 256), losses := [] }

theorem u39854 : Upper (D 6) (R 6) [40,129,288,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39855 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 25, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 292 28 21 98 66 194 322), lower := (rows 41 131 292 28 21 32 64 128 256), losses := [] }

theorem u39855 : Upper (D 6) (R 6) [40,129,288,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39856 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 292 28 22 99 67 195 323), lower := (rows 41 131 292 28 22 32 64 128 256), losses := [] }

theorem u39856 : Upper (D 6) (R 6) [40,129,288,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39857 : Route 9 := (fun mask => (mask,id))

def c39857 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39857 : Upper (D 6) (R 6) [40,129,288,20,65] 13 := by
  apply FastRouting.sound _ _ [40,129,288,20,65] 13 (by decide) (choices 1) [2,4,64] r39857 c39857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26532
  · exact u26533
  · exact u26534

def r39858 : Route 9 := (fun mask => (mask,id))

def c39858 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39858 : Upper (D 6) (R 6) [40,129,288,20,66] 13 := by
  apply FastRouting.sound _ _ [40,129,288,20,66] 13 (by decide) (choices 1) [1,2,4,64] r39858 c39858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26535
  · exact u26536
  · exact u26537
  · exact u26538

def b39859 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 131 292 28 84 99 67 195 323), lower := (rows 41 131 292 28 84 32 64 128 256), losses := [] }

theorem u39859 : Upper (D 6) (R 6) [40,129,288,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39860 : Route 9 := (fun mask => (mask,id))

def c39860 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39860 : Upper (D 6) (R 6) [40,129,288,65,6] 13 := by
  apply FastRouting.sound _ _ [40,129,288,65,6] 13 (by decide) (choices 1) [2,4,16,64] r39860 c39860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26539
  · exact u26540
  · exact u26541
  · exact u26542

def b39861 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 64 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 41 131 292 73 82 54 86 150 278), lower := (rows 41 131 292 73 82 32 64 128 256), losses := [] }

theorem u39861 : Upper (D 6) (R 6) [40,129,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39862 : Route 9 := (fun mask => (mask,id))

def c39862 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39862 : Upper (D 6) (R 6) [40,129,288,65,68] 13 := by
  apply FastRouting.sound _ _ [40,129,288,65,68] 13 (by decide) (choices 1) [2,4,16] r39862 c39862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26543
  · exact u26544
  · exact u26545

def b39863 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 292 74 19 116 84 212 340), lower := (rows 41 131 292 74 19 32 64 128 256), losses := [] }

theorem u39863 : Upper (D 6) (R 6) [40,129,288,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39864 : Route 9 := (fun mask => (mask,id))

def c39864 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39864 : Upper (D 6) (R 6) [40,129,288,66,5] 13 := by
  apply FastRouting.sound _ _ [40,129,288,66,5] 13 (by decide) (choices 1) [2,4,16,64] r39864 c39864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26546
  · exact u26547
  · exact u26548
  · exact u26549

def r39865 : Route 9 := (fun mask => (mask,id))

def c39865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39865 : Upper (D 6) (R 6) [40,129,288,66,6] 13 := by
  apply FastRouting.sound _ _ [40,129,288,66,6] 13 (by decide) (choices 1) [1,4,16,64] r39865 c39865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26550
  · exact u26551
  · exact u26552
  · exact u26553

def r39866 : Route 9 := (fun mask => (mask,id))

def c39866 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39866 : Upper (D 6) (R 6) [40,129,288,66,65] 13 := by
  apply FastRouting.sound _ _ [40,129,288,66,65] 13 (by decide) (choices 1) [2,4,16] r39866 c39866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26554
  · exact u26555
  · exact u26556

def b39867 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 131 292 74 82 53 85 149 277), lower := (rows 41 131 292 74 82 32 64 128 256), losses := [] }

theorem u39867 : Upper (D 6) (R 6) [40,129,288,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39868 : Route 9 := (fun mask => (mask,id))

def c39868 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39868 : Upper (D 6) (R 6) [40,129,288,66,68] 13 := by
  apply FastRouting.sound _ _ [40,129,288,66,68] 13 (by decide) (choices 1) [1,2,4,16] r39868 c39868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26557
  · exact u26558
  · exact u26559
  · exact u26560

def b39869 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 292 76 19 118 86 214 342), lower := (rows 41 131 292 76 19 32 64 128 256), losses := [] }

theorem u39869 : Upper (D 6) (R 6) [40,129,288,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39870 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 32 },{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(1,5),(3,5)], upper := (rows 41 131 292 76 21 114 82 210 338), lower := (rows 41 131 292 76 21 32 64 128 256), losses := [] }

theorem u39870 : Upper (D 6) (R 6) [40,129,288,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39871 : Route 9 := (fun mask => (mask,id))

def c39871 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39871 : Upper (D 6) (R 6) [40,129,288,68,6] 13 := by
  apply FastRouting.sound _ _ [40,129,288,68,6] 13 (by decide) (choices 1) [1,2,16,64] r39871 c39871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26561
  · exact u26562
  · exact u26563
  · exact u26564

def r39872 : Route 9 := (fun mask => (mask,id))

def c39872 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39872 : Upper (D 6) (R 6) [40,129,288,68,65] 13 := by
  apply FastRouting.sound _ _ [40,129,288,68,65] 13 (by decide) (choices 1) [2,4,16] r39872 c39872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26565
  · exact u26566
  · exact u26567

def r39873 : Route 9 := (fun mask => (mask,id))

def c39873 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39873 : Upper (D 6) (R 6) [40,129,288,68,66] 13 := by
  apply FastRouting.sound _ _ [40,129,288,68,66] 13 (by decide) (choices 1) [1,2,4,16] r39873 c39873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26568
  · exact u26569
  · exact u26570
  · exact u26571

def b39874 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 131 292 76 84 51 83 147 275), lower := (rows 41 131 292 76 84 32 64 128 256), losses := [] }

theorem u39874 : Upper (D 6) (R 6) [40,129,288,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39875 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 292 88 19 102 70 198 326), lower := (rows 41 131 292 88 19 32 64 128 256), losses := [] }

theorem u39875 : Upper (D 6) (R 6) [40,129,288,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39876 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 32 },{ cop := 1, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(3,5)], upper := (rows 41 131 292 88 21 102 70 198 326), lower := (rows 41 131 292 88 21 32 64 128 256), losses := [] }

theorem u39876 : Upper (D 6) (R 6) [40,129,288,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39877 : Route 9 := (fun mask => (mask,id))

def c39877 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39877 : Upper (D 6) (R 6) [40,129,288,80,6] 13 := by
  apply FastRouting.sound _ _ [40,129,288,80,6] 13 (by decide) (choices 1) [1,2,4,64] r39877 c39877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26572
  · exact u26573
  · exact u26574
  · exact u26575

def b39878 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 131 292 88 81 38 70 134 262), lower := (rows 41 131 292 88 81 32 64 128 256), losses := [] }

theorem u39878 : Upper (D 6) (R 6) [40,129,288,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39879 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 131 292 88 82 39 71 135 263), lower := (rows 41 131 292 88 82 32 64 128 256), losses := [] }

theorem u39879 : Upper (D 6) (R 6) [40,129,288,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39880 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 131 292 88 84 39 71 135 263), lower := (rows 41 131 292 88 84 32 64 128 256), losses := [] }

theorem u39880 : Upper (D 6) (R 6) [40,129,288,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39881 : Route 9 := (fun mask => (mask,id))

def c39881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39881 : Upper (D 6) (R 6) [40,129,320,5,6] 13 := by
  apply FastRouting.sound _ _ [40,129,320,5,6] 13 (by decide) (choices 1) [2,16,64] r39881 c39881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26576
  · exact u26577
  · exact u26578

def b39882 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 131 324 13 50 118 86 214 342), lower := (rows 41 131 324 13 50 32 64 128 256), losses := [] }

theorem u39882 : Upper (D 6) (R 6) [40,129,320,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39883 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 324 13 52 114 82 210 338), lower := (rows 41 131 324 13 52 32 64 128 256), losses := [] }

theorem u39883 : Upper (D 6) (R 6) [40,129,320,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39884 : Route 9 := (fun mask => (mask,id))

def c39884 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39884 : Upper (D 6) (R 6) [40,129,320,5,66] 13 := by
  apply FastRouting.sound _ _ [40,129,320,5,66] 13 (by decide) (choices 1) [2,4,16] r39884 c39884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26579
  · exact u26580
  · exact u26581

def b39885 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 131 324 13 84 50 114 178 306), lower := (rows 41 131 324 13 84 32 64 128 256), losses := [] }

theorem u39885 : Upper (D 6) (R 6) [40,129,320,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39886 : Route 9 := (fun mask => (mask,id))

def c39886 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39886 : Upper (D 6) (R 6) [40,129,320,5,96] 13 := by
  apply FastRouting.sound _ _ [40,129,320,5,96] 13 (by decide) (choices 1) [2,4,16] r39886 c39886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26582
  · exact u26583
  · exact u26584

def b39887 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 131 324 14 19 116 116 244 372), lower := (rows 41 131 324 14 19 32 64 128 256), losses := [] }

theorem u39887 : Upper (D 6) (R 6) [40,129,320,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39888 : Route 9 := (fun mask => (mask,id))

def c39888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39888 : Upper (D 6) (R 6) [40,129,320,6,5] 13 := by
  apply FastRouting.sound _ _ [40,129,320,6,5] 13 (by decide) (choices 1) [2,16,64] r39888 c39888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26585
  · exact u26586
  · exact u26587

def b39889 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 131 324 14 22 113 113 241 369), lower := (rows 41 131 324 14 22 32 64 128 256), losses := [] }

theorem u39889 : Upper (D 6) (R 6) [40,129,320,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39890 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 131 324 14 49 118 86 214 342), lower := (rows 41 131 324 14 49 32 64 128 256), losses := [] }

theorem u39890 : Upper (D 6) (R 6) [40,129,320,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39891 : Route 9 := (fun mask => (mask,id))

def c39891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39891 : Upper (D 6) (R 6) [40,129,320,6,34] 13 := by
  apply FastRouting.sound _ _ [40,129,320,6,34] 13 (by decide) (choices 1) [1,4,16,64] r39891 c39891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26588
  · exact u26589
  · exact u26590
  · exact u26591

def r39892 : Route 9 := (fun mask => (mask,id))

def c39892 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39892 : Upper (D 6) (R 6) [40,129,320,6,36] 13 := by
  apply FastRouting.sound _ _ [40,129,320,6,36] 13 (by decide) (choices 1) [1,2,16,64] r39892 c39892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26592
  · exact u26593
  · exact u26594
  · exact u26595

def r39893 : Route 9 := (fun mask => (mask,id))

def c39893 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39893 : Upper (D 6) (R 6) [40,129,320,6,65] 13 := by
  apply FastRouting.sound _ _ [40,129,320,6,65] 13 (by decide) (choices 1) [2,4,16] r39893 c39893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26596
  · exact u26597
  · exact u26598

def r39894 : Route 9 := (fun mask => (mask,id))

def c39894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39894 : Upper (D 6) (R 6) [40,129,320,6,66] 13 := by
  apply FastRouting.sound _ _ [40,129,320,6,66] 13 (by decide) (choices 1) [1,4,16] r39894 c39894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26599
  · exact u26600
  · exact u26601

def b39895 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 131 324 14 84 51 115 179 307), lower := (rows 41 131 324 14 84 32 64 128 256), losses := [] }

theorem u39895 : Upper (D 6) (R 6) [40,129,320,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39896 : Route 9 := (fun mask => (mask,id))

def c39896 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39896 : Upper (D 6) (R 6) [40,129,320,6,96] 13 := by
  apply FastRouting.sound _ _ [40,129,320,6,96] 13 (by decide) (choices 1) [1,2,4,16] r39896 c39896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26602
  · exact u26603
  · exact u26604
  · exact u26605

def r39897 : Route 9 := (fun mask => (mask,id))

def c39897 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39897 : Upper (D 6) (R 6) [40,129,320,17,6] 13 := by
  apply FastRouting.sound _ _ [40,129,320,17,6] 13 (by decide) (choices 1) [2,4,64] r39897 c39897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26606
  · exact u26607
  · exact u26608

def b39898 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 25 50 102 70 198 326), lower := (rows 41 131 324 25 50 32 64 128 256), losses := [] }

theorem u39898 : Upper (D 6) (R 6) [40,129,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39899 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 324 25 52 102 70 198 326), lower := (rows 41 131 324 25 52 32 64 128 256), losses := [] }

theorem u39899 : Upper (D 6) (R 6) [40,129,320,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39899
end Delivery.IrregularNine14.P06
