import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0210
import IrregularNine14P06C0211
import IrregularNine14P06C0212
import IrregularNine14P06C0213

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30840 : Route 9 := (fun mask => (mask,id))

def c30840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30840 : Upper (D 6) (R 6) [10,33,144,260,36] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,36] 13 (by decide) (choices 1) [1,2,64] r30840 c30840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12656
  · exact u12657
  · exact u12658

def r30841 : Route 9 := (fun mask => (mask,id))

def c30841 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30841 : Upper (D 6) (R 6) [10,33,144,260,65] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,65] 13 (by decide) (choices 1) [2,4,64] r30841 c30841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12659
  · exact u12660
  · exact u12661

def r30842 : Route 9 := (fun mask => (mask,id))

def c30842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30842 : Upper (D 6) (R 6) [10,33,144,260,66] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,66] 13 (by decide) (choices 1) [1,4,64] r30842 c30842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12662
  · exact u12663
  · exact u12664

def r30843 : Route 9 := (fun mask => (mask,id))

def c30843 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30843 : Upper (D 6) (R 6) [10,33,144,260,68] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,68] 13 (by decide) (choices 1) [1,2,64] r30843 c30843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12665
  · exact u12666
  · exact u12667

def r30844 : Route 9 := (fun mask => (mask,id))

def c30844 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30844 : Upper (D 6) (R 6) [10,33,144,260,96] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,96] 13 (by decide) (choices 1) [1,2,4,64] r30844 c30844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12668
  · exact u12669
  · exact u12670
  · exact u12671

def b30845 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 148 328 19 100 100 228 356), lower := (rows 11 35 148 328 19 32 64 128 256), losses := [] }

theorem u30845 : Upper (D 6) (R 6) [10,33,144,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30846 : Route 9 := (fun mask => (mask,id))

def c30846 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30846 : Upper (D 6) (R 6) [10,33,144,320,5] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,5] 13 (by decide) (choices 1) [2,4,64] r30846 c30846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12672
  · exact u12673
  · exact u12674

def r30847 : Route 9 := (fun mask => (mask,id))

def c30847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30847 : Upper (D 6) (R 6) [10,33,144,320,6] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,6] 13 (by decide) (choices 1) [1,4,64] r30847 c30847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12675
  · exact u12676
  · exact u12677

def b30848 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 148 328 49 102 70 198 326), lower := (rows 11 35 148 328 49 32 64 128 256), losses := [] }

theorem u30848 : Upper (D 6) (R 6) [10,33,144,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30849 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 148 328 50 101 69 197 325), lower := (rows 11 35 148 328 50 32 64 128 256), losses := [] }

theorem u30849 : Upper (D 6) (R 6) [10,33,144,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30850 : Route 9 := (fun mask => (mask,id))

def c30850 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30850 : Upper (D 6) (R 6) [10,33,144,320,36] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,36] 13 (by decide) (choices 1) [1,2,4,64] r30850 c30850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12678
  · exact u12679
  · exact u12680
  · exact u12681

def r30851 : Route 9 := (fun mask => (mask,id))

def c30851 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30851 : Upper (D 6) (R 6) [10,33,144,320,65] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,65] 13 (by decide) (choices 1) [2,4] r30851 c30851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12682
  · exact u12683

def r30852 : Route 9 := (fun mask => (mask,id))

def c30852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30852 : Upper (D 6) (R 6) [10,33,144,320,66] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,66] 13 (by decide) (choices 1) [1,4] r30852 c30852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12684
  · exact u12685

def r30853 : Route 9 := (fun mask => (mask,id))

def c30853 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30853 : Upper (D 6) (R 6) [10,33,144,320,68] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,68] 13 (by decide) (choices 1) [1,2,4] r30853 c30853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12686
  · exact u12687
  · exact u12688

def r30854 : Route 9 := (fun mask => (mask,id))

def c30854 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30854 : Upper (D 6) (R 6) [10,33,144,320,96] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,96] 13 (by decide) (choices 1) [1,2,4] r30854 c30854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12689
  · exact u12690
  · exact u12691

def b30855 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 164 25 22 356 324 452 324), lower := (rows 11 35 164 25 22 32 64 128 256), losses := [] }

theorem u30855 : Upper (D 6) (R 6) [10,33,160,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30856 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 164 25 82 356 324 452 324), lower := (rows 11 35 164 25 82 32 64 128 256), losses := [] }

theorem u30856 : Upper (D 6) (R 6) [10,33,160,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30857 : Route 9 := (fun mask => (mask,id))

def c30857 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30857 : Upper (D 6) (R 6) [10,33,160,17,68] 13 := by
  apply FastRouting.sound _ _ [10,33,160,17,68] 13 (by decide) (choices 1) [2,4,64,256] r30857 c30857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12692
  · exact u12693
  · exact u12694
  · exact u12695

def b30858 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 164 25 274 100 68 196 324), lower := (rows 11 35 164 25 274 32 64 128 256), losses := [] }

theorem u30858 : Upper (D 6) (R 6) [10,33,160,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30859 : Route 9 := (fun mask => (mask,id))

def c30859 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30859 : Upper (D 6) (R 6) [10,33,160,17,260] 13 := by
  apply FastRouting.sound _ _ [10,33,160,17,260] 13 (by decide) (choices 1) [2,4,64] r30859 c30859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12696
  · exact u12697
  · exact u12698

def r30860 : Route 9 := (fun mask => (mask,id))

def c30860 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30860 : Upper (D 6) (R 6) [10,33,160,17,320] 13 := by
  apply FastRouting.sound _ _ [10,33,160,17,320] 13 (by decide) (choices 1) [2,4,64] r30860 c30860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12699
  · exact u12700
  · exact u12701

def b30861 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 164 28 19 356 324 452 324), lower := (rows 11 35 164 28 19 32 64 128 256), losses := [] }

theorem u30861 : Upper (D 6) (R 6) [10,33,160,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30862 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 164 28 21 354 322 450 322), lower := (rows 11 35 164 28 21 32 64 128 256), losses := [] }

theorem u30862 : Upper (D 6) (R 6) [10,33,160,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30863 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 164 28 22 353 321 449 321), lower := (rows 11 35 164 28 22 32 64 128 256), losses := [] }

theorem u30863 : Upper (D 6) (R 6) [10,33,160,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30864 : Route 9 := (fun mask => (mask,id))

def c30864 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30864 : Upper (D 6) (R 6) [10,33,160,20,65] 13 := by
  apply FastRouting.sound _ _ [10,33,160,20,65] 13 (by decide) (choices 1) [2,4,64,256] r30864 c30864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12702
  · exact u12703
  · exact u12704
  · exact u12705

def r30865 : Route 9 := (fun mask => (mask,id))

def c30865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30865 : Upper (D 6) (R 6) [10,33,160,20,66] 13 := by
  apply FastRouting.sound _ _ [10,33,160,20,66] 13 (by decide) (choices 1) [1,4,64,256] r30865 c30865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12706
  · exact u12707
  · exact u12708
  · exact u12709

def b30866 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 164 28 84 355 323 451 323), lower := (rows 11 35 164 28 84 32 64 128 256), losses := [] }

theorem u30866 : Upper (D 6) (R 6) [10,33,160,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30867 : Route 9 := (fun mask => (mask,id))

def c30867 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30867 : Upper (D 6) (R 6) [10,33,160,20,257] 13 := by
  apply FastRouting.sound _ _ [10,33,160,20,257] 13 (by decide) (choices 1) [2,4,64] r30867 c30867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12710
  · exact u12711
  · exact u12712

def r30868 : Route 9 := (fun mask => (mask,id))

def c30868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30868 : Upper (D 6) (R 6) [10,33,160,20,258] 13 := by
  apply FastRouting.sound _ _ [10,33,160,20,258] 13 (by decide) (choices 1) [1,4,64] r30868 c30868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12713
  · exact u12714
  · exact u12715

def b30869 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 164 28 276 99 67 195 323), lower := (rows 11 35 164 28 276 32 64 128 256), losses := [] }

theorem u30869 : Upper (D 6) (R 6) [10,33,160,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30870 : Route 9 := (fun mask => (mask,id))

def c30870 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30870 : Upper (D 6) (R 6) [10,33,160,20,320] 13 := by
  apply FastRouting.sound _ _ [10,33,160,20,320] 13 (by decide) (choices 1) [1,2,4,64] r30870 c30870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12716
  · exact u12717
  · exact u12718
  · exact u12719

def b30871 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 11 35 164 73 22 372 340 468 340), lower := (rows 11 35 164 73 22 32 64 128 256), losses := [] }

theorem u30871 : Upper (D 6) (R 6) [10,33,160,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30872 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 164 73 82 308 340 404 276), lower := (rows 11 35 164 73 82 32 64 128 256), losses := [] }

theorem u30872 : Upper (D 6) (R 6) [10,33,160,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30873 : Route 9 := (fun mask => (mask,id))

def c30873 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30873 : Upper (D 6) (R 6) [10,33,160,65,68] 13 := by
  apply FastRouting.sound _ _ [10,33,160,65,68] 13 (by decide) (choices 1) [2,4,16,256] r30873 c30873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12720
  · exact u12721
  · exact u12722
  · exact u12723

def b30874 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 164 73 274 116 84 212 340), lower := (rows 11 35 164 73 274 32 64 128 256), losses := [] }

theorem u30874 : Upper (D 6) (R 6) [10,33,160,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30875 : Route 9 := (fun mask => (mask,id))

def c30875 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30875 : Upper (D 6) (R 6) [10,33,160,65,260] 13 := by
  apply FastRouting.sound _ _ [10,33,160,65,260] 13 (by decide) (choices 1) [2,4,16,64] r30875 c30875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12724
  · exact u12725
  · exact u12726
  · exact u12727

def r30876 : Route 9 := (fun mask => (mask,id))

def c30876 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30876 : Upper (D 6) (R 6) [10,33,160,65,320] 13 := by
  apply FastRouting.sound _ _ [10,33,160,65,320] 13 (by decide) (choices 1) [2,4,16] r30876 c30876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12728
  · exact u12729
  · exact u12730

def b30877 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 164 76 19 372 340 468 340), lower := (rows 11 35 164 76 19 32 64 128 256), losses := [] }

theorem u30877 : Upper (D 6) (R 6) [10,33,160,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30878 : Route 9 := (fun mask => (mask,id))

def c30878 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30878 : Upper (D 6) (R 6) [10,33,160,68,5] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,5] 13 (by decide) (choices 1) [2,16,64,256] r30878 c30878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12731
  · exact u12732
  · exact u12733
  · exact u12734

def r30879 : Route 9 := (fun mask => (mask,id))

def c30879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30879 : Upper (D 6) (R 6) [10,33,160,68,6] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,6] 13 (by decide) (choices 1) [1,16,64,256] r30879 c30879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12735
  · exact u12736
  · exact u12737
  · exact u12738

def r30880 : Route 9 := (fun mask => (mask,id))

def c30880 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30880 : Upper (D 6) (R 6) [10,33,160,68,65] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,65] 13 (by decide) (choices 1) [2,4,16,256] r30880 c30880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12739
  · exact u12740
  · exact u12741
  · exact u12742

def r30881 : Route 9 := (fun mask => (mask,id))

def c30881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30881 : Upper (D 6) (R 6) [10,33,160,68,66] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,66] 13 (by decide) (choices 1) [1,4,16,256] r30881 c30881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12743
  · exact u12744
  · exact u12745
  · exact u12746

def b30882 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 164 76 84 307 339 403 275), lower := (rows 11 35 164 76 84 32 64 128 256), losses := [] }

theorem u30882 : Upper (D 6) (R 6) [10,33,160,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30883 : Route 9 := (fun mask => (mask,id))

def c30883 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30883 : Upper (D 6) (R 6) [10,33,160,68,257] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,257] 13 (by decide) (choices 1) [2,4,16,64] r30883 c30883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12747
  · exact u12748
  · exact u12749
  · exact u12750

def r30884 : Route 9 := (fun mask => (mask,id))

def c30884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30884 : Upper (D 6) (R 6) [10,33,160,68,258] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,258] 13 (by decide) (choices 1) [1,4,16,64] r30884 c30884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12751
  · exact u12752
  · exact u12753
  · exact u12754

def r30885 : Route 9 := (fun mask => (mask,id))

def c30885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30885 : Upper (D 6) (R 6) [10,33,160,68,260] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,260] 13 (by decide) (choices 1) [1,2,16,64] r30885 c30885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12755
  · exact u12756
  · exact u12757
  · exact u12758

def r30886 : Route 9 := (fun mask => (mask,id))

def c30886 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30886 : Upper (D 6) (R 6) [10,33,160,68,320] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,320] 13 (by decide) (choices 1) [1,2,4,16] r30886 c30886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12759
  · exact u12760
  · exact u12761
  · exact u12762

def b30887 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 164 88 19 356 324 452 324), lower := (rows 11 35 164 88 19 32 64 128 256), losses := [] }

theorem u30887 : Upper (D 6) (R 6) [10,33,160,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30888 : Route 9 := (fun mask => (mask,id))

def c30888 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30888 : Upper (D 6) (R 6) [10,33,160,80,5] 13 := by
  apply FastRouting.sound _ _ [10,33,160,80,5] 13 (by decide) (choices 1) [2,4,64,256] r30888 c30888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12763
  · exact u12764
  · exact u12765
  · exact u12766

def b30889 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 329, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 35 164 88 22 357 325 453 325), lower := (rows 11 35 164 88 22 32 64 128 256), losses := [] }

theorem u30889 : Upper (D 6) (R 6) [10,33,160,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30890 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 164 88 81 294 326 390 262), lower := (rows 11 35 164 88 81 32 64 128 256), losses := [] }

theorem u30890 : Upper (D 6) (R 6) [10,33,160,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30891 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 164 88 82 293 325 389 261), lower := (rows 11 35 164 88 82 32 64 128 256), losses := [] }

theorem u30891 : Upper (D 6) (R 6) [10,33,160,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30892 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 164 88 84 295 327 391 263), lower := (rows 11 35 164 88 84 32 64 128 256), losses := [] }

theorem u30892 : Upper (D 6) (R 6) [10,33,160,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30893 : Route 9 := (fun mask => (mask,id))

def c30893 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30893 : Upper (D 6) (R 6) [10,33,160,80,257] 13 := by
  apply FastRouting.sound _ _ [10,33,160,80,257] 13 (by decide) (choices 1) [2,4,64] r30893 c30893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12767
  · exact u12768
  · exact u12769

def r30894 : Route 9 := (fun mask => (mask,id))

def c30894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30894 : Upper (D 6) (R 6) [10,33,160,80,258] 13 := by
  apply FastRouting.sound _ _ [10,33,160,80,258] 13 (by decide) (choices 1) [1,4,64] r30894 c30894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12770
  · exact u12771
  · exact u12772

def r30895 : Route 9 := (fun mask => (mask,id))

def c30895 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30895 : Upper (D 6) (R 6) [10,33,160,80,260] 13 := by
  apply FastRouting.sound _ _ [10,33,160,80,260] 13 (by decide) (choices 1) [1,2,4,64] r30895 c30895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12773
  · exact u12774
  · exact u12775
  · exact u12776

def b30896 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 164 88 336 39 71 135 263), lower := (rows 11 35 164 88 336 32 64 128 256), losses := [] }

theorem u30896 : Upper (D 6) (R 6) [10,33,160,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30897 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 244, targets := 1 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 11 35 164 265 22 116 84 212 340), lower := (rows 11 35 164 265 22 32 64 128 256), losses := [] }

theorem u30897 : Upper (D 6) (R 6) [10,33,160,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30898 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 244, targets := 1 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 164 265 82 116 84 212 340), lower := (rows 11 35 164 265 82 32 64 128 256), losses := [] }

theorem u30898 : Upper (D 6) (R 6) [10,33,160,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30899 : Route 9 := (fun mask => (mask,id))

def c30899 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30899 : Upper (D 6) (R 6) [10,33,160,257,68] 13 := by
  apply FastRouting.sound _ _ [10,33,160,257,68] 13 (by decide) (choices 1) [2,4,16,64] r30899 c30899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12777
  · exact u12778
  · exact u12779
  · exact u12780

#print axioms u30899
end Delivery.IrregularNine14.P06
