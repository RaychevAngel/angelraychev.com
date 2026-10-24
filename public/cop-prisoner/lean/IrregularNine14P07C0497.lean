import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0192
import IrregularNine14P07C0193

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29820 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 7 44 152 34 81 209 337), lower := (rows 97 386 7 44 152 34 64 128 256), losses := [] }

theorem u29820 : Upper (D 7) (R 7) [96,384,3,36,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29821 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 386 7 44 152 48 67 195 323), lower := (rows 97 386 7 44 152 48 64 128 256), losses := [{ target := 5, region := (rows 1 15 5 8 24 0 69 133 261), good := (rows 455 386 455 478 154 16 64 128 256) }] }

theorem u29821 : Upper (D 7) (R 7) [96,384,3,36,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29821 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29822 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 44 152 96 83 147 275), lower := (rows 97 386 7 44 152 96 64 128 256), losses := [] }

theorem u29822 : Upper (D 7) (R 7) [96,384,3,36,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29823 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 7 44 208 33 90 154 282), lower := (rows 97 386 7 44 208 33 64 128 256), losses := [] }

theorem u29823 : Upper (D 7) (R 7) [96,384,3,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29824 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 7 44 208 34 89 153 281), lower := (rows 97 386 7 44 208 34 64 128 256), losses := [] }

theorem u29824 : Upper (D 7) (R 7) [96,384,3,36,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29825 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 386 7 44 208 40 83 147 275), lower := (rows 97 386 7 44 208 40 64 128 256), losses := [] }

theorem u29825 : Upper (D 7) (R 7) [96,384,3,36,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29825 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29826 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 7 44 208 48 75 139 267), lower := (rows 97 386 7 44 208 48 64 128 256), losses := [] }

theorem u29826 : Upper (D 7) (R 7) [96,384,3,36,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29826 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29827 : Route 9 := (fun mask => (mask,id))

def c29827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29827 : Upper (D 7) (R 7) [96,384,3,48,129,2] 13 := by
  apply FastRouting.sound _ _ [96,384,3,48,129,2] 13 (by decide) (choices 1) [4,8] r29827 c29827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11576
  · exact u11577

def r29828 : Route 9 := (fun mask => (mask,id))

def c29828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29828 : Upper (D 7) (R 7) [96,384,3,48,129,4] 13 := by
  apply FastRouting.sound _ _ [96,384,3,48,129,4] 13 (by decide) (choices 1) [2,8] r29828 c29828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11578
  · exact u11579

def b29829 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 386 7 56 145 40 70 198 326), lower := (rows 97 386 7 56 145 40 64 128 256), losses := [] }

theorem u29829 : Upper (D 7) (R 7) [96,384,3,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29829 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29830 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 56 145 96 78 142 270), lower := (rows 97 386 7 56 145 96 64 128 256), losses := [] }

theorem u29830 : Upper (D 7) (R 7) [96,384,3,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29831 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 450, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,5)], upper := (rows 97 386 7 56 148 33 74 202 330), lower := (rows 97 386 7 56 148 33 64 128 256), losses := [] }

theorem u29831 : Upper (D 7) (R 7) [96,384,3,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29832 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 65, targets := 2 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(3,0),(3,6)], upper := (rows 97 386 7 56 148 34 73 201 329), lower := (rows 97 386 7 56 148 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 38 64 128 256), good := (rows 96 418 38 56 188 34 64 128 256) },{ target := 6, region := (rows 1 2 4 24 16 38 0 128 256), good := (rows 33 418 39 56 188 34 0 128 256) }] }

theorem u29832 : Upper (D 7) (R 7) [96,384,3,48,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29833 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 386 7 56 148 40 67 195 323), lower := (rows 97 386 7 56 148 40 64 128 256), losses := [] }

theorem u29833 : Upper (D 7) (R 7) [96,384,3,48,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29833 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29834 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 7 56 148 96 75 139 267), lower := (rows 97 386 7 56 148 96 64 128 256), losses := [] }

theorem u29834 : Upper (D 7) (R 7) [96,384,3,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29835 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 386 7 56 208 33 78 142 270), lower := (rows 97 386 7 56 208 33 64 128 256), losses := [] }

theorem u29835 : Upper (D 7) (R 7) [96,384,3,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29836 : Route 9 := (fun mask => (mask,id))

def c29836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29836 : Upper (D 7) (R 7) [96,384,3,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,384,3,48,192,2] 13 (by decide) (choices 1) [1,4,8] r29836 c29836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11580
  · exact u11581
  · exact u11582

def r29837 : Route 9 := (fun mask => (mask,id))

def c29837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29837 : Upper (D 7) (R 7) [96,384,3,48,192,4] 13 := by
  apply FastRouting.sound _ _ [96,384,3,48,192,4] 13 (by decide) (choices 1) [1,2,8] r29837 c29837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11583
  · exact u11584
  · exact u11585

def b29838 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 386 7 56 208 40 71 135 263), lower := (rows 97 386 7 56 208 40 64 128 256), losses := [] }

theorem u29838 : Upper (D 7) (R 7) [96,384,3,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29838 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29839 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 386 13 14 50 33 208 208 464), lower := (rows 97 386 13 14 50 33 64 128 256), losses := [] }

theorem u29839 : Upper (D 7) (R 7) [96,384,9,6,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29840 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 13 14 50 48 193 193 449), lower := (rows 97 386 13 14 50 48 64 128 256), losses := [] }

theorem u29840 : Upper (D 7) (R 7) [96,384,9,6,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29840 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29841 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 14 50 96 209 145 401), lower := (rows 97 386 13 14 50 96 64 128 256), losses := [] }

theorem u29841 : Upper (D 7) (R 7) [96,384,9,6,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29842 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 97 386 13 14 50 160 81 209 337), lower := (rows 97 386 13 14 50 160 64 128 256), losses := [] }

theorem u29842 : Upper (D 7) (R 7) [96,384,9,6,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29843 : Route 9 := (fun mask => (mask,id))

def c29843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29843 : Upper (D 7) (R 7) [96,384,9,6,129,2] 13 := by
  apply FastRouting.sound _ _ [96,384,9,6,129,2] 13 (by decide) (choices 1) [16,32] r29843 c29843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11586
  · exact u11587

theorem m29844_2 : Upper (D 7) (R 7) [96,384,9,6,129,16,2] 13 :=
  permutation_upper _ _ _ [96,384,9,6,129,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11586

def r29844 : Route 9 := (fun mask => (mask,id))

def c29844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29844 : Upper (D 7) (R 7) [96,384,9,6,129,16] 13 := by
  apply FastRouting.sound _ _ [96,384,9,6,129,16] 13 (by decide) (choices 1) [2,32] r29844 c29844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m29844_2
  · exact u11588

def b29845 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 14 145 96 114 178 306), lower := (rows 97 386 13 14 145 96 64 128 256), losses := [] }

theorem u29845 : Upper (D 7) (R 7) [96,384,9,6,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29846 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 386 13 14 176 33 82 210 338), lower := (rows 97 386 13 14 176 33 64 128 256), losses := [] }

theorem u29846 : Upper (D 7) (R 7) [96,384,9,6,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29847 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(4,0),(4,1),(4,6)], upper := (rows 97 386 13 14 176 34 81 209 337), lower := (rows 97 386 13 14 176 34 64 128 256), losses := [] }

theorem u29847 : Upper (D 7) (R 7) [96,384,9,6,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29848 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 13 14 176 48 67 195 323), lower := (rows 97 386 13 14 176 48 64 128 256), losses := [] }

theorem u29848 : Upper (D 7) (R 7) [96,384,9,6,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29848 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29849 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 14 176 96 83 147 275), lower := (rows 97 386 13 14 176 96 64 128 256), losses := [] }

theorem u29849 : Upper (D 7) (R 7) [96,384,9,6,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29850 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 97 386 13 26 52 33 194 194 450), lower := (rows 97 386 13 26 52 33 64 128 256), losses := [] }

theorem u29850 : Upper (D 7) (R 7) [96,384,9,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29851 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 386, targets := 32 },{ cop := 4, region := 193, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(4,0)], upper := (rows 97 386 13 26 52 34 193 193 449), lower := (rows 97 386 13 26 52 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 42 64 128 256), good := (rows 96 418 60 58 52 34 64 128 256) },{ target := 1, region := (rows 49 0 12 8 16 32 125 189 317), good := (rows 481 384 461 477 501 481 64 128 256) }] }

theorem u29851 : Upper (D 7) (R 7) [96,384,9,18,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29852 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 26 52 96 195 131 387), lower := (rows 97 386 13 26 52 96 64 128 256), losses := [] }

theorem u29852 : Upper (D 7) (R 7) [96,384,9,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29853 : Route 9 := (fun mask => (mask,id))

def c29853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29853 : Upper (D 7) (R 7) [96,384,9,18,36,128] 13 := by
  apply FastRouting.sound _ _ [96,384,9,18,36,128] 13 (by decide) (choices 1) [1,2] r29853 c29853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11589
  · exact u11590

def r29854 : Route 9 := (fun mask => (mask,id))

def c29854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29854 : Upper (D 7) (R 7) [96,384,9,18,129,2] 13 := by
  apply FastRouting.sound _ _ [96,384,9,18,129,2] 13 (by decide) (choices 1) [4,32] r29854 c29854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11591
  · exact u11592

def b29855 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 97 386 13 26 145 36 98 226 354), lower := (rows 97 386 13 26 145 36 64 128 256), losses := [] }

theorem u29855 : Upper (D 7) (R 7) [96,384,9,18,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29855 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29856 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 26 145 96 102 166 294), lower := (rows 97 386 13 26 145 96 64 128 256), losses := [] }

theorem u29856 : Upper (D 7) (R 7) [96,384,9,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29857 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 386, targets := 1 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,0),(2,7)], upper := (rows 97 386 13 26 148 33 98 226 354), lower := (rows 97 386 13 26 148 33 64 128 256), losses := [] }

theorem u29857 : Upper (D 7) (R 7) [96,384,9,18,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29858 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 5, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 97 386 13 26 148 34 97 225 353), lower := (rows 97 386 13 26 148 34 64 128 256), losses := [{ target := 1, region := (rows 33 0 4 8 20 32 97 161 289), good := (rows 481 384 477 24 148 481 64 128 256) }] }

theorem u29858 : Upper (D 7) (R 7) [96,384,9,18,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29859 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 26 148 96 99 163 291), lower := (rows 97 386 13 26 148 96 64 128 256), losses := [] }

theorem u29859 : Upper (D 7) (R 7) [96,384,9,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29860 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(2,7)], upper := (rows 97 386 13 26 176 33 70 198 326), lower := (rows 97 386 13 26 176 33 64 128 256), losses := [] }

theorem u29860 : Upper (D 7) (R 7) [96,384,9,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29861 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 97 386 13 26 176 34 69 197 325), lower := (rows 97 386 13 26 176 34 64 128 256), losses := [] }

theorem u29861 : Upper (D 7) (R 7) [96,384,9,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29862 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,7),(1,5),(2,7)], upper := (rows 97 386 13 26 176 36 67 195 323), lower := (rows 97 386 13 26 176 36 64 128 256), losses := [] }

theorem u29862 : Upper (D 7) (R 7) [96,384,9,18,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29862 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29863 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 26 176 96 71 135 263), lower := (rows 97 386 13 26 176 96 64 128 256), losses := [] }

theorem u29863 : Upper (D 7) (R 7) [96,384,9,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29864 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 386 13 28 50 33 194 194 450), lower := (rows 97 386 13 28 50 33 64 128 256), losses := [] }

theorem u29864 : Upper (D 7) (R 7) [96,384,9,20,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29865 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 193, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 97 386 13 28 50 34 193 193 449), lower := (rows 97 386 13 28 50 34 64 128 256), losses := [] }

theorem u29865 : Upper (D 7) (R 7) [96,384,9,20,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29866 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 28 50 96 195 131 387), lower := (rows 97 386 13 28 50 96 64 128 256), losses := [] }

theorem u29866 : Upper (D 7) (R 7) [96,384,9,20,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29867 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 97 386 13 28 50 160 67 195 323), lower := (rows 97 386 13 28 50 160 64 128 256), losses := [] }

theorem u29867 : Upper (D 7) (R 7) [96,384,9,20,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29868 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 386 13 28 176 33 66 194 322), lower := (rows 97 386 13 28 176 33 64 128 256), losses := [] }

theorem u29868 : Upper (D 7) (R 7) [96,384,9,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29869 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 0, region := 386, targets := 32 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(4,0),(4,6)], upper := (rows 97 386 13 28 176 34 67 195 323), lower := (rows 97 386 13 28 176 34 64 128 256), losses := [] }

theorem u29869 : Upper (D 7) (R 7) [96,384,9,20,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29870 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 28 176 96 67 131 259), lower := (rows 97 386 13 28 176 96 64 128 256), losses := [] }

theorem u29870 : Upper (D 7) (R 7) [96,384,9,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29871 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 42 22 33 208 208 464), lower := (rows 97 386 13 42 22 33 64 128 256), losses := [] }

theorem u29871 : Upper (D 7) (R 7) [96,384,9,34,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29872 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 386 13 42 22 48 193 193 449), lower := (rows 97 386 13 42 22 48 64 128 256), losses := [] }

theorem u29872 : Upper (D 7) (R 7) [96,384,9,34,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29872 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29873 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 13 42 22 96 209 145 401), lower := (rows 97 386 13 42 22 96 64 128 256), losses := [] }

theorem u29873 : Upper (D 7) (R 7) [96,384,9,34,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29874 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 97 386 13 42 22 160 81 209 337), lower := (rows 97 386 13 42 22 160 64 128 256), losses := [] }

theorem u29874 : Upper (D 7) (R 7) [96,384,9,34,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29875 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 42 82 33 212 148 404), lower := (rows 97 386 13 42 82 33 64 128 256), losses := [] }

theorem u29875 : Upper (D 7) (R 7) [96,384,9,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29876 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 386 13 42 82 36 209 145 401), lower := (rows 97 386 13 42 82 36 64 128 256), losses := [] }

theorem u29876 : Upper (D 7) (R 7) [96,384,9,34,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29876 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29877 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 13 42 82 48 197 133 389), lower := (rows 97 386 13 42 82 48 64 128 256), losses := [] }

theorem u29877 : Upper (D 7) (R 7) [96,384,9,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29877 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29878 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 97 386 13 42 82 160 85 149 277), lower := (rows 97 386 13 42 82 160 64 128 256), losses := [] }

theorem u29878 : Upper (D 7) (R 7) [96,384,9,34,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29879 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 386 13 42 84 33 210 146 402), lower := (rows 97 386 13 42 84 33 64 128 256), losses := [] }

theorem u29879 : Upper (D 7) (R 7) [96,384,9,34,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29879
end Delivery.IrregularNine14.P07
