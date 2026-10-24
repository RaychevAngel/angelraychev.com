import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0331
import IrregularNine14P08C0332
import IrregularNine14P08C0333
import IrregularNine14P08C0334
import IrregularNine14P08C0335
import IrregularNine14P08C0336
import IrregularNine14P08C0337
import IrregularNine14P08C0338

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24000 : PairBound 9 := { available := 441, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 7 196 441 441 441 505 441 441), lower := (rows 67 7 196 8 16 32 64 128 256), losses := [] }

theorem u24000 : Upper (D 8) (R 8) [66,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24001 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 67 7 261 248 248 248 248 248 504), lower := (rows 67 7 261 8 16 32 64 128 256), losses := [] }

theorem u24001 : Upper (D 8) (R 8) [66,5,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24002 : Route 9 := (fun mask => (mask,id))

def c24002 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24002 : Upper (D 8) (R 8) [66,5,264] 13 := by
  apply FastRouting.sound _ _ [66,5,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24002 c24002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19871
  · exact u19872
  · exact u19873
  · exact u19874
  · exact u19875
  · exact u19876
  · exact u19877
  · exact u19878
  · exact u19879
  · exact u19880

def r24003 : Route 9 := (fun mask => (mask,id))

def c24003 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24003 : Upper (D 8) (R 8) [66,5,288] 13 := by
  apply FastRouting.sound _ _ [66,5,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24003 c24003
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19881
  · exact u19882
  · exact u19883
  · exact u19884
  · exact u19885
  · exact u19886
  · exact u19887
  · exact u19888
  · exact u19889
  · exact u19890

def b24004 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 7 324 185 185 185 249 185 441), lower := (rows 67 7 324 8 16 32 64 128 256), losses := [] }

theorem u24004 : Upper (D 8) (R 8) [66,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24005 : Route 9 := (fun mask => (mask,id))

def c24005 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24005 : Upper (D 8) (R 8) [66,5,384] 13 := by
  apply FastRouting.sound _ _ [66,5,384] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24005 c24005
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19891
  · exact u19892
  · exact u19893
  · exact u19894
  · exact u19895
  · exact u19896
  · exact u19897
  · exact u19898
  · exact u19899
  · exact u19900

def r24006 : Route 9 := (fun mask => (mask,id))

def c24006 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u24006 : Upper (D 8) (R 8) [66,12,17] 13 := by
  apply FastRouting.sound _ _ [66,12,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r24006 c24006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19901
  · exact u19902
  · exact u19903
  · exact u19904
  · exact u19905
  · exact u19906
  · exact u19907
  · exact u19908
  · exact u19909
  · exact u19910

theorem m24007_17 : Upper (D 8) (R 8) [66,12,33,17] 13 :=
  permutation_upper _ _ _ [66,12,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19901

def r24007 : Route 9 := (fun mask => (mask,id))

def c24007 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u24007 : Upper (D 8) (R 8) [66,12,33] 13 := by
  apply FastRouting.sound _ _ [66,12,33] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r24007 c24007
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24007_17
  · exact u19911
  · exact u19912
  · exact u19913
  · exact u19914
  · exact u19915
  · exact u19916
  · exact u19917
  · exact u19918
  · exact u19919
  · exact u19920
  · exact u19921
  · exact u19922
  · exact u19923
  · exact u19924

theorem m24008_33 : Upper (D 8) (R 8) [66,12,48,33] 13 :=
  permutation_upper _ _ _ [66,12,33,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19912

def r24008 : Route 9 := (fun mask => (mask,id))

def c24008 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u24008 : Upper (D 8) (R 8) [66,12,48] 13 := by
  apply FastRouting.sound _ _ [66,12,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r24008 c24008
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24008_33
  · exact u19925
  · exact u19926
  · exact u19927
  · exact u19928
  · exact u19929
  · exact u19930
  · exact u19931
  · exact u19932
  · exact u19933

def b24009 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 69 441 433 433 497 433 433), lower := (rows 67 14 69 8 16 32 64 128 256), losses := [] }

theorem u24009 : Upper (D 8) (R 8) [66,12,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24010 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 84 425 433 417 481 417 417), lower := (rows 67 14 84 8 16 32 64 128 256), losses := [] }

theorem u24010 : Upper (D 8) (R 8) [66,12,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24011 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 100 441 433 433 497 433 433), lower := (rows 67 14 100 8 16 32 64 128 256), losses := [] }

theorem u24011 : Upper (D 8) (R 8) [66,12,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24012_17 : Upper (D 8) (R 8) [66,12,129,17] 13 :=
  permutation_upper _ _ _ [66,12,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19904

theorem m24012_33 : Upper (D 8) (R 8) [66,12,129,33] 13 :=
  permutation_upper _ _ _ [66,12,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19916

theorem m24012_48 : Upper (D 8) (R 8) [66,12,129,48] 13 :=
  permutation_upper _ _ _ [66,12,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19927

theorem m24012_65 : Upper (D 8) (R 8) [66,12,129,65] 13 :=
  permutation_upper _ _ _ [66,12,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19934

theorem m24012_80 : Upper (D 8) (R 8) [66,12,129,80] 13 :=
  permutation_upper _ _ _ [66,12,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19941

theorem m24012_96 : Upper (D 8) (R 8) [66,12,129,96] 13 :=
  permutation_upper _ _ _ [66,12,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19946

def r24012 : Route 9 := (fun mask => (mask,id))

def c24012 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u24012 : Upper (D 8) (R 8) [66,12,129] 13 := by
  apply FastRouting.sound _ _ [66,12,129] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r24012 c24012
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24012_17
  · exact m24012_33
  · exact m24012_48
  · exact m24012_65
  · exact m24012_80
  · exact m24012_96
  · exact u19953
  · exact u19954
  · exact u19955
  · exact u19956
  · exact u19957
  · exact u19958
  · exact u19959
  · exact u19960
  · exact u19961

theorem m24013_33 : Upper (D 8) (R 8) [66,12,144,33] 13 :=
  permutation_upper _ _ _ [66,12,33,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19917

theorem m24013_65 : Upper (D 8) (R 8) [66,12,144,65] 13 :=
  permutation_upper _ _ _ [66,12,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19935

theorem m24013_96 : Upper (D 8) (R 8) [66,12,144,96] 13 :=
  permutation_upper _ _ _ [66,12,96,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19947

theorem m24013_129 : Upper (D 8) (R 8) [66,12,144,129] 13 :=
  permutation_upper _ _ _ [66,12,129,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19954

def r24013 : Route 9 := (fun mask => (mask,id))

def c24013 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u24013 : Upper (D 8) (R 8) [66,12,144] 13 := by
  apply FastRouting.sound _ _ [66,12,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r24013 c24013
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24013_33
  · exact m24013_65
  · exact m24013_96
  · exact m24013_129
  · exact u19962
  · exact u19963
  · exact u19964
  · exact u19965
  · exact u19966
  · exact u19967

theorem m24014_17 : Upper (D 8) (R 8) [66,12,160,17] 13 :=
  permutation_upper _ _ _ [66,12,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19905

theorem m24014_33 : Upper (D 8) (R 8) [66,12,160,33] 13 :=
  permutation_upper _ _ _ [66,12,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19918

theorem m24014_48 : Upper (D 8) (R 8) [66,12,160,48] 13 :=
  permutation_upper _ _ _ [66,12,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19928

theorem m24014_65 : Upper (D 8) (R 8) [66,12,160,65] 13 :=
  permutation_upper _ _ _ [66,12,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19936

theorem m24014_80 : Upper (D 8) (R 8) [66,12,160,80] 13 :=
  permutation_upper _ _ _ [66,12,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19942

theorem m24014_96 : Upper (D 8) (R 8) [66,12,160,96] 13 :=
  permutation_upper _ _ _ [66,12,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19948

theorem m24014_129 : Upper (D 8) (R 8) [66,12,160,129] 13 :=
  permutation_upper _ _ _ [66,12,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19955

theorem m24014_144 : Upper (D 8) (R 8) [66,12,160,144] 13 :=
  permutation_upper _ _ _ [66,12,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19962

def r24014 : Route 9 := (fun mask => (mask,id))

def c24014 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u24014 : Upper (D 8) (R 8) [66,12,160] 13 := by
  apply FastRouting.sound _ _ [66,12,160] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r24014 c24014
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24014_17
  · exact m24014_33
  · exact m24014_48
  · exact m24014_65
  · exact m24014_80
  · exact m24014_96
  · exact m24014_129
  · exact m24014_144
  · exact u19968
  · exact u19969
  · exact u19970
  · exact u19971
  · exact u19972
  · exact u19973
  · exact u19974

def b24015 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 196 441 433 433 497 433 433), lower := (rows 67 14 196 8 16 32 64 128 256), losses := [] }

theorem u24015 : Upper (D 8) (R 8) [66,12,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24016_17 : Upper (D 8) (R 8) [66,12,257,17] 13 :=
  permutation_upper _ _ _ [66,12,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19907

theorem m24016_33 : Upper (D 8) (R 8) [66,12,257,33] 13 :=
  permutation_upper _ _ _ [66,12,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19920

theorem m24016_48 : Upper (D 8) (R 8) [66,12,257,48] 13 :=
  permutation_upper _ _ _ [66,12,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19930

theorem m24016_65 : Upper (D 8) (R 8) [66,12,257,65] 13 :=
  permutation_upper _ _ _ [66,12,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19937

theorem m24016_80 : Upper (D 8) (R 8) [66,12,257,80] 13 :=
  permutation_upper _ _ _ [66,12,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19943

theorem m24016_96 : Upper (D 8) (R 8) [66,12,257,96] 13 :=
  permutation_upper _ _ _ [66,12,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19949

theorem m24016_129 : Upper (D 8) (R 8) [66,12,257,129] 13 :=
  permutation_upper _ _ _ [66,12,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19957

theorem m24016_144 : Upper (D 8) (R 8) [66,12,257,144] 13 :=
  permutation_upper _ _ _ [66,12,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19964

theorem m24016_160 : Upper (D 8) (R 8) [66,12,257,160] 13 :=
  permutation_upper _ _ _ [66,12,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19970

theorem m24016_192 : Upper (D 8) (R 8) [66,12,257,192] 13 :=
  permutation_upper _ _ _ [66,12,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19975

def r24016 : Route 9 := (fun mask => (mask,id))

def c24016 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24016 : Upper (D 8) (R 8) [66,12,257] 13 := by
  apply FastRouting.sound _ _ [66,12,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24016 c24016
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24016_17
  · exact m24016_33
  · exact m24016_48
  · exact m24016_65
  · exact m24016_80
  · exact m24016_96
  · exact m24016_129
  · exact m24016_144
  · exact m24016_160
  · exact m24016_192

theorem m24017_33 : Upper (D 8) (R 8) [66,12,272,33] 13 :=
  permutation_upper _ _ _ [66,12,33,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19921

theorem m24017_65 : Upper (D 8) (R 8) [66,12,272,65] 13 :=
  permutation_upper _ _ _ [66,12,65,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19938

theorem m24017_96 : Upper (D 8) (R 8) [66,12,272,96] 13 :=
  permutation_upper _ _ _ [66,12,96,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19950

theorem m24017_129 : Upper (D 8) (R 8) [66,12,272,129] 13 :=
  permutation_upper _ _ _ [66,12,129,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19958

theorem m24017_160 : Upper (D 8) (R 8) [66,12,272,160] 13 :=
  permutation_upper _ _ _ [66,12,160,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19971

theorem m24017_192 : Upper (D 8) (R 8) [66,12,272,192] 13 :=
  permutation_upper _ _ _ [66,12,192,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19976

def r24017 : Route 9 := (fun mask => (mask,id))

def c24017 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24017 : Upper (D 8) (R 8) [66,12,272] 13 := by
  apply FastRouting.sound _ _ [66,12,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r24017 c24017
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24017_33
  · exact m24017_65
  · exact m24017_96
  · exact m24017_129
  · exact m24017_160
  · exact m24017_192

theorem m24018_17 : Upper (D 8) (R 8) [66,12,288,17] 13 :=
  permutation_upper _ _ _ [66,12,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19908

theorem m24018_33 : Upper (D 8) (R 8) [66,12,288,33] 13 :=
  permutation_upper _ _ _ [66,12,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19922

theorem m24018_48 : Upper (D 8) (R 8) [66,12,288,48] 13 :=
  permutation_upper _ _ _ [66,12,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19931

theorem m24018_65 : Upper (D 8) (R 8) [66,12,288,65] 13 :=
  permutation_upper _ _ _ [66,12,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19939

theorem m24018_80 : Upper (D 8) (R 8) [66,12,288,80] 13 :=
  permutation_upper _ _ _ [66,12,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19944

theorem m24018_96 : Upper (D 8) (R 8) [66,12,288,96] 13 :=
  permutation_upper _ _ _ [66,12,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19951

theorem m24018_129 : Upper (D 8) (R 8) [66,12,288,129] 13 :=
  permutation_upper _ _ _ [66,12,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19959

theorem m24018_144 : Upper (D 8) (R 8) [66,12,288,144] 13 :=
  permutation_upper _ _ _ [66,12,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19965

theorem m24018_160 : Upper (D 8) (R 8) [66,12,288,160] 13 :=
  permutation_upper _ _ _ [66,12,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19972

theorem m24018_192 : Upper (D 8) (R 8) [66,12,288,192] 13 :=
  permutation_upper _ _ _ [66,12,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19977

def r24018 : Route 9 := (fun mask => (mask,id))

def c24018 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24018 : Upper (D 8) (R 8) [66,12,288] 13 := by
  apply FastRouting.sound _ _ [66,12,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24018 c24018
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24018_17
  · exact m24018_33
  · exact m24018_48
  · exact m24018_65
  · exact m24018_80
  · exact m24018_96
  · exact m24018_129
  · exact m24018_144
  · exact m24018_160
  · exact m24018_192

def b24019 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 324 185 177 177 241 177 433), lower := (rows 67 14 324 8 16 32 64 128 256), losses := [] }

theorem u24019 : Upper (D 8) (R 8) [66,12,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24020_17 : Upper (D 8) (R 8) [66,12,384,17] 13 :=
  permutation_upper _ _ _ [66,12,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19910

theorem m24020_33 : Upper (D 8) (R 8) [66,12,384,33] 13 :=
  permutation_upper _ _ _ [66,12,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19924

theorem m24020_48 : Upper (D 8) (R 8) [66,12,384,48] 13 :=
  permutation_upper _ _ _ [66,12,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19933

theorem m24020_65 : Upper (D 8) (R 8) [66,12,384,65] 13 :=
  permutation_upper _ _ _ [66,12,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19940

theorem m24020_80 : Upper (D 8) (R 8) [66,12,384,80] 13 :=
  permutation_upper _ _ _ [66,12,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19945

theorem m24020_96 : Upper (D 8) (R 8) [66,12,384,96] 13 :=
  permutation_upper _ _ _ [66,12,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19952

theorem m24020_129 : Upper (D 8) (R 8) [66,12,384,129] 13 :=
  permutation_upper _ _ _ [66,12,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19961

theorem m24020_144 : Upper (D 8) (R 8) [66,12,384,144] 13 :=
  permutation_upper _ _ _ [66,12,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19967

theorem m24020_160 : Upper (D 8) (R 8) [66,12,384,160] 13 :=
  permutation_upper _ _ _ [66,12,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19974

theorem m24020_192 : Upper (D 8) (R 8) [66,12,384,192] 13 :=
  permutation_upper _ _ _ [66,12,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19978

def r24020 : Route 9 := (fun mask => (mask,id))

def c24020 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24020 : Upper (D 8) (R 8) [66,12,384] 13 := by
  apply FastRouting.sound _ _ [66,12,384] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24020 c24020
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24020_17
  · exact m24020_33
  · exact m24020_48
  · exact m24020_65
  · exact m24020_80
  · exact m24020_96
  · exact m24020_129
  · exact m24020_144
  · exact m24020_160
  · exact m24020_192

def b24021 : PairBound 9 := { available := 500, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 508 500 500 500 500 500), lower := (rows 67 35 13 8 16 32 64 128 256), losses := [] }

theorem u24021 : Upper (D 8) (R 8) [66,33,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24022_5 : Upper (D 8) (R 8) [66,33,24,5] 13 :=
  permutation_upper _ _ _ [66,33,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19979

def r24022 : Route 9 := (fun mask => (mask,id))

def c24022 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u24022 : Upper (D 8) (R 8) [66,33,24] 13 := by
  apply FastRouting.sound _ _ [66,33,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r24022 c24022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24022_5
  · exact u19998
  · exact u19999
  · exact u20000
  · exact u20001
  · exact u20002
  · exact u20003
  · exact u20004
  · exact u20005
  · exact u20006
  · exact u20007
  · exact u20008
  · exact u20009
  · exact u20010
  · exact u20011

def b24023 : PairBound 9 := { available := 508, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 508 508 508 508 508 508), lower := (rows 67 35 37 8 16 32 64 128 256), losses := [] }

theorem u24023 : Upper (D 8) (R 8) [66,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24024_5 : Upper (D 8) (R 8) [66,33,40,5] 13 :=
  permutation_upper _ _ _ [66,33,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19980

theorem m24024_17 : Upper (D 8) (R 8) [66,33,40,17] 13 :=
  permutation_upper _ _ _ [66,33,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19989

theorem m24024_20 : Upper (D 8) (R 8) [66,33,40,20] 13 :=
  permutation_upper _ _ _ [66,33,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19999

theorem m24024_33 : Upper (D 8) (R 8) [66,33,40,33] 13 :=
  permutation_upper _ _ _ [66,33,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20012

def r24024 : Route 9 := (fun mask => (mask,id))

def c24024 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u24024 : Upper (D 8) (R 8) [66,33,40] 13 := by
  apply FastRouting.sound _ _ [66,33,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r24024 c24024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24024_5
  · exact m24024_17
  · exact m24024_20
  · exact m24024_33
  · exact u20021
  · exact u20022
  · exact u20023
  · exact u20024
  · exact u20025
  · exact u20026
  · exact u20027
  · exact u20028
  · exact u20029
  · exact u20030
  · exact u20031
  · exact u20032
  · exact u20033
  · exact u20034
  · exact u20035
  · exact u20036
  · exact u20037

def b24025 : PairBound 9 := { available := 444, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 69 444 444 444 508 444 444), lower := (rows 67 35 69 8 16 32 64 128 256), losses := [] }

theorem u24025 : Upper (D 8) (R 8) [66,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24026_5 : Upper (D 8) (R 8) [66,33,72,5] 13 :=
  permutation_upper _ _ _ [66,33,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19981

theorem m24026_17 : Upper (D 8) (R 8) [66,33,72,17] 13 :=
  permutation_upper _ _ _ [66,33,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19990

theorem m24026_20 : Upper (D 8) (R 8) [66,33,72,20] 13 :=
  permutation_upper _ _ _ [66,33,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20001

theorem m24026_33 : Upper (D 8) (R 8) [66,33,72,33] 13 :=
  permutation_upper _ _ _ [66,33,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20013

theorem m24026_36 : Upper (D 8) (R 8) [66,33,72,36] 13 :=
  permutation_upper _ _ _ [66,33,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20024

theorem m24026_48 : Upper (D 8) (R 8) [66,33,72,48] 13 :=
  permutation_upper _ _ _ [66,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20038

def r24026 : Route 9 := (fun mask => (mask,id))

def c24026 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u24026 : Upper (D 8) (R 8) [66,33,72] 13 := by
  apply FastRouting.sound _ _ [66,33,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r24026 c24026
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24026_5
  · exact m24026_17
  · exact m24026_20
  · exact m24026_33
  · exact m24026_36
  · exact m24026_48
  · exact u20051
  · exact u20052
  · exact u20053
  · exact u20054
  · exact u20055
  · exact u20056
  · exact u20057
  · exact u20058
  · exact u20059

def b24027 : PairBound 9 := { available := 445, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 100 445 445 445 509 445 445), lower := (rows 67 35 100 8 16 32 64 128 256), losses := [] }

theorem u24027 : Upper (D 8) (R 8) [66,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24028 : PairBound 9 := { available := 508, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 508 508 508 508 508 508), lower := (rows 67 35 133 8 16 32 64 128 256), losses := [] }

theorem u24028 : Upper (D 8) (R 8) [66,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24029_5 : Upper (D 8) (R 8) [66,33,136,5] 13 :=
  permutation_upper _ _ _ [66,33,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19982

theorem m24029_17 : Upper (D 8) (R 8) [66,33,136,17] 13 :=
  permutation_upper _ _ _ [66,33,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19991

theorem m24029_20 : Upper (D 8) (R 8) [66,33,136,20] 13 :=
  permutation_upper _ _ _ [66,33,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20004

theorem m24029_33 : Upper (D 8) (R 8) [66,33,136,33] 13 :=
  permutation_upper _ _ _ [66,33,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20014

theorem m24029_36 : Upper (D 8) (R 8) [66,33,136,36] 13 :=
  permutation_upper _ _ _ [66,33,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20028

theorem m24029_48 : Upper (D 8) (R 8) [66,33,136,48] 13 :=
  permutation_upper _ _ _ [66,33,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20039

theorem m24029_65 : Upper (D 8) (R 8) [66,33,136,65] 13 :=
  permutation_upper _ _ _ [66,33,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20046

theorem m24029_68 : Upper (D 8) (R 8) [66,33,136,68] 13 :=
  permutation_upper _ _ _ [66,33,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20052

theorem m24029_80 : Upper (D 8) (R 8) [66,33,136,80] 13 :=
  permutation_upper _ _ _ [66,33,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20060

theorem m24029_96 : Upper (D 8) (R 8) [66,33,136,96] 13 :=
  permutation_upper _ _ _ [66,33,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20065

theorem m24029_129 : Upper (D 8) (R 8) [66,33,136,129] 13 :=
  permutation_upper _ _ _ [66,33,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20070

def r24029 : Route 9 := (fun mask => (mask,id))

def c24029 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u24029 : Upper (D 8) (R 8) [66,33,136] 13 := by
  apply FastRouting.sound _ _ [66,33,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r24029 c24029
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24029_5
  · exact m24029_17
  · exact m24029_20
  · exact m24029_33
  · exact m24029_36
  · exact m24029_48
  · exact m24029_65
  · exact m24029_68
  · exact m24029_80
  · exact m24029_96
  · exact m24029_129
  · exact u20077
  · exact u20078
  · exact u20079
  · exact u20080
  · exact u20081
  · exact u20082
  · exact u20083
  · exact u20084
  · exact u20085
  · exact u20086

theorem m24030_5 : Upper (D 8) (R 8) [66,33,160,5] 13 :=
  permutation_upper _ _ _ [66,33,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19983

theorem m24030_17 : Upper (D 8) (R 8) [66,33,160,17] 13 :=
  permutation_upper _ _ _ [66,33,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19992

theorem m24030_20 : Upper (D 8) (R 8) [66,33,160,20] 13 :=
  permutation_upper _ _ _ [66,33,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20005

theorem m24030_33 : Upper (D 8) (R 8) [66,33,160,33] 13 :=
  permutation_upper _ _ _ [66,33,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20015

theorem m24030_36 : Upper (D 8) (R 8) [66,33,160,36] 13 :=
  permutation_upper _ _ _ [66,33,40,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20030

theorem m24030_48 : Upper (D 8) (R 8) [66,33,160,48] 13 :=
  permutation_upper _ _ _ [66,33,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20040

theorem m24030_65 : Upper (D 8) (R 8) [66,33,160,65] 13 :=
  permutation_upper _ _ _ [66,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20047

theorem m24030_68 : Upper (D 8) (R 8) [66,33,160,68] 13 :=
  permutation_upper _ _ _ [66,33,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20054

theorem m24030_80 : Upper (D 8) (R 8) [66,33,160,80] 13 :=
  permutation_upper _ _ _ [66,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20061

theorem m24030_96 : Upper (D 8) (R 8) [66,33,160,96] 13 :=
  permutation_upper _ _ _ [66,33,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20066

theorem m24030_129 : Upper (D 8) (R 8) [66,33,160,129] 13 :=
  permutation_upper _ _ _ [66,33,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20071

theorem m24030_132 : Upper (D 8) (R 8) [66,33,160,132] 13 :=
  permutation_upper _ _ _ [66,33,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20079

theorem m24030_144 : Upper (D 8) (R 8) [66,33,160,144] 13 :=
  permutation_upper _ _ _ [66,33,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20087

def r24030 : Route 9 := (fun mask => (mask,id))

def c24030 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u24030 : Upper (D 8) (R 8) [66,33,160] 13 := by
  apply FastRouting.sound _ _ [66,33,160] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r24030 c24030
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24030_5
  · exact m24030_17
  · exact m24030_20
  · exact m24030_33
  · exact m24030_36
  · exact m24030_48
  · exact m24030_65
  · exact m24030_68
  · exact m24030_80
  · exact m24030_96
  · exact m24030_129
  · exact m24030_132
  · exact m24030_144
  · exact u20093
  · exact u20094
  · exact u20095
  · exact u20096
  · exact u20097
  · exact u20098
  · exact u20099
  · exact u20100

theorem m24031_5 : Upper (D 8) (R 8) [66,33,192,5] 13 :=
  permutation_upper _ _ _ [66,33,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19984

theorem m24031_17 : Upper (D 8) (R 8) [66,33,192,17] 13 :=
  permutation_upper _ _ _ [66,33,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19993

theorem m24031_20 : Upper (D 8) (R 8) [66,33,192,20] 13 :=
  permutation_upper _ _ _ [66,33,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20006

theorem m24031_33 : Upper (D 8) (R 8) [66,33,192,33] 13 :=
  permutation_upper _ _ _ [66,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20016

theorem m24031_36 : Upper (D 8) (R 8) [66,33,192,36] 13 :=
  permutation_upper _ _ _ [66,33,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20031

theorem m24031_48 : Upper (D 8) (R 8) [66,33,192,48] 13 :=
  permutation_upper _ _ _ [66,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20041

theorem m24031_129 : Upper (D 8) (R 8) [66,33,192,129] 13 :=
  permutation_upper _ _ _ [66,33,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20072

theorem m24031_132 : Upper (D 8) (R 8) [66,33,192,132] 13 :=
  permutation_upper _ _ _ [66,33,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20080

theorem m24031_144 : Upper (D 8) (R 8) [66,33,192,144] 13 :=
  permutation_upper _ _ _ [66,33,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20088

theorem m24031_160 : Upper (D 8) (R 8) [66,33,192,160] 13 :=
  permutation_upper _ _ _ [66,33,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20094

def r24031 : Route 9 := (fun mask => (mask,id))

def c24031 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u24031 : Upper (D 8) (R 8) [66,33,192] 13 := by
  apply FastRouting.sound _ _ [66,33,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r24031 c24031
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24031_5
  · exact m24031_17
  · exact m24031_20
  · exact m24031_33
  · exact m24031_36
  · exact m24031_48
  · exact m24031_129
  · exact m24031_132
  · exact m24031_144
  · exact m24031_160
  · exact u20101
  · exact u20102
  · exact u20103
  · exact u20104
  · exact u20105

def b24032 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 261 252 252 252 252 252 508), lower := (rows 67 35 261 8 16 32 64 128 256), losses := [] }

theorem u24032 : Upper (D 8) (R 8) [66,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24033_5 : Upper (D 8) (R 8) [66,33,264,5] 13 :=
  permutation_upper _ _ _ [66,33,9,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19985

theorem m24033_17 : Upper (D 8) (R 8) [66,33,264,17] 13 :=
  permutation_upper _ _ _ [66,33,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19994

theorem m24033_20 : Upper (D 8) (R 8) [66,33,264,20] 13 :=
  permutation_upper _ _ _ [66,33,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20008

theorem m24033_33 : Upper (D 8) (R 8) [66,33,264,33] 13 :=
  permutation_upper _ _ _ [66,33,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20017

theorem m24033_36 : Upper (D 8) (R 8) [66,33,264,36] 13 :=
  permutation_upper _ _ _ [66,33,40,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20033

theorem m24033_48 : Upper (D 8) (R 8) [66,33,264,48] 13 :=
  permutation_upper _ _ _ [66,33,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20042

theorem m24033_65 : Upper (D 8) (R 8) [66,33,264,65] 13 :=
  permutation_upper _ _ _ [66,33,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20048

theorem m24033_68 : Upper (D 8) (R 8) [66,33,264,68] 13 :=
  permutation_upper _ _ _ [66,33,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20056

theorem m24033_80 : Upper (D 8) (R 8) [66,33,264,80] 13 :=
  permutation_upper _ _ _ [66,33,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20062

theorem m24033_96 : Upper (D 8) (R 8) [66,33,264,96] 13 :=
  permutation_upper _ _ _ [66,33,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20067

theorem m24033_129 : Upper (D 8) (R 8) [66,33,264,129] 13 :=
  permutation_upper _ _ _ [66,33,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20073

theorem m24033_132 : Upper (D 8) (R 8) [66,33,264,132] 13 :=
  permutation_upper _ _ _ [66,33,136,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20082

theorem m24033_144 : Upper (D 8) (R 8) [66,33,264,144] 13 :=
  permutation_upper _ _ _ [66,33,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20089

theorem m24033_160 : Upper (D 8) (R 8) [66,33,264,160] 13 :=
  permutation_upper _ _ _ [66,33,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20096

theorem m24033_192 : Upper (D 8) (R 8) [66,33,264,192] 13 :=
  permutation_upper _ _ _ [66,33,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20102

def r24033 : Route 9 := (fun mask => (mask,id))

def c24033 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24033 : Upper (D 8) (R 8) [66,33,264] 13 := by
  apply FastRouting.sound _ _ [66,33,264] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24033 c24033
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24033_5
  · exact m24033_17
  · exact m24033_20
  · exact m24033_33
  · exact m24033_36
  · exact m24033_48
  · exact m24033_65
  · exact m24033_68
  · exact m24033_80
  · exact m24033_96
  · exact m24033_129
  · exact m24033_132
  · exact m24033_144
  · exact m24033_160
  · exact m24033_192

theorem m24034_5 : Upper (D 8) (R 8) [66,33,288,5] 13 :=
  permutation_upper _ _ _ [66,33,9,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19986

theorem m24034_17 : Upper (D 8) (R 8) [66,33,288,17] 13 :=
  permutation_upper _ _ _ [66,33,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19995

theorem m24034_20 : Upper (D 8) (R 8) [66,33,288,20] 13 :=
  permutation_upper _ _ _ [66,33,24,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20009

theorem m24034_33 : Upper (D 8) (R 8) [66,33,288,33] 13 :=
  permutation_upper _ _ _ [66,33,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20018

theorem m24034_36 : Upper (D 8) (R 8) [66,33,288,36] 13 :=
  permutation_upper _ _ _ [66,33,40,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20035

theorem m24034_48 : Upper (D 8) (R 8) [66,33,288,48] 13 :=
  permutation_upper _ _ _ [66,33,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20043

theorem m24034_65 : Upper (D 8) (R 8) [66,33,288,65] 13 :=
  permutation_upper _ _ _ [66,33,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20049

theorem m24034_68 : Upper (D 8) (R 8) [66,33,288,68] 13 :=
  permutation_upper _ _ _ [66,33,72,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20058

theorem m24034_80 : Upper (D 8) (R 8) [66,33,288,80] 13 :=
  permutation_upper _ _ _ [66,33,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20063

theorem m24034_96 : Upper (D 8) (R 8) [66,33,288,96] 13 :=
  permutation_upper _ _ _ [66,33,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20068

theorem m24034_129 : Upper (D 8) (R 8) [66,33,288,129] 13 :=
  permutation_upper _ _ _ [66,33,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20074

theorem m24034_132 : Upper (D 8) (R 8) [66,33,288,132] 13 :=
  permutation_upper _ _ _ [66,33,136,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20084

theorem m24034_144 : Upper (D 8) (R 8) [66,33,288,144] 13 :=
  permutation_upper _ _ _ [66,33,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20090

theorem m24034_160 : Upper (D 8) (R 8) [66,33,288,160] 13 :=
  permutation_upper _ _ _ [66,33,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20098

theorem m24034_192 : Upper (D 8) (R 8) [66,33,288,192] 13 :=
  permutation_upper _ _ _ [66,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20104

def r24034 : Route 9 := (fun mask => (mask,id))

def c24034 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24034 : Upper (D 8) (R 8) [66,33,288] 13 := by
  apply FastRouting.sound _ _ [66,33,288] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24034 c24034
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24034_5
  · exact m24034_17
  · exact m24034_20
  · exact m24034_33
  · exact m24034_36
  · exact m24034_48
  · exact m24034_65
  · exact m24034_68
  · exact m24034_80
  · exact m24034_96
  · exact m24034_129
  · exact m24034_132
  · exact m24034_144
  · exact m24034_160
  · exact m24034_192

theorem m24035_5 : Upper (D 8) (R 8) [66,33,320,5] 13 :=
  permutation_upper _ _ _ [66,33,9,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19987

theorem m24035_17 : Upper (D 8) (R 8) [66,33,320,17] 13 :=
  permutation_upper _ _ _ [66,33,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19996

theorem m24035_20 : Upper (D 8) (R 8) [66,33,320,20] 13 :=
  permutation_upper _ _ _ [66,33,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20010

theorem m24035_33 : Upper (D 8) (R 8) [66,33,320,33] 13 :=
  permutation_upper _ _ _ [66,33,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20019

theorem m24035_36 : Upper (D 8) (R 8) [66,33,320,36] 13 :=
  permutation_upper _ _ _ [66,33,40,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20036

theorem m24035_48 : Upper (D 8) (R 8) [66,33,320,48] 13 :=
  permutation_upper _ _ _ [66,33,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20044

theorem m24035_129 : Upper (D 8) (R 8) [66,33,320,129] 13 :=
  permutation_upper _ _ _ [66,33,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20075

theorem m24035_132 : Upper (D 8) (R 8) [66,33,320,132] 13 :=
  permutation_upper _ _ _ [66,33,136,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20085

theorem m24035_144 : Upper (D 8) (R 8) [66,33,320,144] 13 :=
  permutation_upper _ _ _ [66,33,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20091

theorem m24035_160 : Upper (D 8) (R 8) [66,33,320,160] 13 :=
  permutation_upper _ _ _ [66,33,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20099

def r24035 : Route 9 := (fun mask => (mask,id))

def c24035 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24035 : Upper (D 8) (R 8) [66,33,320] 13 := by
  apply FastRouting.sound _ _ [66,33,320] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r24035 c24035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24035_5
  · exact m24035_17
  · exact m24035_20
  · exact m24035_33
  · exact m24035_36
  · exact m24035_48
  · exact m24035_129
  · exact m24035_132
  · exact m24035_144
  · exact m24035_160

theorem m24036_5 : Upper (D 8) (R 8) [66,33,384,5] 13 :=
  permutation_upper _ _ _ [66,33,9,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19988

theorem m24036_17 : Upper (D 8) (R 8) [66,33,384,17] 13 :=
  permutation_upper _ _ _ [66,33,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19997

theorem m24036_20 : Upper (D 8) (R 8) [66,33,384,20] 13 :=
  permutation_upper _ _ _ [66,33,24,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20011

theorem m24036_33 : Upper (D 8) (R 8) [66,33,384,33] 13 :=
  permutation_upper _ _ _ [66,33,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20020

theorem m24036_36 : Upper (D 8) (R 8) [66,33,384,36] 13 :=
  permutation_upper _ _ _ [66,33,40,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20037

theorem m24036_48 : Upper (D 8) (R 8) [66,33,384,48] 13 :=
  permutation_upper _ _ _ [66,33,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20045

theorem m24036_65 : Upper (D 8) (R 8) [66,33,384,65] 13 :=
  permutation_upper _ _ _ [66,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20050

theorem m24036_68 : Upper (D 8) (R 8) [66,33,384,68] 13 :=
  permutation_upper _ _ _ [66,33,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20059

theorem m24036_80 : Upper (D 8) (R 8) [66,33,384,80] 13 :=
  permutation_upper _ _ _ [66,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20064

theorem m24036_96 : Upper (D 8) (R 8) [66,33,384,96] 13 :=
  permutation_upper _ _ _ [66,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20069

theorem m24036_129 : Upper (D 8) (R 8) [66,33,384,129] 13 :=
  permutation_upper _ _ _ [66,33,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20076

theorem m24036_132 : Upper (D 8) (R 8) [66,33,384,132] 13 :=
  permutation_upper _ _ _ [66,33,136,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20086

theorem m24036_144 : Upper (D 8) (R 8) [66,33,384,144] 13 :=
  permutation_upper _ _ _ [66,33,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20092

theorem m24036_160 : Upper (D 8) (R 8) [66,33,384,160] 13 :=
  permutation_upper _ _ _ [66,33,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20100

theorem m24036_192 : Upper (D 8) (R 8) [66,33,384,192] 13 :=
  permutation_upper _ _ _ [66,33,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20105

def r24036 : Route 9 := (fun mask => (mask,id))

def c24036 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24036 : Upper (D 8) (R 8) [66,33,384] 13 := by
  apply FastRouting.sound _ _ [66,33,384] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24036 c24036
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24036_5
  · exact m24036_17
  · exact m24036_20
  · exact m24036_33
  · exact m24036_36
  · exact m24036_48
  · exact m24036_65
  · exact m24036_68
  · exact m24036_80
  · exact m24036_96
  · exact m24036_129
  · exact m24036_132
  · exact m24036_144
  · exact m24036_160
  · exact m24036_192

def r24037 : Route 9 := (fun mask => (mask,id))

def c24037 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u24037 : Upper (D 8) (R 8) [66,36,9] 13 := by
  apply FastRouting.sound _ _ [66,36,9] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r24037 c24037
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20106
  · exact u20107
  · exact u20108
  · exact u20109
  · exact u20110
  · exact u20111
  · exact u20112
  · exact u20113
  · exact u20114
  · exact u20115
  · exact u20116
  · exact u20117
  · exact u20118
  · exact u20119
  · exact u20120

def r24038 : Route 9 := (fun mask => (mask,id))

def c24038 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u24038 : Upper (D 8) (R 8) [66,36,24] 13 := by
  apply FastRouting.sound _ _ [66,36,24] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r24038 c24038
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20121
  · exact u20122
  · exact u20123
  · exact u20124
  · exact u20125
  · exact u20126
  · exact u20127
  · exact u20128
  · exact u20129
  · exact u20130

def b24039 : PairBound 9 := { available := 505, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 37 505 505 505 505 505 505), lower := (rows 67 38 37 8 16 32 64 128 256), losses := [] }

theorem u24039 : Upper (D 8) (R 8) [66,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24040 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 44 505 497 497 497 497 497), lower := (rows 67 38 44 8 16 32 64 128 256), losses := [] }

theorem u24040 : Upper (D 8) (R 8) [66,36,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24041 : PairBound 9 := { available := 441, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 69 441 441 441 505 441 441), lower := (rows 67 38 69 8 16 32 64 128 256), losses := [] }

theorem u24041 : Upper (D 8) (R 8) [66,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24042 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 76 441 433 433 497 433 433), lower := (rows 67 38 76 8 16 32 64 128 256), losses := [] }

theorem u24042 : Upper (D 8) (R 8) [66,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24043 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 100 441 441 441 505 441 441), lower := (rows 67 38 100 8 16 32 64 128 256), losses := [] }

theorem u24043 : Upper (D 8) (R 8) [66,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24044 : Route 9 := (fun mask => (mask,id))

def c24044 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u24044 : Upper (D 8) (R 8) [66,36,129] 13 := by
  apply FastRouting.sound _ _ [66,36,129] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r24044 c24044
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20131
  · exact u20132
  · exact u20133
  · exact u20134
  · exact u20135
  · exact u20136
  · exact u20137
  · exact u20138
  · exact u20139
  · exact u20140
  · exact u20141
  · exact u20142
  · exact u20143
  · exact u20144
  · exact u20145

def r24045 : Route 9 := (fun mask => (mask,id))

def c24045 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u24045 : Upper (D 8) (R 8) [66,36,136] 13 := by
  apply FastRouting.sound _ _ [66,36,136] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r24045 c24045
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20146
  · exact u20147
  · exact u20148
  · exact u20149
  · exact u20150
  · exact u20151
  · exact u20152
  · exact u20153
  · exact u20154
  · exact u20155
  · exact u20156
  · exact u20157
  · exact u20158
  · exact u20159
  · exact u20160

def b24046 : PairBound 9 := { available := 505, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 164 505 505 505 505 505 505), lower := (rows 67 38 164 8 16 32 64 128 256), losses := [] }

theorem u24046 : Upper (D 8) (R 8) [66,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24047 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 196 441 441 441 505 441 441), lower := (rows 67 38 196 8 16 32 64 128 256), losses := [] }

theorem u24047 : Upper (D 8) (R 8) [66,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24048 : Route 9 := (fun mask => (mask,id))

def c24048 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24048 : Upper (D 8) (R 8) [66,36,257] 13 := by
  apply FastRouting.sound _ _ [66,36,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24048 c24048
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20161
  · exact u20162
  · exact u20163
  · exact u20164
  · exact u20165
  · exact u20166
  · exact u20167
  · exact u20168
  · exact u20169
  · exact u20170

def r24049 : Route 9 := (fun mask => (mask,id))

def c24049 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24049 : Upper (D 8) (R 8) [66,36,264] 13 := by
  apply FastRouting.sound _ _ [66,36,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24049 c24049
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20171
  · exact u20172
  · exact u20173
  · exact u20174
  · exact u20175
  · exact u20176
  · exact u20177
  · exact u20178
  · exact u20179
  · exact u20180

def b24050 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 292 249 249 249 249 249 505), lower := (rows 67 38 292 8 16 32 64 128 256), losses := [] }

theorem u24050 : Upper (D 8) (R 8) [66,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24051 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 324 185 185 185 249 185 441), lower := (rows 67 38 324 8 16 32 64 128 256), losses := [] }

theorem u24051 : Upper (D 8) (R 8) [66,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24052 : Route 9 := (fun mask => (mask,id))

def c24052 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24052 : Upper (D 8) (R 8) [66,36,384] 13 := by
  apply FastRouting.sound _ _ [66,36,384] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24052 c24052
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u20181
  · exact u20182
  · exact u20183
  · exact u20184
  · exact u20185
  · exact u20186
  · exact u20187
  · exact u20188
  · exact u20189
  · exact u20190

def b24053 : PairBound 9 := { available := 500, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 508 500 500 500 500 500), lower := (rows 67 131 13 8 16 32 64 128 256), losses := [] }

theorem u24053 : Upper (D 8) (R 8) [66,129,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24054_5 : Upper (D 8) (R 8) [66,129,24,5] 13 :=
  permutation_upper _ _ _ [66,129,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20191

def r24054 : Route 9 := (fun mask => (mask,id))

def c24054 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u24054 : Upper (D 8) (R 8) [66,129,24] 13 := by
  apply FastRouting.sound _ _ [66,129,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r24054 c24054
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24054_5
  · exact u20210
  · exact u20211
  · exact u20212
  · exact u20213
  · exact u20214
  · exact u20215
  · exact u20216
  · exact u20217
  · exact u20218
  · exact u20219
  · exact u20220
  · exact u20221
  · exact u20222
  · exact u20223

def b24055 : PairBound 9 := { available := 508, camps := [{ cop := 2, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 37 508 508 508 508 508 508), lower := (rows 67 131 37 8 16 32 64 128 256), losses := [] }

theorem u24055 : Upper (D 8) (R 8) [66,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24056_5 : Upper (D 8) (R 8) [66,129,40,5] 13 :=
  permutation_upper _ _ _ [66,129,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20192

theorem m24056_17 : Upper (D 8) (R 8) [66,129,40,17] 13 :=
  permutation_upper _ _ _ [66,129,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20201

theorem m24056_20 : Upper (D 8) (R 8) [66,129,40,20] 13 :=
  permutation_upper _ _ _ [66,129,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20211

theorem m24056_33 : Upper (D 8) (R 8) [66,129,40,33] 13 :=
  permutation_upper _ _ _ [66,129,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20224

def r24056 : Route 9 := (fun mask => (mask,id))

def c24056 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u24056 : Upper (D 8) (R 8) [66,129,40] 13 := by
  apply FastRouting.sound _ _ [66,129,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r24056 c24056
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24056_5
  · exact m24056_17
  · exact m24056_20
  · exact m24056_33
  · exact u20233
  · exact u20234
  · exact u20235
  · exact u20236
  · exact u20237
  · exact u20238
  · exact u20239
  · exact u20240
  · exact u20241
  · exact u20242
  · exact u20243
  · exact u20244
  · exact u20245
  · exact u20246
  · exact u20247
  · exact u20248
  · exact u20249

def b24057 : PairBound 9 := { available := 444, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 69 444 444 444 508 444 444), lower := (rows 67 131 69 8 16 32 64 128 256), losses := [] }

theorem u24057 : Upper (D 8) (R 8) [66,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24058_5 : Upper (D 8) (R 8) [66,129,72,5] 13 :=
  permutation_upper _ _ _ [66,129,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20193

theorem m24058_17 : Upper (D 8) (R 8) [66,129,72,17] 13 :=
  permutation_upper _ _ _ [66,129,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20202

theorem m24058_20 : Upper (D 8) (R 8) [66,129,72,20] 13 :=
  permutation_upper _ _ _ [66,129,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20213

theorem m24058_33 : Upper (D 8) (R 8) [66,129,72,33] 13 :=
  permutation_upper _ _ _ [66,129,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20225

theorem m24058_36 : Upper (D 8) (R 8) [66,129,72,36] 13 :=
  permutation_upper _ _ _ [66,129,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20236

theorem m24058_48 : Upper (D 8) (R 8) [66,129,72,48] 13 :=
  permutation_upper _ _ _ [66,129,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20250

def r24058 : Route 9 := (fun mask => (mask,id))

def c24058 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u24058 : Upper (D 8) (R 8) [66,129,72] 13 := by
  apply FastRouting.sound _ _ [66,129,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r24058 c24058
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24058_5
  · exact m24058_17
  · exact m24058_20
  · exact m24058_33
  · exact m24058_36
  · exact m24058_48
  · exact u20263
  · exact u20264
  · exact u20265
  · exact u20266
  · exact u20267
  · exact u20268
  · exact u20269
  · exact u20270
  · exact u20271

theorem m24059_5 : Upper (D 8) (R 8) [66,129,96,5] 13 :=
  permutation_upper _ _ _ [66,129,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20194

theorem m24059_17 : Upper (D 8) (R 8) [66,129,96,17] 13 :=
  permutation_upper _ _ _ [66,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20203

theorem m24059_20 : Upper (D 8) (R 8) [66,129,96,20] 13 :=
  permutation_upper _ _ _ [66,129,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20214

theorem m24059_33 : Upper (D 8) (R 8) [66,129,96,33] 13 :=
  permutation_upper _ _ _ [66,129,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20226

theorem m24059_36 : Upper (D 8) (R 8) [66,129,96,36] 13 :=
  permutation_upper _ _ _ [66,129,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20238

theorem m24059_48 : Upper (D 8) (R 8) [66,129,96,48] 13 :=
  permutation_upper _ _ _ [66,129,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20251

def r24059 : Route 9 := (fun mask => (mask,id))

def c24059 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u24059 : Upper (D 8) (R 8) [66,129,96] 13 := by
  apply FastRouting.sound _ _ [66,129,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r24059 c24059
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24059_5
  · exact m24059_17
  · exact m24059_20
  · exact m24059_33
  · exact m24059_36
  · exact m24059_48
  · exact u20277
  · exact u20278
  · exact u20279
  · exact u20280
  · exact u20281
  · exact u20282
  · exact u20283
  · exact u20284
  · exact u20285

#print axioms u24059
end Delivery.IrregularNine14.P08
