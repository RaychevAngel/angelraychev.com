import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0731
import IrregularNine14P07C0732
import IrregularNine14P07C0733
import IrregularNine14P07C0734
import IrregularNine14P07C0735
import IrregularNine14P07C0736
import IrregularNine14P07C0737
import IrregularNine14P07C0738
import IrregularNine14P07C0739

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m44400_3 : Upper (D 7) (R 7) [96,384,9,3] 13 :=
  permutation_upper _ _ _ [96,384,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43902

def r44400 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44400 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44400 : Upper (D 7) (R 7) [96,384,9] 13 := by
  apply FastRouting.sound _ _ [96,384,9] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,129,130,132,144,160] r44400 c44400
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44400_3
  · exact u43917
  · exact u43918
  · exact u43919
  · exact u43920
  · exact u43921
  · exact u43922
  · exact u43923
  · exact u43924
  · exact u43925
  · exact u43926
  · exact u43927
  · exact u43928
  · exact u43929
  · exact u43930
  · exact u43931

theorem m44401_3 : Upper (D 7) (R 7) [96,384,10,3] 13 :=
  permutation_upper _ _ _ [96,384,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43903

theorem m44401_5 : Upper (D 7) (R 7) [96,384,10,5] 13 :=
  permutation_upper _ _ _ [96,384,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43918

def r44401 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44401 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44401 : Upper (D 7) (R 7) [96,384,10] 13 := by
  apply FastRouting.sound _ _ [96,384,10] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,129,130,132,144,160] r44401 c44401
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44401_3
  · exact m44401_5
  · exact u43932
  · exact u43933
  · exact u43934
  · exact u43935
  · exact u43936
  · exact u43937
  · exact u43938
  · exact u43939
  · exact u43940
  · exact u43941
  · exact u43942
  · exact u43943
  · exact u43944
  · exact u43945

theorem m44402_3 : Upper (D 7) (R 7) [96,384,24,3] 13 :=
  permutation_upper _ _ _ [96,384,3,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43906

theorem m44402_5 : Upper (D 7) (R 7) [96,384,24,5] 13 :=
  permutation_upper _ _ _ [96,384,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43921

theorem m44402_6 : Upper (D 7) (R 7) [96,384,24,6] 13 :=
  permutation_upper _ _ _ [96,384,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43935

def r44402 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44402 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44402 : Upper (D 7) (R 7) [96,384,24] 13 := by
  apply FastRouting.sound _ _ [96,384,24] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r44402 c44402
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44402_3
  · exact m44402_5
  · exact m44402_6
  · exact u43956
  · exact u43957
  · exact u43958
  · exact u43959
  · exact u43960
  · exact u43961
  · exact u43962
  · exact u43963

def b44403 : PairBound 9 := { available := 223, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 386 37 223 223 255 223 223 479), lower := (rows 97 386 37 8 16 32 64 128 256), losses := [] }

theorem u44403 : Upper (D 7) (R 7) [96,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44404_3 : Upper (D 7) (R 7) [96,384,34,3] 13 :=
  permutation_upper _ _ _ [96,384,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43908

theorem m44404_5 : Upper (D 7) (R 7) [96,384,34,5] 13 :=
  permutation_upper _ _ _ [96,384,9,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43923

theorem m44404_6 : Upper (D 7) (R 7) [96,384,34,6] 13 :=
  permutation_upper _ _ _ [96,384,10,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43937

theorem m44404_17 : Upper (D 7) (R 7) [96,384,34,17] 13 :=
  permutation_upper _ _ _ [96,384,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43946

theorem m44404_18 : Upper (D 7) (R 7) [96,384,34,18] 13 :=
  permutation_upper _ _ _ [96,384,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43951

theorem m44404_20 : Upper (D 7) (R 7) [96,384,34,20] 13 :=
  permutation_upper _ _ _ [96,384,24,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43957

theorem m44404_65 : Upper (D 7) (R 7) [96,384,34,65] 13 :=
  permutation_upper _ _ _ [96,384,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43964

def r44404 : Route 9 := (fun mask => (mask,id))

def c44404 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44404 : Upper (D 7) (R 7) [96,384,34] 13 := by
  apply FastRouting.sound _ _ [96,384,34] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44404 c44404
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44404_3
  · exact m44404_5
  · exact m44404_6
  · exact m44404_17
  · exact m44404_18
  · exact m44404_20
  · exact m44404_65
  · exact u43969
  · exact u43970
  · exact u43971
  · exact u43972
  · exact u43973
  · exact u43974
  · exact u43975
  · exact u43976

theorem m44405_3 : Upper (D 7) (R 7) [96,384,40,3] 13 :=
  permutation_upper _ _ _ [96,384,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43909

theorem m44405_5 : Upper (D 7) (R 7) [96,384,40,5] 13 :=
  permutation_upper _ _ _ [96,384,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43924

theorem m44405_6 : Upper (D 7) (R 7) [96,384,40,6] 13 :=
  permutation_upper _ _ _ [96,384,10,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43938

theorem m44405_17 : Upper (D 7) (R 7) [96,384,40,17] 13 :=
  permutation_upper _ _ _ [96,384,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43947

theorem m44405_18 : Upper (D 7) (R 7) [96,384,40,18] 13 :=
  permutation_upper _ _ _ [96,384,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43952

theorem m44405_20 : Upper (D 7) (R 7) [96,384,40,20] 13 :=
  permutation_upper _ _ _ [96,384,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43958

theorem m44405_65 : Upper (D 7) (R 7) [96,384,40,65] 13 :=
  permutation_upper _ _ _ [96,384,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43965

theorem m44405_66 : Upper (D 7) (R 7) [96,384,40,66] 13 :=
  permutation_upper _ _ _ [96,384,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43970

def r44405 : Route 9 := (fun mask => (mask,id))

def c44405 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44405 : Upper (D 7) (R 7) [96,384,40] 13 := by
  apply FastRouting.sound _ _ [96,384,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44405 c44405
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44405_3
  · exact m44405_5
  · exact m44405_6
  · exact m44405_17
  · exact m44405_18
  · exact m44405_20
  · exact m44405_65
  · exact m44405_66
  · exact u43977
  · exact u43978
  · exact u43979
  · exact u43980
  · exact u43981
  · exact u43982
  · exact u43983

def b44406 : PairBound 9 := { available := 159, camps := [{ cop := 0, region := 4, targets := 130 },{ cop := 2, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 386 100 159 159 191 223 159 415), lower := (rows 97 386 100 8 16 32 64 128 256), losses := [] }

theorem u44406 : Upper (D 7) (R 7) [96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44407_3 : Upper (D 7) (R 7) [96,384,129,3] 13 :=
  permutation_upper _ _ _ [96,384,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43912

theorem m44407_5 : Upper (D 7) (R 7) [96,384,129,5] 13 :=
  permutation_upper _ _ _ [96,384,9,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43927

theorem m44407_6 : Upper (D 7) (R 7) [96,384,129,6] 13 :=
  permutation_upper _ _ _ [96,384,10,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43941

theorem m44407_17 : Upper (D 7) (R 7) [96,384,129,17] 13 :=
  permutation_upper _ _ _ [96,384,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43948

theorem m44407_18 : Upper (D 7) (R 7) [96,384,129,18] 13 :=
  permutation_upper _ _ _ [96,384,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43953

theorem m44407_20 : Upper (D 7) (R 7) [96,384,129,20] 13 :=
  permutation_upper _ _ _ [96,384,24,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43960

theorem m44407_33 : Upper (D 7) (R 7) [96,384,129,33] 13 :=
  permutation_upper _ _ _ [96,384,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43966

theorem m44407_34 : Upper (D 7) (R 7) [96,384,129,34] 13 :=
  permutation_upper _ _ _ [96,384,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43972

theorem m44407_36 : Upper (D 7) (R 7) [96,384,129,36] 13 :=
  permutation_upper _ _ _ [96,384,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43979

theorem m44407_48 : Upper (D 7) (R 7) [96,384,129,48] 13 :=
  permutation_upper _ _ _ [96,384,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43984

theorem m44407_96 : Upper (D 7) (R 7) [96,384,129,96] 13 :=
  permutation_upper _ _ _ [96,384,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43987

def r44407 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44407 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u44407 : Upper (D 7) (R 7) [96,384,129] 13 := by
  apply FastRouting.sound _ _ [96,384,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96] r44407 c44407
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44407_3
  · exact m44407_5
  · exact m44407_6
  · exact m44407_17
  · exact m44407_18
  · exact m44407_20
  · exact m44407_33
  · exact m44407_34
  · exact m44407_36
  · exact m44407_48
  · exact m44407_96

def b44408 : PairBound 9 := { available := 127, camps := [{ cop := 1, region := 4, targets := 97 },{ cop := 2, region := 121, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6)], upper := (rows 97 386 134 127 127 127 127 255 383), lower := (rows 97 386 134 8 16 32 64 128 256), losses := [] }

theorem u44408 : Upper (D 7) (R 7) [96,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44409_3 : Upper (D 7) (R 7) [96,384,136,3] 13 :=
  permutation_upper _ _ _ [96,384,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43914

theorem m44409_5 : Upper (D 7) (R 7) [96,384,136,5] 13 :=
  permutation_upper _ _ _ [96,384,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43929

theorem m44409_6 : Upper (D 7) (R 7) [96,384,136,6] 13 :=
  permutation_upper _ _ _ [96,384,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43943

theorem m44409_17 : Upper (D 7) (R 7) [96,384,136,17] 13 :=
  permutation_upper _ _ _ [96,384,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43949

theorem m44409_18 : Upper (D 7) (R 7) [96,384,136,18] 13 :=
  permutation_upper _ _ _ [96,384,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43954

theorem m44409_20 : Upper (D 7) (R 7) [96,384,136,20] 13 :=
  permutation_upper _ _ _ [96,384,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43962

theorem m44409_33 : Upper (D 7) (R 7) [96,384,136,33] 13 :=
  permutation_upper _ _ _ [96,384,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43967

theorem m44409_34 : Upper (D 7) (R 7) [96,384,136,34] 13 :=
  permutation_upper _ _ _ [96,384,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43974

theorem m44409_36 : Upper (D 7) (R 7) [96,384,136,36] 13 :=
  permutation_upper _ _ _ [96,384,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43981

theorem m44409_48 : Upper (D 7) (R 7) [96,384,136,48] 13 :=
  permutation_upper _ _ _ [96,384,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43985

theorem m44409_96 : Upper (D 7) (R 7) [96,384,136,96] 13 :=
  permutation_upper _ _ _ [96,384,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43988

def r44409 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44409 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u44409 : Upper (D 7) (R 7) [96,384,136] 13 := by
  apply FastRouting.sound _ _ [96,384,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96] r44409 c44409
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44409_3
  · exact m44409_5
  · exact m44409_6
  · exact m44409_17
  · exact m44409_18
  · exact m44409_20
  · exact m44409_33
  · exact m44409_34
  · exact m44409_36
  · exact m44409_48
  · exact m44409_96

theorem m44410_3 : Upper (D 7) (R 7) [96,384,160,3] 13 :=
  permutation_upper _ _ _ [96,384,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43916

theorem m44410_5 : Upper (D 7) (R 7) [96,384,160,5] 13 :=
  permutation_upper _ _ _ [96,384,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43931

theorem m44410_6 : Upper (D 7) (R 7) [96,384,160,6] 13 :=
  permutation_upper _ _ _ [96,384,10,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43945

theorem m44410_17 : Upper (D 7) (R 7) [96,384,160,17] 13 :=
  permutation_upper _ _ _ [96,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43950

theorem m44410_18 : Upper (D 7) (R 7) [96,384,160,18] 13 :=
  permutation_upper _ _ _ [96,384,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43955

theorem m44410_20 : Upper (D 7) (R 7) [96,384,160,20] 13 :=
  permutation_upper _ _ _ [96,384,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43963

theorem m44410_65 : Upper (D 7) (R 7) [96,384,160,65] 13 :=
  permutation_upper _ _ _ [96,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43968

theorem m44410_66 : Upper (D 7) (R 7) [96,384,160,66] 13 :=
  permutation_upper _ _ _ [96,384,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43976

theorem m44410_68 : Upper (D 7) (R 7) [96,384,160,68] 13 :=
  permutation_upper _ _ _ [96,384,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43983

theorem m44410_80 : Upper (D 7) (R 7) [96,384,160,80] 13 :=
  permutation_upper _ _ _ [96,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43986

def r44410 : Route 9 := (fun mask => (mask,id))

def c44410 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u44410 : Upper (D 7) (R 7) [96,384,160] 13 := by
  apply FastRouting.sound _ _ [96,384,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r44410 c44410
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44410_3
  · exact m44410_5
  · exact m44410_6
  · exact m44410_17
  · exact m44410_18
  · exact m44410_20
  · exact m44410_65
  · exact m44410_66
  · exact m44410_68
  · exact m44410_80

def r44411 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44411 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u44411 : Upper (D 7) (R 7) [6,9] 13 := by
  apply FastRouting.sound _ _ [6,9] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,257,258,272,288] r44411 c44411
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43989
  · exact u43990
  · exact u43991
  · exact u43992
  · exact u43993
  · exact u43994
  · exact u43995
  · exact u43996
  · exact u43997
  · exact u43998
  · exact u43999

def r44412 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44412 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44412 : Upper (D 7) (R 7) [6,24] 13 := by
  apply FastRouting.sound _ _ [6,24] 13 (by decide) (choices 2) [3,33,34,96,257,258,288] r44412 c44412
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44000
  · exact u44001
  · exact u44002
  · exact u44003
  · exact u44004
  · exact u44005
  · exact u44006

def r44413 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44413 : Nat → Fin 9 := (fun _ => 0)

theorem u44413 : Upper (D 7) (R 7) [6,33] 13 := by
  apply FastRouting.sound _ _ [6,33] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,192,257,258,264,288,320] r44413 c44413
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44007
  · exact u44008
  · exact u44009
  · exact u44010
  · exact u44011
  · exact u44012
  · exact u44013
  · exact u44014
  · exact u44015
  · exact u44016
  · exact u44017
  · exact u44018
  · exact u44019
  · exact u44020
  · exact u44021
  · exact u44022
  · exact u44023

def r44414 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44414 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u44414 : Upper (D 7) (R 7) [6,40] 13 := by
  apply FastRouting.sound _ _ [6,40] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r44414 c44414
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44024
  · exact u44025
  · exact u44026
  · exact u44027
  · exact u44028
  · exact u44029
  · exact u44030
  · exact u44031
  · exact u44032
  · exact u44033
  · exact u44034
  · exact u44035
  · exact u44036
  · exact u44037
  · exact u44038
  · exact u44039

def r44415 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44415 : Nat → Fin 9 := (fun _ => 0)

theorem u44415 : Upper (D 7) (R 7) [6,96] 13 := by
  apply FastRouting.sound _ _ [6,96] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,96,129,130,136,160,257,258,264,288,384] r44415 c44415
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44040
  · exact u44041
  · exact u44042
  · exact u44043
  · exact u44044
  · exact u44045
  · exact u44046
  · exact u44047
  · exact u44048
  · exact u44049
  · exact u44050
  · exact u44051
  · exact u44052
  · exact u44053
  · exact u44054
  · exact u44055
  · exact u44056

def r44416 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44416 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44416 : Upper (D 7) (R 7) [6,257] 13 := by
  apply FastRouting.sound _ _ [6,257] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,96] r44416 c44416
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44057
  · exact u44058
  · exact u44059
  · exact u44060
  · exact u44061
  · exact u44062
  · exact u44063
  · exact u44064

def r44417 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44417 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44417 : Upper (D 7) (R 7) [6,264] 13 := by
  apply FastRouting.sound _ _ [6,264] 13 (by decide) (choices 2) [3,17,18,33,34,48,96] r44417 c44417
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44065
  · exact u44066
  · exact u44067
  · exact u44068
  · exact u44069
  · exact u44070
  · exact u44071

def r44418 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44418 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44418 : Upper (D 7) (R 7) [6,288] 13 := by
  apply FastRouting.sound _ _ [6,288] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,192] r44418 c44418
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44072
  · exact u44073
  · exact u44074
  · exact u44075
  · exact u44076
  · exact u44077
  · exact u44078
  · exact u44079
  · exact u44080
  · exact u44081
  · exact u44082
  · exact u44083

def r44419 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44419 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u44419 : Upper (D 7) (R 7) [12,33] 13 := by
  apply FastRouting.sound _ _ [12,33] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r44419 c44419
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44084
  · exact u44085
  · exact u44086
  · exact u44087
  · exact u44088
  · exact u44089
  · exact u44090
  · exact u44091
  · exact u44092
  · exact u44093
  · exact u44094
  · exact u44095
  · exact u44096
  · exact u44097
  · exact u44098
  · exact u44099

def r44420 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44420 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44420 : Upper (D 7) (R 7) [12,48] 13 := by
  apply FastRouting.sound _ _ [12,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r44420 c44420
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44100
  · exact u44101
  · exact u44102
  · exact u44103
  · exact u44104
  · exact u44105
  · exact u44106
  · exact u44107
  · exact u44108
  · exact u44109
  · exact u44110

def r44421 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44421 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u44421 : Upper (D 7) (R 7) [12,96] 13 := by
  apply FastRouting.sound _ _ [12,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160,257,258,272,288,384] r44421 c44421
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44111
  · exact u44112
  · exact u44113
  · exact u44114
  · exact u44115
  · exact u44116
  · exact u44117
  · exact u44118
  · exact u44119
  · exact u44120
  · exact u44121
  · exact u44122
  · exact u44123
  · exact u44124
  · exact u44125
  · exact u44126

def r44422 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44422 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44422 : Upper (D 7) (R 7) [12,257] 13 := by
  apply FastRouting.sound _ _ [12,257] 13 (by decide) (choices 2) [3,17,18,33,34,48,96] r44422 c44422
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44127
  · exact u44128
  · exact u44129
  · exact u44130
  · exact u44131
  · exact u44132
  · exact u44133

def r44423 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44423 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 17 => 4 | 257 => 8 | 10 => 3 | 18 => 4 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44423 : Upper (D 7) (R 7) [12,272] 13 := by
  apply FastRouting.sound _ _ [12,272] 13 (by decide) (choices 2) [3,33,34,96] r44423 c44423
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u44134
  · exact u44135
  · exact u44136
  · exact u44137

def r44424 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44424 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44424 : Upper (D 7) (R 7) [12,288] 13 := by
  apply FastRouting.sound _ _ [12,288] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44424 c44424
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44138
  · exact u44139
  · exact u44140
  · exact u44141
  · exact u44142
  · exact u44143
  · exact u44144
  · exact u44145
  · exact u44146
  · exact u44147
  · exact u44148

def b44425 : PairBound 9 := { available := 479, camps := [{ cop := 5, region := 3, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 35 479 479 479 511 479 479 479), lower := (rows 35 35 4 8 16 32 64 128 256), losses := [] }

theorem u44425 : Upper (D 7) (R 7) [34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44426 : PairBound 9 := { available := 475, camps := [{ cop := 0, region := 476, targets := 32 },{ cop := 1, region := 1, targets := 64 }], pairs := [(0,6),(2,5),(3,5),(4,5)], upper := (rows 35 38 479 475 475 507 475 475 475), lower := (rows 35 38 4 8 16 32 64 128 256), losses := [] }

theorem u44426 : Upper (D 7) (R 7) [34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44427_10 : Upper (D 7) (R 7) [34,65,10] 13 :=
  permutation_upper _ _ _ [34,65,9] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44150

theorem m44427_65 : Upper (D 7) (R 7) [34,65,65] 13 :=
  permutation_upper _ _ _ [34,65,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44153

theorem m44427_66 : Upper (D 7) (R 7) [34,65,66] 13 :=
  permutation_upper _ _ _ [34,65,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44152

theorem m44427_72 : Upper (D 7) (R 7) [34,65,72] 13 :=
  permutation_upper _ _ _ [34,65,40] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44154

theorem m44427_130 : Upper (D 7) (R 7) [34,65,130] 13 :=
  permutation_upper _ _ _ [34,65,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44156

theorem m44427_192 : Upper (D 7) (R 7) [34,65,192] 13 :=
  permutation_upper _ _ _ [34,65,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44158

theorem m44427_258 : Upper (D 7) (R 7) [34,65,258] 13 :=
  permutation_upper _ _ _ [34,65,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44159

theorem m44427_320 : Upper (D 7) (R 7) [34,65,320] 13 :=
  permutation_upper _ _ _ [34,65,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44161

def r44427 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c44427 : Nat → Fin 9 := (fun _ => 0)

theorem u44427 : Upper (D 7) (R 7) [34,65] 13 := by
  apply FastRouting.sound _ _ [34,65] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,129,130,136,160,192,257,258,264,288,320,384] r44427 c44427
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44149
  · exact u44150
  · exact m44427_10
  · exact u44151
  · exact u44152
  · exact u44153
  · exact u44154
  · exact m44427_65
  · exact m44427_66
  · exact m44427_72
  · exact u44155
  · exact u44156
  · exact m44427_130
  · exact u44157
  · exact u44158
  · exact m44427_192
  · exact u44159
  · exact m44427_258
  · exact u44160
  · exact u44161
  · exact m44427_320
  · exact u44162

def r44428 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c44428 : Nat → Fin 9 := (fun _ => 0)

theorem u44428 : Upper (D 7) (R 7) [34,68] 13 := by
  apply FastRouting.sound _ _ [34,68] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,129,130,136,160,192,257,258,264,288,320,384] r44428 c44428
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44163
  · exact u44164
  · exact u44165
  · exact u44166
  · exact u44167
  · exact u44168
  · exact u44169
  · exact u44170
  · exact u44171
  · exact u44172
  · exact u44173
  · exact u44174
  · exact u44175
  · exact u44176
  · exact u44177
  · exact u44178
  · exact u44179
  · exact u44180
  · exact u44181
  · exact u44182
  · exact u44183
  · exact u44184

def b44429 : PairBound 9 := { available := 479, camps := [{ cop := 0, region := 476, targets := 32 },{ cop := 1, region := 1, targets := 64 }], pairs := [(0,6),(2,5),(3,5),(4,5)], upper := (rows 35 98 479 479 479 511 479 479 479), lower := (rows 35 98 4 8 16 32 64 128 256), losses := [] }

theorem u44429 : Upper (D 7) (R 7) [34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44430 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44430 : Nat → Fin 9 := (fun _ => 0)

theorem u44430 : Upper (D 7) (R 7) [34,192] 13 := by
  apply FastRouting.sound _ _ [34,192] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,192,257,258,264,288,320] r44430 c44430
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44185
  · exact u44186
  · exact u44187
  · exact u44188
  · exact u44189
  · exact u44190
  · exact u44191
  · exact u44192
  · exact u44193
  · exact u44194
  · exact u44195
  · exact u44196
  · exact u44197
  · exact u44198
  · exact u44199
  · exact u44200
  · exact u44201

def r44431 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44431 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44431 : Upper (D 7) (R 7) [34,257] 13 := by
  apply FastRouting.sound _ _ [34,257] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,192] r44431 c44431
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44202
  · exact u44203
  · exact u44204
  · exact u44205
  · exact u44206
  · exact u44207
  · exact u44208
  · exact u44209
  · exact u44210
  · exact u44211
  · exact u44212
  · exact u44213

def r44432 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44432 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44432 : Upper (D 7) (R 7) [34,260] 13 := by
  apply FastRouting.sound _ _ [34,260] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,192] r44432 c44432
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44214
  · exact u44215
  · exact u44216
  · exact u44217
  · exact u44218
  · exact u44219
  · exact u44220
  · exact u44221
  · exact u44222
  · exact u44223
  · exact u44224
  · exact u44225

def b44433 : PairBound 9 := { available := 223, camps := [{ cop := 0, region := 220, targets := 32 },{ cop := 1, region := 1, targets := 64 }], pairs := [(0,6),(2,5),(3,5),(4,5)], upper := (rows 35 290 223 223 223 255 223 223 479), lower := (rows 35 290 4 8 16 32 64 128 256), losses := [] }

theorem u44433 : Upper (D 7) (R 7) [34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44434 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c44434 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44434 : Upper (D 7) (R 7) [34,320] 13 := by
  apply FastRouting.sound _ _ [34,320] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,129,130,136,160,192] r44434 c44434
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44226
  · exact u44227
  · exact u44228
  · exact u44229
  · exact u44230
  · exact u44231
  · exact u44232
  · exact u44233
  · exact u44234
  · exact u44235
  · exact u44236
  · exact u44237
  · exact u44238
  · exact u44239
  · exact u44240
  · exact u44241

def r44435 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44435 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44435 : Upper (D 7) (R 7) [36,40] 13 := by
  apply FastRouting.sound _ _ [36,40] 13 (by decide) (choices 2) [3,17,18,65,66,80,192,257,258,272,320] r44435 c44435
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44242
  · exact u44243
  · exact u44244
  · exact u44245
  · exact u44246
  · exact u44247
  · exact u44248
  · exact u44249
  · exact u44250
  · exact u44251
  · exact u44252

def r44436 : Route 9 := (fun mask => (mask,id))

def c44436 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u44436 : Upper (D 7) (R 7) [36,72] 13 := by
  apply FastRouting.sound _ _ [36,72] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192,257,258,272,288,320,384] r44436 c44436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44253
  · exact u44254
  · exact u44255
  · exact u44256
  · exact u44257
  · exact u44258
  · exact u44259
  · exact u44260
  · exact u44261
  · exact u44262
  · exact u44263
  · exact u44264
  · exact u44265
  · exact u44266
  · exact u44267
  · exact u44268
  · exact u44269
  · exact u44270
  · exact u44271
  · exact u44272
  · exact u44273

def r44437 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c44437 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44437 : Upper (D 7) (R 7) [36,96] 13 := by
  apply FastRouting.sound _ _ [36,96] 13 (by decide) (choices 2) [3,9,10,24,65,66,72,129,130,136,192,257,258,264,320,384] r44437 c44437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44274
  · exact u44275
  · exact u44276
  · exact u44277
  · exact u44278
  · exact u44279
  · exact u44280
  · exact u44281
  · exact u44282
  · exact u44283
  · exact u44284
  · exact u44285
  · exact u44286
  · exact u44287
  · exact u44288
  · exact u44289

def r44438 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44438 : Nat → Fin 9 := (fun _ => 0)

theorem u44438 : Upper (D 7) (R 7) [36,192] 13 := by
  apply FastRouting.sound _ _ [36,192] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,192,257,258,264,288,320] r44438 c44438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44290
  · exact u44291
  · exact u44292
  · exact u44293
  · exact u44294
  · exact u44295
  · exact u44296
  · exact u44297
  · exact u44298
  · exact u44299
  · exact u44300
  · exact u44301
  · exact u44302
  · exact u44303
  · exact u44304
  · exact u44305
  · exact u44306

def r44439 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44439 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44439 : Upper (D 7) (R 7) [36,257] 13 := by
  apply FastRouting.sound _ _ [36,257] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,192] r44439 c44439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44307
  · exact u44308
  · exact u44309
  · exact u44310
  · exact u44311
  · exact u44312
  · exact u44313
  · exact u44314
  · exact u44315
  · exact u44316
  · exact u44317
  · exact u44318

def r44440 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44440 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44440 : Upper (D 7) (R 7) [36,264] 13 := by
  apply FastRouting.sound _ _ [36,264] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44440 c44440
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44319
  · exact u44320
  · exact u44321
  · exact u44322
  · exact u44323
  · exact u44324
  · exact u44325
  · exact u44326
  · exact u44327
  · exact u44328
  · exact u44329

def r44441 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44441 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 40 => 5 | 264 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44441 : Upper (D 7) (R 7) [36,288] 13 := by
  apply FastRouting.sound _ _ [36,288] 13 (by decide) (choices 2) [3,9,10,24,65,66,72,192] r44441 c44441
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44330
  · exact u44331
  · exact u44332
  · exact u44333
  · exact u44334
  · exact u44335
  · exact u44336
  · exact u44337

def r44442 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c44442 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44442 : Upper (D 7) (R 7) [36,320] 13 := by
  apply FastRouting.sound _ _ [36,320] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,129,130,136,160,192] r44442 c44442
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44338
  · exact u44339
  · exact u44340
  · exact u44341
  · exact u44342
  · exact u44343
  · exact u44344
  · exact u44345
  · exact u44346
  · exact u44347
  · exact u44348
  · exact u44349
  · exact u44350
  · exact u44351
  · exact u44352
  · exact u44353

def b44443 : PairBound 9 := { available := 415, camps := [{ cop := 0, region := 2, targets := 1 },{ cop := 0, region := 2, targets := 128 },{ cop := 1, region := 1, targets := 2 },{ cop := 1, region := 1, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(1,7)], upper := (rows 97 98 415 415 415 447 479 415 415), lower := (rows 97 98 4 8 16 32 64 128 256), losses := [] }

theorem u44443 : Upper (D 7) (R 7) [96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44444_10 : Upper (D 7) (R 7) [96,160,10] 13 :=
  permutation_upper _ _ _ [96,160,9] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44355

theorem m44444_129 : Upper (D 7) (R 7) [96,160,129] 13 :=
  permutation_upper _ _ _ [96,160,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44358

theorem m44444_130 : Upper (D 7) (R 7) [96,160,130] 13 :=
  permutation_upper _ _ _ [96,160,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44357

theorem m44444_136 : Upper (D 7) (R 7) [96,160,136] 13 :=
  permutation_upper _ _ _ [96,160,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44359

theorem m44444_258 : Upper (D 7) (R 7) [96,160,258] 13 :=
  permutation_upper _ _ _ [96,160,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44361

theorem m44444_384 : Upper (D 7) (R 7) [96,160,384] 13 :=
  permutation_upper _ _ _ [96,160,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44363

def r44444 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c44444 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44444 : Upper (D 7) (R 7) [96,160] 13 := by
  apply FastRouting.sound _ _ [96,160] 13 (by decide) (choices 2) [3,9,10,24,65,66,72,129,130,136,192,257,258,264,320,384] r44444 c44444
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44354
  · exact u44355
  · exact m44444_10
  · exact u44356
  · exact u44357
  · exact u44358
  · exact u44359
  · exact m44444_129
  · exact m44444_130
  · exact m44444_136
  · exact u44360
  · exact u44361
  · exact m44444_258
  · exact u44362
  · exact u44363
  · exact m44444_384

def r44445 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44445 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44445 : Upper (D 7) (R 7) [96,257] 13 := by
  apply FastRouting.sound _ _ [96,257] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,96,129,130,136,160] r44445 c44445
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44364
  · exact u44365
  · exact u44366
  · exact u44367
  · exact u44368
  · exact u44369
  · exact u44370
  · exact u44371
  · exact u44372
  · exact u44373
  · exact u44374
  · exact u44375

def r44446 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44446 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44446 : Upper (D 7) (R 7) [96,260] 13 := by
  apply FastRouting.sound _ _ [96,260] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,96,129,130,136,160] r44446 c44446
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44376
  · exact u44377
  · exact u44378
  · exact u44379
  · exact u44380
  · exact u44381
  · exact u44382
  · exact u44383
  · exact u44384
  · exact u44385
  · exact u44386
  · exact u44387

def r44447 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c44447 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 40 => 5 | 264 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44447 : Upper (D 7) (R 7) [96,288] 13 := by
  apply FastRouting.sound _ _ [96,288] 13 (by decide) (choices 2) [3,9,10,24,65,66,72,129,130,136,192] r44447 c44447
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44388
  · exact u44389
  · exact u44390
  · exact u44391
  · exact u44392
  · exact u44393
  · exact u44394
  · exact u44395
  · exact u44396
  · exact u44397
  · exact u44398

def r44448 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44448 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44448 : Upper (D 7) (R 7) [96,384] 13 := by
  apply FastRouting.sound _ _ [96,384] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,96,129,130,136,160] r44448 c44448
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44399
  · exact u44400
  · exact u44401
  · exact u44402
  · exact u44403
  · exact u44404
  · exact u44405
  · exact u44406
  · exact u44407
  · exact u44408
  · exact u44409
  · exact u44410

def r44449 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 7 | 7 => 5 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44449 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44449 : Upper (D 7) (R 7) [6] 13 := by
  apply FastRouting.sound _ _ [6] 13 (by decide) (choices 2) [9,24,33,40,96,257,264,288] r44449 c44449
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44411
  · exact u44412
  · exact u44413
  · exact u44414
  · exact u44415
  · exact u44416
  · exact u44417
  · exact u44418

theorem m44450_17 : Upper (D 7) (R 7) [12,17] 13 :=
  permutation_upper _ _ _ [6,24] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44412

def r44450 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44450 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u44450 : Upper (D 7) (R 7) [12] 13 := by
  apply FastRouting.sound _ _ [12] 13 (by decide) (choices 2) [17,33,48,96,257,272,288] r44450 c44450
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44450_17
  · exact u44419
  · exact u44420
  · exact u44421
  · exact u44422
  · exact u44423
  · exact u44424

theorem m44451_5 : Upper (D 7) (R 7) [34,5] 13 :=
  permutation_upper _ _ _ [6,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44413

theorem m44451_12 : Upper (D 7) (R 7) [34,12] 13 :=
  permutation_upper _ _ _ [12,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44419

def r44451 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 264 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 48 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 80 => (68,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 144 => (68,(fun i => match i.val with | 2 => 4 | 4 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (260,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44451 : Nat → Fin 9 := (fun _ => 0)

theorem u44451 : Upper (D 7) (R 7) [34] 13 := by
  apply FastRouting.sound _ _ [34] 13 (by decide) (choices 2) [5,12,33,36,65,68,96,192,257,260,288,320] r44451 c44451
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44451_5
  · exact m44451_12
  · exact u44425
  · exact u44426
  · exact u44427
  · exact u44428
  · exact u44429
  · exact u44430
  · exact u44431
  · exact u44432
  · exact u44433
  · exact u44434

theorem m44452_9 : Upper (D 7) (R 7) [36,9] 13 :=
  permutation_upper _ _ _ [6,40] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44414

theorem m44452_24 : Upper (D 7) (R 7) [36,24] 13 :=
  permutation_upper _ _ _ [12,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44420

theorem m44452_33 : Upper (D 7) (R 7) [36,33] 13 :=
  permutation_upper _ _ _ [34,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44426

theorem m44452_65 : Upper (D 7) (R 7) [36,65] 13 :=
  permutation_upper _ _ _ [34,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44428

def r44452 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44452 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44452 : Upper (D 7) (R 7) [36] 13 := by
  apply FastRouting.sound _ _ [36] 13 (by decide) (choices 2) [9,24,33,40,65,72,96,192,257,264,288,320] r44452 c44452
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44452_9
  · exact m44452_24
  · exact m44452_33
  · exact u44435
  · exact m44452_65
  · exact u44436
  · exact u44437
  · exact u44438
  · exact u44439
  · exact u44440
  · exact u44441
  · exact u44442

theorem m44453_5 : Upper (D 7) (R 7) [96,5] 13 :=
  permutation_upper _ _ _ [6,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44415

theorem m44453_12 : Upper (D 7) (R 7) [96,12] 13 :=
  permutation_upper _ _ _ [12,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44421

theorem m44453_33 : Upper (D 7) (R 7) [96,33] 13 :=
  permutation_upper _ _ _ [34,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44429

theorem m44453_36 : Upper (D 7) (R 7) [96,36] 13 :=
  permutation_upper _ _ _ [36,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44437

theorem m44453_129 : Upper (D 7) (R 7) [96,129] 13 :=
  permutation_upper _ _ _ [34,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44430

theorem m44453_132 : Upper (D 7) (R 7) [96,132] 13 :=
  permutation_upper _ _ _ [36,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44438

def r44453 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (132,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 264 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 48 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 80 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (132,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 272 => (260,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44453 : Nat → Fin 9 := (fun _ => 0)

theorem u44453 : Upper (D 7) (R 7) [96] 13 := by
  apply FastRouting.sound _ _ [96] 13 (by decide) (choices 2) [5,12,33,36,96,129,132,160,257,260,288,384] r44453 c44453
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44453_5
  · exact m44453_12
  · exact m44453_33
  · exact m44453_36
  · exact u44443
  · exact m44453_129
  · exact m44453_132
  · exact u44444
  · exact u44445
  · exact u44446
  · exact u44447
  · exact u44448

theorem m44454_5 : Upper (D 7) (R 7) [258,5] 13 :=
  permutation_upper _ _ _ [6,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44416

theorem m44454_12 : Upper (D 7) (R 7) [258,12] 13 :=
  permutation_upper _ _ _ [12,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44422

theorem m44454_33 : Upper (D 7) (R 7) [258,33] 13 :=
  permutation_upper _ _ _ [34,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44431

theorem m44454_36 : Upper (D 7) (R 7) [258,36] 13 :=
  permutation_upper _ _ _ [36,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44439

theorem m44454_96 : Upper (D 7) (R 7) [258,96] 13 :=
  permutation_upper _ _ _ [96,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44445

def r44454 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 7 | 7 => 5 | _ => i)) | 48 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 80 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44454 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 260 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44454 : Upper (D 7) (R 7) [258] 13 := by
  apply FastRouting.sound _ _ [258] 13 (by decide) (choices 2) [5,12,33,36,96] r44454 c44454
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m44454_5
  · exact m44454_12
  · exact m44454_33
  · exact m44454_36
  · exact m44454_96

theorem m44455_9 : Upper (D 7) (R 7) [260,9] 13 :=
  permutation_upper _ _ _ [6,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44417

theorem m44455_24 : Upper (D 7) (R 7) [260,24] 13 :=
  permutation_upper _ _ _ [12,272] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44423

theorem m44455_33 : Upper (D 7) (R 7) [260,33] 13 :=
  permutation_upper _ _ _ [34,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44432

theorem m44455_40 : Upper (D 7) (R 7) [260,40] 13 :=
  permutation_upper _ _ _ [36,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44440

theorem m44455_96 : Upper (D 7) (R 7) [260,96] 13 :=
  permutation_upper _ _ _ [96,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44446

def r44455 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44455 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44455 : Upper (D 7) (R 7) [260] 13 := by
  apply FastRouting.sound _ _ [260] 13 (by decide) (choices 2) [9,24,33,40,96] r44455 c44455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m44455_9
  · exact m44455_24
  · exact m44455_33
  · exact m44455_40
  · exact m44455_96

theorem m44456_5 : Upper (D 7) (R 7) [288,5] 13 :=
  permutation_upper _ _ _ [6,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44418

theorem m44456_12 : Upper (D 7) (R 7) [288,12] 13 :=
  permutation_upper _ _ _ [12,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44424

theorem m44456_33 : Upper (D 7) (R 7) [288,33] 13 :=
  permutation_upper _ _ _ [34,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44433

theorem m44456_36 : Upper (D 7) (R 7) [288,36] 13 :=
  permutation_upper _ _ _ [36,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44441

theorem m44456_65 : Upper (D 7) (R 7) [288,65] 13 :=
  permutation_upper _ _ _ [34,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44434

theorem m44456_68 : Upper (D 7) (R 7) [288,68] 13 :=
  permutation_upper _ _ _ [36,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44442

theorem m44456_96 : Upper (D 7) (R 7) [288,96] 13 :=
  permutation_upper _ _ _ [96,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44447

theorem m44456_192 : Upper (D 7) (R 7) [288,192] 13 :=
  permutation_upper _ _ _ [96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u44448

def r44456 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 48 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 80 => (68,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 144 => (68,(fun i => match i.val with | 2 => 4 | 4 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44456 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 260 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44456 : Upper (D 7) (R 7) [288] 13 := by
  apply FastRouting.sound _ _ [288] 13 (by decide) (choices 2) [5,12,33,36,65,68,96,192] r44456 c44456
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44456_5
  · exact m44456_12
  · exact m44456_33
  · exact m44456_36
  · exact m44456_65
  · exact m44456_68
  · exact m44456_96
  · exact m44456_192

def r44457 : Route 9 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 18 => (6,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 7 | 7 => 5 | _ => i)) | 264 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 48 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 80 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | 5 => 7 | 7 => 5 | _ => i)) | 272 => (260,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c44457 : Nat → Fin 9 := (fun _ => 0)

theorem u44457 : Upper (D 7) (R 7) [] 13 := by
  apply FastRouting.sound _ _ [] 13 (by decide) (choices 2) [6,12,34,36,96,258,260,288] r44457 c44457
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u44449
  · exact u44450
  · exact u44451
  · exact u44452
  · exact u44453
  · exact u44454
  · exact u44455
  · exact u44456

#print axioms u44457
end Delivery.IrregularNine14.P07
