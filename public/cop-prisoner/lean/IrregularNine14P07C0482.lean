import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0182
import IrregularNine14P07C0183

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28920 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 168 145 96 83 147 275), lower := (rows 97 262 14 168 145 96 64 128 256), losses := [] }

theorem u28920 : Upper (D 7) (R 7) [96,260,10,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28921 : Route 9 := (fun mask => (mask,id))

def c28921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28921 : Upper (D 7) (R 7) [96,260,10,160,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,130,1] 13 (by decide) (choices 1) [1,16] r28921 c28921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10949
  · exact u10950

def b28922 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 262 14 168 146 48 65 193 321), lower := (rows 97 262 14 168 146 48 64 128 256), losses := [] }

theorem u28922 : Upper (D 7) (R 7) [96,260,10,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28922 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28923 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 168 146 96 81 145 273), lower := (rows 97 262 14 168 146 96 64 128 256), losses := [] }

theorem u28923 : Upper (D 7) (R 7) [96,260,10,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28924 : Route 9 := (fun mask => (mask,id))

def c28924 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28924 : Upper (D 7) (R 7) [96,260,10,160,192,1] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,192,1] 13 (by decide) (choices 1) [1,2,16] r28924 c28924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10951
  · exact u10952
  · exact u10953

def b28925 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,1),(3,1),(4,1),(4,5)], upper := (rows 97 262 14 168 208 34 81 145 273), lower := (rows 97 262 14 168 208 34 64 128 256), losses := [] }

theorem u28925 : Upper (D 7) (R 7) [96,260,10,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28926 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 14 168 208 48 67 131 259), lower := (rows 97 262 14 168 208 48 64 128 256), losses := [] }

theorem u28926 : Upper (D 7) (R 7) [96,260,10,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28926 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28927 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 52, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 97 262 28 11 50 33 192 192 448), lower := (rows 97 262 28 11 50 33 64 128 256), losses := [] }

theorem u28927 : Upper (D 7) (R 7) [96,260,24,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28928 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 11 50 96 193 129 385), lower := (rows 97 262 28 11 50 96 64 128 256), losses := [] }

theorem u28928 : Upper (D 7) (R 7) [96,260,24,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28929 : Route 9 := (fun mask => (mask,id))

def c28929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28929 : Upper (D 7) (R 7) [96,260,24,3,34,128] 13 := by
  apply FastRouting.sound _ _ [96,260,24,3,34,128] 13 (by decide) (choices 1) [1,128] r28929 c28929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10954
  · exact u10955

def b28930 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 209, targets := 2 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 97 262 28 11 145 34 224 224 480), lower := (rows 97 262 28 11 145 34 64 128 256), losses := [{ target := 1, region := (rows 33 0 12 8 57 32 97 161 289), good := (rows 497 260 28 477 465 497 64 128 256) }] }

theorem u28930 : Upper (D 7) (R 7) [96,260,24,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28931 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 11 145 96 226 162 418), lower := (rows 97 262 28 11 145 96 64 128 256), losses := [] }

theorem u28931 : Upper (D 7) (R 7) [96,260,24,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28932_2 : Upper (D 7) (R 7) [96,260,24,3,129,128,2] 13 :=
  permutation_upper _ _ _ [96,260,24,3,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10956

theorem m28932_32 : Upper (D 7) (R 7) [96,260,24,3,129,128,32] 13 :=
  permutation_upper _ _ _ [96,260,24,3,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10957

def r28932 : Route 9 := (fun mask => (mask,id))

def c28932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28932 : Upper (D 7) (R 7) [96,260,24,3,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,24,3,129,128] 13 (by decide) (choices 1) [2,32] r28932 c28932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28932_2
  · exact m28932_32

def b28933 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 225, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(2,0)], upper := (rows 97 262 28 11 146 33 224 224 480), lower := (rows 97 262 28 11 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 32 97 161 289), good := (rows 480 262 30 478 146 480 64 128 256) }] }

theorem u28933 : Upper (D 7) (R 7) [96,260,24,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28934 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 11 146 96 225 161 417), lower := (rows 97 262 28 11 146 96 64 128 256), losses := [] }

theorem u28934 : Upper (D 7) (R 7) [96,260,24,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28935_1 : Upper (D 7) (R 7) [96,260,24,3,130,128,1] 13 :=
  permutation_upper _ _ _ [96,260,24,3,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10958

theorem m28935_32 : Upper (D 7) (R 7) [96,260,24,3,130,128,32] 13 :=
  permutation_upper _ _ _ [96,260,24,3,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10959

def r28935 : Route 9 := (fun mask => (mask,id))

def c28935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28935 : Upper (D 7) (R 7) [96,260,24,3,130,128] 13 := by
  apply FastRouting.sound _ _ [96,260,24,3,130,128] 13 (by decide) (choices 1) [1,32] r28935 c28935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28935_1
  · exact m28935_32

def b28936 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,5)], upper := (rows 97 262 28 11 176 33 194 194 450), lower := (rows 97 262 28 11 176 33 64 128 256), losses := [] }

theorem u28936 : Upper (D 7) (R 7) [96,260,24,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28937 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 97 262 28 11 176 34 193 193 449), lower := (rows 97 262 28 11 176 34 64 128 256), losses := [{ target := 1, region := (rows 49 0 12 8 49 32 125 189 317), good := (rows 497 452 477 477 497 497 64 128 256) },{ target := 5, region := (rows 1 6 4 8 16 0 73 137 265), good := (rows 449 262 478 459 144 2 64 128 256) }] }

theorem u28937 : Upper (D 7) (R 7) [96,260,24,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28938 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 11 176 96 195 131 387), lower := (rows 97 262 28 11 176 96 64 128 256), losses := [] }

theorem u28938 : Upper (D 7) (R 7) [96,260,24,3,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28939 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 262 28 11 176 160 67 195 323), lower := (rows 97 262 28 11 176 160 64 128 256), losses := [] }

theorem u28939 : Upper (D 7) (R 7) [96,260,24,3,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28940 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 1, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 262 28 42 82 33 193 129 385), lower := (rows 97 262 28 42 82 33 64 128 256), losses := [] }

theorem u28940 : Upper (D 7) (R 7) [96,260,24,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28941_1 : Upper (D 7) (R 7) [96,260,24,34,66,128,1] 13 :=
  permutation_upper _ _ _ [96,260,24,34,66,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10960

def r28941 : Route 9 := (fun mask => (mask,id))

def c28941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28941 : Upper (D 7) (R 7) [96,260,24,34,66,128] 13 := by
  apply FastRouting.sound _ _ [96,260,24,34,66,128] 13 (by decide) (choices 1) [1,128] r28941 c28941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28941_1
  · exact u10961

def b28942 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,5)], upper := (rows 97 262 28 42 145 33 194 194 450), lower := (rows 97 262 28 42 145 33 64 128 256), losses := [] }

theorem u28942 : Upper (D 7) (R 7) [96,260,24,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28943 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 193, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 28 42 145 34 193 193 449), lower := (rows 97 262 28 42 145 34 64 128 256), losses := [] }

theorem u28943 : Upper (D 7) (R 7) [96,260,24,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28944 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 42 145 96 195 131 387), lower := (rows 97 262 28 42 145 96 64 128 256), losses := [] }

theorem u28944 : Upper (D 7) (R 7) [96,260,24,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28945 : Route 9 := (fun mask => (mask,id))

def c28945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28945 : Upper (D 7) (R 7) [96,260,24,34,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,24,34,129,128] 13 (by decide) (choices 1) [1,2] r28945 c28945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10962
  · exact u10963

def b28946 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 225, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,5),(2,5)], upper := (rows 97 262 28 42 146 33 193 193 449), lower := (rows 97 262 28 42 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 97 161 289), good := (rows 449 262 30 478 146 449 64 128 256) }] }

theorem u28946 : Upper (D 7) (R 7) [96,260,24,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28947 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 42 146 96 193 129 385), lower := (rows 97 262 28 42 146 96 64 128 256), losses := [] }

theorem u28947 : Upper (D 7) (R 7) [96,260,24,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28948 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 262 28 42 146 160 65 193 321), lower := (rows 97 262 28 42 146 160 64 128 256), losses := [] }

theorem u28948 : Upper (D 7) (R 7) [96,260,24,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28949 : Route 9 := (fun mask => (mask,id))

def c28949 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28949 : Upper (D 7) (R 7) [96,260,24,34,192,1] 13 := by
  apply FastRouting.sound _ _ [96,260,24,34,192,1] 13 (by decide) (choices 1) [1,2,128] r28949 c28949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10964
  · exact u10965
  · exact u10966

def b28950 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 193, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 28 42 208 34 193 129 385), lower := (rows 97 262 28 42 208 34 64 128 256), losses := [] }

theorem u28950 : Upper (D 7) (R 7) [96,260,24,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28951 : Route 9 := (fun mask => (mask,id))

def c28951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28951 : Upper (D 7) (R 7) [96,260,24,34,192,128] 13 := by
  apply FastRouting.sound _ _ [96,260,24,34,192,128] 13 (by decide) (choices 1) [1,2] r28951 c28951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10967
  · exact u10968

def r28952 : Route 9 := (fun mask => (mask,id))

def c28952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28952 : Upper (D 7) (R 7) [96,260,24,129,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,24,129,130,1] 13 (by decide) (choices 1) [2,32] r28952 c28952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10969
  · exact u10970

def b28953 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 5, region := 201, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,1)], upper := (rows 97 262 28 137 146 34 97 225 353), lower := (rows 97 262 28 137 146 34 64 128 256), losses := [] }

theorem u28953 : Upper (D 7) (R 7) [96,260,24,129,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28954 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 137 146 96 99 163 291), lower := (rows 97 262 28 137 146 96 64 128 256), losses := [] }

theorem u28954 : Upper (D 7) (R 7) [96,260,24,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28955 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 97 262 28 137 176 33 66 194 322), lower := (rows 97 262 28 137 176 33 64 128 256), losses := [] }

theorem u28955 : Upper (D 7) (R 7) [96,260,24,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28956 : Route 9 := (fun mask => (mask,id))

def c28956 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28956 : Upper (D 7) (R 7) [96,260,24,129,160,2] 13 := by
  apply FastRouting.sound _ _ [96,260,24,129,160,2] 13 (by decide) (choices 1) [1,2] r28956 c28956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10971
  · exact u10972

def b28957 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 137 176 96 67 131 259), lower := (rows 97 262 28 137 176 96 64 128 256), losses := [] }

theorem u28957 : Upper (D 7) (R 7) [96,260,24,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28958 : Route 9 := (fun mask => (mask,id))

def c28958 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28958 : Upper (D 7) (R 7) [96,260,24,130,160,1] 13 := by
  apply FastRouting.sound _ _ [96,260,24,130,160,1] 13 (by decide) (choices 1) [1,2] r28958 c28958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10973
  · exact u10974

def b28959 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 97 262 28 138 176 34 65 193 321), lower := (rows 97 262 28 138 176 34 64 128 256), losses := [] }

theorem u28959 : Upper (D 7) (R 7) [96,260,24,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28960 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 28 138 176 96 67 131 259), lower := (rows 97 262 28 138 176 96 64 128 256), losses := [] }

theorem u28960 : Upper (D 7) (R 7) [96,260,24,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28961 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 262 28 168 208 33 67 131 259), lower := (rows 97 262 28 168 208 33 64 128 256), losses := [] }

theorem u28961 : Upper (D 7) (R 7) [96,260,24,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28962_1 : Upper (D 7) (R 7) [96,260,24,160,192,2,1] 13 :=
  permutation_upper _ _ _ [96,260,24,160,192,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10975

def r28962 : Route 9 := (fun mask => (mask,id))

def c28962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28962 : Upper (D 7) (R 7) [96,260,24,160,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,24,160,192,2] 13 (by decide) (choices 1) [1,2] r28962 c28962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28962_1
  · exact u10976

def b28963 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(4,0),(4,1),(4,5)], upper := (rows 97 262 38 11 88 33 208 144 400), lower := (rows 97 262 38 11 88 33 64 128 256), losses := [] }

theorem u28963 : Upper (D 7) (R 7) [96,260,34,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28964 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 38 11 88 48 193 129 385), lower := (rows 97 262 38 11 88 48 64 128 256), losses := [] }

theorem u28964 : Upper (D 7) (R 7) [96,260,34,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28964 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28965 : Route 9 := (fun mask => (mask,id))

def c28965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28965 : Upper (D 7) (R 7) [96,260,34,3,72,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,3,72,128] 13 (by decide) (choices 1) [1,16,128] r28965 c28965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10977
  · exact u10978
  · exact u10979

def b28966 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 262 38 11 145 40 208 208 464), lower := (rows 97 262 38 11 145 40 64 128 256), losses := [] }

theorem u28966 : Upper (D 7) (R 7) [96,260,34,3,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28966 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28967 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 3, region := 208, targets := 32 }], pairs := [(0,1),(4,1),(4,5)], upper := (rows 97 262 38 11 145 48 200 200 456), lower := (rows 97 262 38 11 145 48 64 128 256), losses := [] }

theorem u28967 : Upper (D 7) (R 7) [96,260,34,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28967 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28968 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 38 11 145 96 216 152 408), lower := (rows 97 262 38 11 145 96 64 128 256), losses := [] }

theorem u28968 : Upper (D 7) (R 7) [96,260,34,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28969 : Route 9 := (fun mask => (mask,id))

def c28969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28969 : Upper (D 7) (R 7) [96,260,34,3,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,3,129,128] 13 (by decide) (choices 1) [8,16] r28969 c28969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10980
  · exact u10981

def b28970 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(4,0),(4,1),(4,5)], upper := (rows 97 262 38 11 152 33 208 208 464), lower := (rows 97 262 38 11 152 33 64 128 256), losses := [] }

theorem u28970 : Upper (D 7) (R 7) [96,260,34,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28971 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 3, region := 208, targets := 32 }], pairs := [(0,1),(4,1),(4,5)], upper := (rows 97 262 38 11 152 48 193 193 449), lower := (rows 97 262 38 11 152 48 64 128 256), losses := [] }

theorem u28971 : Upper (D 7) (R 7) [96,260,34,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28971 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28972 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 38 11 152 96 209 145 401), lower := (rows 97 262 38 11 152 96 64 128 256), losses := [] }

theorem u28972 : Upper (D 7) (R 7) [96,260,34,3,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28973 : Route 9 := (fun mask => (mask,id))

def c28973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28973 : Upper (D 7) (R 7) [96,260,34,3,136,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,3,136,128] 13 (by decide) (choices 1) [1,16] r28973 c28973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10982
  · exact u10983

def b28974 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 208, targets := 33 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(4,0),(4,1),(4,5)], upper := (rows 97 262 38 11 208 33 216 152 408), lower := (rows 97 262 38 11 208 33 64 128 256), losses := [] }

theorem u28974 : Upper (D 7) (R 7) [96,260,34,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28975 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 262 38 11 208 40 209 145 401), lower := (rows 97 262 38 11 208 40 64 128 256), losses := [] }

theorem u28975 : Upper (D 7) (R 7) [96,260,34,3,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28975 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28976 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 38 11 208 48 201 137 393), lower := (rows 97 262 38 11 208 48 64 128 256), losses := [] }

theorem u28976 : Upper (D 7) (R 7) [96,260,34,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28976 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28977 : Route 9 := (fun mask => (mask,id))

def c28977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28977 : Upper (D 7) (R 7) [96,260,34,3,192,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,3,192,128] 13 (by decide) (choices 1) [1,8,16] r28977 c28977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10984
  · exact u10985
  · exact u10986

def b28978 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(2,0),(3,1)], upper := (rows 97 262 38 25 26 33 192 192 448), lower := (rows 97 262 38 25 26 33 64 128 256), losses := [] }

theorem u28978 : Upper (D 7) (R 7) [96,260,34,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28979 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 38 25 26 96 193 129 385), lower := (rows 97 262 38 25 26 96 64 128 256), losses := [] }

theorem u28979 : Upper (D 7) (R 7) [96,260,34,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28979
end Delivery.IrregularNine14.P07
