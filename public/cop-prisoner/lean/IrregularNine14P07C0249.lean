import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0045
import IrregularNine14P07C0046

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14940 : Route 9 := (fun mask => (mask,id))

def c14940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14940 : Upper (D 7) (R 7) [6,264,48,192,65,128] 13 := by
  apply FastRouting.sound _ _ [6,264,48,192,65,128] 13 (by decide) (choices 1) [1,2,32] r14940 c14940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2749
  · exact u2750
  · exact u2751

def b14941 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 37, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 52 200 82 33 225 161 417), lower := (rows 7 266 52 200 82 33 64 128 256), losses := [] }

theorem u14941 : Upper (D 7) (R 7) [6,264,48,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14942 : Route 9 := (fun mask => (mask,id))

def c14942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14942 : Upper (D 7) (R 7) [6,264,48,192,66,128] 13 := by
  apply FastRouting.sound _ _ [6,264,48,192,66,128] 13 (by decide) (choices 1) [1,32] r14942 c14942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2752
  · exact u2753

def b14943 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 266 100 25 50 33 192 192 448), lower := (rows 7 266 100 25 50 33 64 128 256), losses := [] }

theorem u14943 : Upper (D 7) (R 7) [6,264,96,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14944 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 25 50 96 193 129 385), lower := (rows 7 266 100 25 50 96 64 128 256), losses := [] }

theorem u14944 : Upper (D 7) (R 7) [6,264,96,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14945 : Route 9 := (fun mask => (mask,id))

def c14945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14945 : Upper (D 7) (R 7) [6,264,96,17,34,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17,34,128] 13 (by decide) (choices 1) [1,128] r14945 c14945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2754
  · exact u2755

def r14946 : Route 9 := (fun mask => (mask,id))

def c14946 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14946 : Upper (D 7) (R 7) [6,264,96,17,130,1] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17,130,1] 13 (by decide) (choices 1) [32,128] r14946 c14946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2756
  · exact u2757

def b14947 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 25 146 96 225 161 417), lower := (rows 7 266 100 25 146 96 64 128 256), losses := [] }

theorem u14947 : Upper (D 7) (R 7) [6,264,96,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14948_1 : Upper (D 7) (R 7) [6,264,96,17,130,128,1] 13 :=
  permutation_upper _ _ _ [6,264,96,17,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2757

theorem m14948_32 : Upper (D 7) (R 7) [6,264,96,17,130,128,32] 13 :=
  permutation_upper _ _ _ [6,264,96,17,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2758

def r14948 : Route 9 := (fun mask => (mask,id))

def c14948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14948 : Upper (D 7) (R 7) [6,264,96,17,130,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17,130,128] 13 (by decide) (choices 1) [1,32] r14948 c14948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14948_1
  · exact m14948_32

def b14949 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 450, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(4,0)], upper := (rows 7 266 100 25 176 33 194 194 450), lower := (rows 7 266 100 25 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 36 8 48 32 75 139 267), good := (rows 454 458 116 474 180 500 64 128 256) }] }

theorem u14949 : Upper (D 7) (R 7) [6,264,96,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14950 : Route 9 := (fun mask => (mask,id))

def c14950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14950 : Upper (D 7) (R 7) [6,264,96,17,160,2] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17,160,2] 13 (by decide) (choices 1) [1,128] r14950 c14950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2759
  · exact u2760

def b14951 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 25 176 96 195 131 387), lower := (rows 7 266 100 25 176 96 64 128 256), losses := [] }

theorem u14951 : Upper (D 7) (R 7) [6,264,96,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14952 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 100 25 176 160 67 195 323), lower := (rows 7 266 100 25 176 160 64 128 256), losses := [] }

theorem u14952 : Upper (D 7) (R 7) [6,264,96,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14953 : Route 9 := (fun mask => (mask,id))

def c14953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14953 : Upper (D 7) (R 7) [6,264,96,18,129,1] 13 := by
  apply FastRouting.sound _ _ [6,264,96,18,129,1] 13 (by decide) (choices 1) [32,128] r14953 c14953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2761
  · exact u2762

def b14954 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 26 145 96 225 161 417), lower := (rows 7 266 100 26 145 96 64 128 256), losses := [] }

theorem u14954 : Upper (D 7) (R 7) [6,264,96,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14955_1 : Upper (D 7) (R 7) [6,264,96,18,129,128,1] 13 :=
  permutation_upper _ _ _ [6,264,96,18,129,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2762

theorem m14955_32 : Upper (D 7) (R 7) [6,264,96,18,129,128,32] 13 :=
  permutation_upper _ _ _ [6,264,96,18,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2763

def r14955 : Route 9 := (fun mask => (mask,id))

def c14955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14955 : Upper (D 7) (R 7) [6,264,96,18,129,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,18,129,128] 13 (by decide) (choices 1) [1,32] r14955 c14955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14955_1
  · exact m14955_32

def b14956 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 266 100 26 176 33 193 193 449), lower := (rows 7 266 100 26 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 24 16 0 97 161 289), good := (rows 455 266 452 26 474 449 64 128 256) }] }

theorem u14956 : Upper (D 7) (R 7) [6,264,96,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14957 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 26 176 96 193 129 385), lower := (rows 7 266 100 26 176 96 64 128 256), losses := [] }

theorem u14957 : Upper (D 7) (R 7) [6,264,96,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14958 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 100 26 176 160 65 193 321), lower := (rows 7 266 100 26 176 160 64 128 256), losses := [] }

theorem u14958 : Upper (D 7) (R 7) [6,264,96,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14959 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 266 100 41 82 33 208 144 400), lower := (rows 7 266 100 41 82 33 64 128 256), losses := [] }

theorem u14959 : Upper (D 7) (R 7) [6,264,96,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14960 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 266 100 41 82 48 193 129 385), lower := (rows 7 266 100 41 82 48 64 128 256), losses := [] }

theorem u14960 : Upper (D 7) (R 7) [6,264,96,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14960 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14961 : Route 9 := (fun mask => (mask,id))

def c14961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14961 : Upper (D 7) (R 7) [6,264,96,33,66,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,33,66,128] 13 (by decide) (choices 1) [1,16,128] r14961 c14961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2764
  · exact u2765
  · exact u2766

def b14962 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 40, targets := 192 }], pairs := [(3,6),(3,7),(4,1),(4,5)], upper := (rows 7 266 100 41 145 34 208 208 464), lower := (rows 7 266 100 41 145 34 64 128 256), losses := [] }

theorem u14962 : Upper (D 7) (R 7) [6,264,96,33,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14963 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 266 100 41 145 48 194 194 450), lower := (rows 7 266 100 41 145 48 64 128 256), losses := [] }

theorem u14963 : Upper (D 7) (R 7) [6,264,96,33,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14963 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14964 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 41 145 96 210 146 402), lower := (rows 7 266 100 41 145 96 64 128 256), losses := [] }

theorem u14964 : Upper (D 7) (R 7) [6,264,96,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14965 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 66 }], pairs := [(1,5),(3,1),(3,6),(4,5)], upper := (rows 7 266 100 41 145 160 82 210 338), lower := (rows 7 266 100 41 145 160 64 128 256), losses := [] }

theorem u14965 : Upper (D 7) (R 7) [6,264,96,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14966 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 266 100 41 146 33 208 208 464), lower := (rows 7 266 100 41 146 33 64 128 256), losses := [] }

theorem u14966 : Upper (D 7) (R 7) [6,264,96,33,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14967 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 7 266 100 41 146 48 193 193 449), lower := (rows 7 266 100 41 146 48 64 128 256), losses := [] }

theorem u14967 : Upper (D 7) (R 7) [6,264,96,33,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14967 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14968 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 41 146 96 209 145 401), lower := (rows 7 266 100 41 146 96 64 128 256), losses := [] }

theorem u14968 : Upper (D 7) (R 7) [6,264,96,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14969 : Route 9 := (fun mask => (mask,id))

def c14969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14969 : Upper (D 7) (R 7) [6,264,96,33,130,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,33,130,128] 13 (by decide) (choices 1) [1,16] r14969 c14969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2767
  · exact u2768

def b14970 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 266 100 41 208 33 210 146 402), lower := (rows 7 266 100 41 208 33 64 128 256), losses := [] }

theorem u14970 : Upper (D 7) (R 7) [6,264,96,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14971 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 40, targets := 192 }], pairs := [(3,6),(3,7),(4,1),(4,5)], upper := (rows 7 266 100 41 208 34 209 145 401), lower := (rows 7 266 100 41 208 34 64 128 256), losses := [] }

theorem u14971 : Upper (D 7) (R 7) [6,264,96,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14972 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 266 100 41 208 48 195 131 387), lower := (rows 7 266 100 41 208 48 64 128 256), losses := [] }

theorem u14972 : Upper (D 7) (R 7) [6,264,96,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14972 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14973 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(1,5),(2,0),(2,1),(4,5)], upper := (rows 7 266 100 41 208 160 83 147 275), lower := (rows 7 266 100 41 208 160 64 128 256), losses := [] }

theorem u14973 : Upper (D 7) (R 7) [6,264,96,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14974 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 40, targets := 192 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 266 100 42 145 33 208 208 464), lower := (rows 7 266 100 42 145 33 64 128 256), losses := [] }

theorem u14974 : Upper (D 7) (R 7) [6,264,96,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14975 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 266 100 42 145 48 193 193 449), lower := (rows 7 266 100 42 145 48 64 128 256), losses := [] }

theorem u14975 : Upper (D 7) (R 7) [6,264,96,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14975 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14976 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 42 145 96 209 145 401), lower := (rows 7 266 100 42 145 96 64 128 256), losses := [] }

theorem u14976 : Upper (D 7) (R 7) [6,264,96,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14977 : Route 9 := (fun mask => (mask,id))

def c14977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14977 : Upper (D 7) (R 7) [6,264,96,34,129,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,34,129,128] 13 (by decide) (choices 1) [1,16] r14977 c14977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2769
  · exact u2770

def b14978 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 40, targets := 192 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 266 100 42 208 33 209 145 401), lower := (rows 7 266 100 42 208 33 64 128 256), losses := [] }

theorem u14978 : Upper (D 7) (R 7) [6,264,96,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14979 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 266 100 42 208 48 193 129 385), lower := (rows 7 266 100 42 208 48 64 128 256), losses := [] }

theorem u14979 : Upper (D 7) (R 7) [6,264,96,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14979 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14980 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1),(4,5)], upper := (rows 7 266 100 42 208 160 81 145 273), lower := (rows 7 266 100 42 208 160 64 128 256), losses := [] }

theorem u14980 : Upper (D 7) (R 7) [6,264,96,34,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14981 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 44, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 7 266 100 56 81 33 194 130 386), lower := (rows 7 266 100 56 81 33 64 128 256), losses := [] }

theorem u14981 : Upper (D 7) (R 7) [6,264,96,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14982 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6),(4,1),(4,5)], upper := (rows 7 266 100 56 81 34 193 129 385), lower := (rows 7 266 100 56 81 34 64 128 256), losses := [] }

theorem u14982 : Upper (D 7) (R 7) [6,264,96,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14983 : Route 9 := (fun mask => (mask,id))

def c14983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14983 : Upper (D 7) (R 7) [6,264,96,48,65,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,65,128] 13 (by decide) (choices 1) [1,2,128] r14983 c14983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2771
  · exact u2772
  · exact u2773

def b14984 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(3,7)], upper := (rows 7 266 100 56 82 33 193 129 385), lower := (rows 7 266 100 56 82 33 64 128 256), losses := [] }

theorem u14984 : Upper (D 7) (R 7) [6,264,96,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14985 : Route 9 := (fun mask => (mask,id))

def c14985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14985 : Upper (D 7) (R 7) [6,264,96,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,66,128] 13 (by decide) (choices 1) [1,128] r14985 c14985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2774
  · exact u2775

def b14986 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 194 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 266 100 56 145 33 194 194 450), lower := (rows 7 266 100 56 145 33 64 128 256), losses := [] }

theorem u14986 : Upper (D 7) (R 7) [6,264,96,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14987 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 }], pairs := [(2,1),(3,0),(4,1),(4,5)], upper := (rows 7 266 100 56 145 34 193 193 449), lower := (rows 7 266 100 56 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 38 298 100 56 184 34 64 128 256) },{ target := 1, region := (rows 1 0 12 8 17 32 81 145 273), good := (rows 469 268 100 508 465 32 64 128 256) }] }

theorem u14987 : Upper (D 7) (R 7) [6,264,96,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14988 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 56 145 96 195 131 387), lower := (rows 7 266 100 56 145 96 64 128 256), losses := [] }

theorem u14988 : Upper (D 7) (R 7) [6,264,96,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14989 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 266 100 56 145 160 67 195 323), lower := (rows 7 266 100 56 145 160 64 128 256), losses := [] }

theorem u14989 : Upper (D 7) (R 7) [6,264,96,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14990 : Route 9 := (fun mask => (mask,id))

def c14990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14990 : Upper (D 7) (R 7) [6,264,96,48,130,1] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,130,1] 13 (by decide) (choices 1) [1,128] r14990 c14990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2776
  · exact u2777

def b14991 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 56 146 96 193 129 385), lower := (rows 7 266 100 56 146 96 64 128 256), losses := [] }

theorem u14991 : Upper (D 7) (R 7) [6,264,96,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14992 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 266 100 56 146 160 65 193 321), lower := (rows 7 266 100 56 146 160 64 128 256), losses := [] }

theorem u14992 : Upper (D 7) (R 7) [6,264,96,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14993 : Route 9 := (fun mask => (mask,id))

def c14993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14993 : Upper (D 7) (R 7) [6,264,96,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,192,1] 13 (by decide) (choices 1) [1,2,128] r14993 c14993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2778
  · exact u2779
  · exact u2780

def r14994 : Route 9 := (fun mask => (mask,id))

def c14994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14994 : Upper (D 7) (R 7) [6,264,96,48,192,2] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48,192,2] 13 (by decide) (choices 1) [1,128] r14994 c14994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2781
  · exact u2782

def b14995 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 266 100 56 208 160 67 131 259), lower := (rows 7 266 100 56 208 160 64 128 256), losses := [] }

theorem u14995 : Upper (D 7) (R 7) [6,264,96,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14996 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 48, targets := 192 },{ cop := 4, region := 204, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 266 100 137 49 34 208 208 464), lower := (rows 7 266 100 137 49 34 64 128 256), losses := [] }

theorem u14996 : Upper (D 7) (R 7) [6,264,96,129,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14997 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 266 100 137 49 48 194 194 450), lower := (rows 7 266 100 137 49 48 64 128 256), losses := [] }

theorem u14997 : Upper (D 7) (R 7) [6,264,96,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14997 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14998 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 137 49 96 210 146 402), lower := (rows 7 266 100 137 49 96 64 128 256), losses := [] }

theorem u14998 : Upper (D 7) (R 7) [6,264,96,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14999 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,6)], upper := (rows 7 266 100 137 49 160 82 210 338), lower := (rows 7 266 100 137 49 160 64 128 256), losses := [] }

theorem u14999 : Upper (D 7) (R 7) [6,264,96,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14999
end Delivery.IrregularNine14.P07
