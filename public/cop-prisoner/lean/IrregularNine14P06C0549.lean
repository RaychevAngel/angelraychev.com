import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0261
import IrregularNine14P06C0262
import IrregularNine14P06C0263

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32940 : Route 9 := (fun mask => (mask,id))

def c32940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32940 : Upper (D 6) (R 6) [10,129,258,36,96] 13 := by
  apply FastRouting.sound _ _ [10,129,258,36,96] 13 (by decide) (choices 1) [1,4,16,64] r32940 c32940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15707
  · exact u15708
  · exact u15709
  · exact u15710

def b32941 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 262 56 21 100 100 228 356), lower := (rows 11 131 262 56 21 32 64 128 256), losses := [] }

theorem u32941 : Upper (D 6) (R 6) [10,129,258,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32942 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 262 56 49 100 68 196 324), lower := (rows 11 131 262 56 49 32 64 128 256), losses := [] }

theorem u32942 : Upper (D 6) (R 6) [10,129,258,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32943 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 262 56 52 101 69 197 325), lower := (rows 11 131 262 56 52 32 64 128 256), losses := [] }

theorem u32943 : Upper (D 6) (R 6) [10,129,258,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32944 : Route 9 := (fun mask => (mask,id))

def c32944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32944 : Upper (D 6) (R 6) [10,129,258,48,65] 13 := by
  apply FastRouting.sound _ _ [10,129,258,48,65] 13 (by decide) (choices 1) [4,64] r32944 c32944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15711
  · exact u15712

def r32945 : Route 9 := (fun mask => (mask,id))

def c32945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32945 : Upper (D 6) (R 6) [10,129,258,48,68] 13 := by
  apply FastRouting.sound _ _ [10,129,258,48,68] 13 (by decide) (choices 1) [1,4,64] r32945 c32945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15713
  · exact u15714
  · exact u15715

def b32946 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 262 56 112 101 69 197 325), lower := (rows 11 131 262 56 112 32 64 128 256), losses := [] }

theorem u32946 : Upper (D 6) (R 6) [10,129,258,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32947 : Route 9 := (fun mask => (mask,id))

def c32947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32947 : Upper (D 6) (R 6) [10,129,258,96,5] 13 := by
  apply FastRouting.sound _ _ [10,129,258,96,5] 13 (by decide) (choices 1) [4,16,64] r32947 c32947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15716
  · exact u15717
  · exact u15718

def r32948 : Route 9 := (fun mask => (mask,id))

def c32948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32948 : Upper (D 6) (R 6) [10,129,258,96,33] 13 := by
  apply FastRouting.sound _ _ [10,129,258,96,33] 13 (by decide) (choices 1) [4,16,64] r32948 c32948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15719
  · exact u15720
  · exact u15721

def r32949 : Route 9 := (fun mask => (mask,id))

def c32949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32949 : Upper (D 6) (R 6) [10,129,258,96,36] 13 := by
  apply FastRouting.sound _ _ [10,129,258,96,36] 13 (by decide) (choices 1) [1,4,16,64] r32949 c32949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15722
  · exact u15723
  · exact u15724
  · exact u15725

def b32950 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 131 262 104 112 53 85 149 277), lower := (rows 11 131 262 104 112 32 64 128 256), losses := [] }

theorem u32950 : Upper (D 6) (R 6) [10,129,258,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32951 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 276 13 22 96 96 224 352), lower := (rows 11 131 276 13 22 32 64 128 256), losses := [] }

theorem u32951 : Upper (D 6) (R 6) [10,129,272,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32952 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 13 50 100 100 228 356), lower := (rows 11 131 276 13 50 32 64 128 256), losses := [] }

theorem u32952 : Upper (D 6) (R 6) [10,129,272,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32953 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 131 276 13 52 98 98 226 354), lower := (rows 11 131 276 13 52 32 64 128 256), losses := [] }

theorem u32953 : Upper (D 6) (R 6) [10,129,272,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32954 : Route 9 := (fun mask => (mask,id))

def c32954 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32954 : Upper (D 6) (R 6) [10,129,272,5,96] 13 := by
  apply FastRouting.sound _ _ [10,129,272,5,96] 13 (by decide) (choices 1) [2,4,64] r32954 c32954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15726
  · exact u15727
  · exact u15728

def b32955 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 41 22 100 100 228 356), lower := (rows 11 131 276 41 22 32 64 128 256), losses := [] }

theorem u32955 : Upper (D 6) (R 6) [10,129,272,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32956 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 131 276 41 50 100 68 196 324), lower := (rows 11 131 276 41 50 32 64 128 256), losses := [] }

theorem u32956 : Upper (D 6) (R 6) [10,129,272,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32957 : Route 9 := (fun mask => (mask,id))

def c32957 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32957 : Upper (D 6) (R 6) [10,129,272,33,36] 13 := by
  apply FastRouting.sound _ _ [10,129,272,33,36] 13 (by decide) (choices 1) [2,4,64] r32957 c32957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15729
  · exact u15730
  · exact u15731

def b32958 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 41 82 100 100 228 356), lower := (rows 11 131 276 41 82 32 64 128 256), losses := [] }

theorem u32958 : Upper (D 6) (R 6) [10,129,272,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32959 : Route 9 := (fun mask => (mask,id))

def c32959 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32959 : Upper (D 6) (R 6) [10,129,272,33,68] 13 := by
  apply FastRouting.sound _ _ [10,129,272,33,68] 13 (by decide) (choices 1) [2,4,64] r32959 c32959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15732
  · exact u15733
  · exact u15734

def r32960 : Route 9 := (fun mask => (mask,id))

def c32960 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32960 : Upper (D 6) (R 6) [10,129,272,33,96] 13 := by
  apply FastRouting.sound _ _ [10,129,272,33,96] 13 (by decide) (choices 1) [2,4,64] r32960 c32960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15735
  · exact u15736
  · exact u15737

def b32961 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 276 44 19 100 100 228 356), lower := (rows 11 131 276 44 19 32 64 128 256), losses := [] }

theorem u32961 : Upper (D 6) (R 6) [10,129,272,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32962 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 276 44 21 98 98 226 354), lower := (rows 11 131 276 44 21 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 490 482 284 44 508 32 64 128 256) }] }

theorem u32962 : Upper (D 6) (R 6) [10,129,272,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32963 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 131 276 44 22 97 97 225 353), lower := (rows 11 131 276 44 22 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 489 481 284 44 508 32 64 128 256) }] }

theorem u32963 : Upper (D 6) (R 6) [10,129,272,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32964 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 4, region := 454, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 276 44 49 102 70 198 326), lower := (rows 11 131 276 44 49 32 64 128 256), losses := [] }

theorem u32964 : Upper (D 6) (R 6) [10,129,272,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32965 : Route 9 := (fun mask => (mask,id))

def c32965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32965 : Upper (D 6) (R 6) [10,129,272,36,34] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,34] 13 (by decide) (choices 1) [1,4,64] r32965 c32965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15738
  · exact u15739
  · exact u15740

def b32966 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 276 44 52 99 67 195 323), lower := (rows 11 131 276 44 52 32 64 128 256), losses := [] }

theorem u32966 : Upper (D 6) (R 6) [10,129,272,36,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32967 : Route 9 := (fun mask => (mask,id))

def c32967 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32967 : Upper (D 6) (R 6) [10,129,272,36,65] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,65] 13 (by decide) (choices 1) [2,4,64] r32967 c32967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15741
  · exact u15742
  · exact u15743

def r32968 : Route 9 := (fun mask => (mask,id))

def c32968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32968 : Upper (D 6) (R 6) [10,129,272,36,66] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,66] 13 (by decide) (choices 1) [1,4,64] r32968 c32968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15744
  · exact u15745
  · exact u15746

def r32969 : Route 9 := (fun mask => (mask,id))

def c32969 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32969 : Upper (D 6) (R 6) [10,129,272,36,68] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,68] 13 (by decide) (choices 1) [1,2,64] r32969 c32969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15747
  · exact u15748
  · exact u15749

def r32970 : Route 9 := (fun mask => (mask,id))

def c32970 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32970 : Upper (D 6) (R 6) [10,129,272,36,96] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36,96] 13 (by decide) (choices 1) [1,2,4,64] r32970 c32970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15750
  · exact u15751
  · exact u15752
  · exact u15753

def b32971 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 276 104 19 100 100 228 356), lower := (rows 11 131 276 104 19 32 64 128 256), losses := [] }

theorem u32971 : Upper (D 6) (R 6) [10,129,272,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32972 : Route 9 := (fun mask => (mask,id))

def c32972 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32972 : Upper (D 6) (R 6) [10,129,272,96,5] 13 := by
  apply FastRouting.sound _ _ [10,129,272,96,5] 13 (by decide) (choices 1) [2,4,64] r32972 c32972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15754
  · exact u15755
  · exact u15756

def r32973 : Route 9 := (fun mask => (mask,id))

def c32973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32973 : Upper (D 6) (R 6) [10,129,272,96,6] 13 := by
  apply FastRouting.sound _ _ [10,129,272,96,6] 13 (by decide) (choices 1) [1,4,64] r32973 c32973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15757
  · exact u15758
  · exact u15759

def r32974 : Route 9 := (fun mask => (mask,id))

def c32974 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32974 : Upper (D 6) (R 6) [10,129,272,96,33] 13 := by
  apply FastRouting.sound _ _ [10,129,272,96,33] 13 (by decide) (choices 1) [2,4,64] r32974 c32974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15760
  · exact u15761
  · exact u15762

def r32975 : Route 9 := (fun mask => (mask,id))

def c32975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32975 : Upper (D 6) (R 6) [10,129,272,96,34] 13 := by
  apply FastRouting.sound _ _ [10,129,272,96,34] 13 (by decide) (choices 1) [1,4,64] r32975 c32975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15763
  · exact u15764
  · exact u15765

def r32976 : Route 9 := (fun mask => (mask,id))

def c32976 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32976 : Upper (D 6) (R 6) [10,129,272,96,36] 13 := by
  apply FastRouting.sound _ _ [10,129,272,96,36] 13 (by decide) (choices 1) [1,2,4,64] r32976 c32976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15766
  · exact u15767
  · exact u15768
  · exact u15769

def b32977 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 131 276 104 112 39 71 135 263), lower := (rows 11 131 276 104 112 32 64 128 256), losses := [] }

theorem u32977 : Upper (D 6) (R 6) [10,129,272,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32978 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 292 13 22 112 112 240 368), lower := (rows 11 131 292 13 22 32 64 128 256), losses := [] }

theorem u32978 : Upper (D 6) (R 6) [10,129,288,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32979 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 13 50 116 84 212 340), lower := (rows 11 131 292 13 50 32 64 128 256), losses := [] }

theorem u32979 : Upper (D 6) (R 6) [10,129,288,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32980 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 292 13 52 114 82 210 338), lower := (rows 11 131 292 13 52 32 64 128 256), losses := [] }

theorem u32980 : Upper (D 6) (R 6) [10,129,288,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32981 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 292, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 13 82 116 116 244 372), lower := (rows 11 131 292 13 82 32 64 128 256), losses := [] }

theorem u32981 : Upper (D 6) (R 6) [10,129,288,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32982 : Route 9 := (fun mask => (mask,id))

def c32982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32982 : Upper (D 6) (R 6) [10,129,288,5,68] 13 := by
  apply FastRouting.sound _ _ [10,129,288,5,68] 13 (by decide) (choices 1) [2,16,64] r32982 c32982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15770
  · exact u15771
  · exact u15772

def r32983 : Route 9 := (fun mask => (mask,id))

def c32983 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32983 : Upper (D 6) (R 6) [10,129,288,5,96] 13 := by
  apply FastRouting.sound _ _ [10,129,288,5,96] 13 (by decide) (choices 1) [2,4,16,64] r32983 c32983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15773
  · exact u15774
  · exact u15775
  · exact u15776

def b32984 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 292 25 22 100 100 228 356), lower := (rows 11 131 292 25 22 32 64 128 256), losses := [] }

theorem u32984 : Upper (D 6) (R 6) [10,129,288,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32985 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 292 25 50 100 68 196 324), lower := (rows 11 131 292 25 50 32 64 128 256), losses := [] }

theorem u32985 : Upper (D 6) (R 6) [10,129,288,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32986 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 292 25 52 102 70 198 326), lower := (rows 11 131 292 25 52 32 64 128 256), losses := [] }

theorem u32986 : Upper (D 6) (R 6) [10,129,288,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32987 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 292 25 82 100 100 228 356), lower := (rows 11 131 292 25 82 32 64 128 256), losses := [] }

theorem u32987 : Upper (D 6) (R 6) [10,129,288,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32988 : Route 9 := (fun mask => (mask,id))

def c32988 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32988 : Upper (D 6) (R 6) [10,129,288,17,68] 13 := by
  apply FastRouting.sound _ _ [10,129,288,17,68] 13 (by decide) (choices 1) [2,4,64] r32988 c32988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15777
  · exact u15778
  · exact u15779

def r32989 : Route 9 := (fun mask => (mask,id))

def c32989 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32989 : Upper (D 6) (R 6) [10,129,288,17,96] 13 := by
  apply FastRouting.sound _ _ [10,129,288,17,96] 13 (by decide) (choices 1) [2,4,64] r32989 c32989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15780
  · exact u15781
  · exact u15782

def b32990 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 28 19 100 100 228 356), lower := (rows 11 131 292 28 19 32 64 128 256), losses := [] }

theorem u32990 : Upper (D 6) (R 6) [10,129,288,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32991 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 292 28 21 98 98 226 354), lower := (rows 11 131 292 28 21 32 64 128 256), losses := [] }

theorem u32991 : Upper (D 6) (R 6) [10,129,288,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32992 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 292 28 22 97 97 225 353), lower := (rows 11 131 292 28 22 32 64 128 256), losses := [] }

theorem u32992 : Upper (D 6) (R 6) [10,129,288,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32993 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 356, targets := 1 }], pairs := [(0,5),(1,5),(2,0)], upper := (rows 11 131 292 28 49 102 70 198 326), lower := (rows 11 131 292 28 49 32 64 128 256), losses := [] }

theorem u32993 : Upper (D 6) (R 6) [10,129,288,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32994 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 11 131 292 28 50 101 69 197 325), lower := (rows 11 131 292 28 50 32 64 128 256), losses := [] }

theorem u32994 : Upper (D 6) (R 6) [10,129,288,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32995 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 292 28 52 99 67 195 323), lower := (rows 11 131 292 28 52 32 64 128 256), losses := [] }

theorem u32995 : Upper (D 6) (R 6) [10,129,288,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32996 : Route 9 := (fun mask => (mask,id))

def c32996 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32996 : Upper (D 6) (R 6) [10,129,288,20,65] 13 := by
  apply FastRouting.sound _ _ [10,129,288,20,65] 13 (by decide) (choices 1) [2,4,64] r32996 c32996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15783
  · exact u15784
  · exact u15785

def r32997 : Route 9 := (fun mask => (mask,id))

def c32997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32997 : Upper (D 6) (R 6) [10,129,288,20,66] 13 := by
  apply FastRouting.sound _ _ [10,129,288,20,66] 13 (by decide) (choices 1) [1,4,64] r32997 c32997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15786
  · exact u15787
  · exact u15788

def b32998 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 292 28 84 99 99 227 355), lower := (rows 11 131 292 28 84 32 64 128 256), losses := [] }

theorem u32998 : Upper (D 6) (R 6) [10,129,288,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32999 : Route 9 := (fun mask => (mask,id))

def c32999 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32999 : Upper (D 6) (R 6) [10,129,288,20,96] 13 := by
  apply FastRouting.sound _ _ [10,129,288,20,96] 13 (by decide) (choices 1) [1,2,4,64] r32999 c32999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15789
  · exact u15790
  · exact u15791
  · exact u15792

#print axioms u32999
end Delivery.IrregularNine14.P06
