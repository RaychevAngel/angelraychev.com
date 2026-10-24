import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0073

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r16920 : Route 9 := (fun mask => (mask,id))

def c16920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16920 : Upper (D 6) (R 6) [10,144,258,36,68,64] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36,68,64] 13 (by decide) (choices 1) [1,32] r16920 c16920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4389
  · exact u4390

def b16921 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,6),(2,5),(3,6)], upper := (rows 11 146 262 44 112 33 69 197 325), lower := (rows 11 146 262 44 112 33 64 128 256), losses := [] }

theorem u16921 : Upper (D 6) (R 6) [10,144,258,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16922 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 146 262 44 112 36 65 193 321), lower := (rows 11 146 262 44 112 36 64 128 256), losses := [] }

theorem u16922 : Upper (D 6) (R 6) [10,144,258,36,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16923 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 262 44 112 96 69 133 261), lower := (rows 11 146 262 44 112 96 64 128 256), losses := [] }

theorem u16923 : Upper (D 6) (R 6) [10,144,258,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16924 : Route 9 := (fun mask => (mask,id))

def c16924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16924 : Upper (D 6) (R 6) [10,144,258,96,5,1] 13 := by
  apply FastRouting.sound _ _ [10,144,258,96,5,1] 13 (by decide) (choices 1) [4,32] r16924 c16924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4391
  · exact u4392

theorem m16925_1 : Upper (D 6) (R 6) [10,144,258,96,5,4,1] 13 :=
  permutation_upper _ _ _ [10,144,258,96,5,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4391

def r16925 : Route 9 := (fun mask => (mask,id))

def c16925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16925 : Upper (D 6) (R 6) [10,144,258,96,5,4] 13 := by
  apply FastRouting.sound _ _ [10,144,258,96,5,4] 13 (by decide) (choices 1) [1,32] r16925 c16925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16925_1
  · exact u4393

def b16926 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 262 104 21 96 101 165 293), lower := (rows 11 146 262 104 21 96 64 128 256), losses := [] }

theorem u16926 : Upper (D 6) (R 6) [10,144,258,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16927 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 146 262 104 49 33 68 196 324), lower := (rows 11 146 262 104 49 33 64 128 256), losses := [] }

theorem u16927 : Upper (D 6) (R 6) [10,144,258,96,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16928 : Route 9 := (fun mask => (mask,id))

def c16928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16928 : Upper (D 6) (R 6) [10,144,258,96,33,4] 13 := by
  apply FastRouting.sound _ _ [10,144,258,96,33,4] 13 (by decide) (choices 1) [1,4] r16928 c16928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4394
  · exact u4395

def b16929 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 262 104 49 96 69 133 261), lower := (rows 11 146 262 104 49 96 64 128 256), losses := [] }

theorem u16929 : Upper (D 6) (R 6) [10,144,258,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16930 : Route 9 := (fun mask => (mask,id))

def c16930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16930 : Upper (D 6) (R 6) [10,144,258,96,36,1] 13 := by
  apply FastRouting.sound _ _ [10,144,258,96,36,1] 13 (by decide) (choices 1) [1,4] r16930 c16930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4396
  · exact u4397

def b16931 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 262 104 52 36 65 193 321), lower := (rows 11 146 262 104 52 36 64 128 256), losses := [] }

theorem u16931 : Upper (D 6) (R 6) [10,144,258,96,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16932 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 262 104 52 96 69 133 261), lower := (rows 11 146 262 104 52 96 64 128 256), losses := [] }

theorem u16932 : Upper (D 6) (R 6) [10,144,258,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16933 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 454, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 11 146 292 13 49 34 68 196 324), lower := (rows 11 146 292 13 49 34 64 128 256), losses := [] }

theorem u16933 : Upper (D 6) (R 6) [10,144,288,5,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16934 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 13 49 36 66 194 322), lower := (rows 11 146 292 13 49 36 64 128 256), losses := [] }

theorem u16934 : Upper (D 6) (R 6) [10,144,288,5,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16935 : Route 9 := (fun mask => (mask,id))

def c16935 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16935 : Upper (D 6) (R 6) [10,144,288,5,33,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,33,64] 13 (by decide) (choices 1) [2,4] r16935 c16935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4398
  · exact u4399

def b16936 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 50 33 68 196 324), lower := (rows 11 146 292 13 50 33 64 128 256), losses := [] }

theorem u16936 : Upper (D 6) (R 6) [10,144,288,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16937 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 13 50 36 65 193 321), lower := (rows 11 146 292 13 50 36 64 128 256), losses := [] }

theorem u16937 : Upper (D 6) (R 6) [10,144,288,5,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16938 : Route 9 := (fun mask => (mask,id))

def c16938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16938 : Upper (D 6) (R 6) [10,144,288,5,34,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,34,64] 13 (by decide) (choices 1) [1,4] r16938 c16938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4400
  · exact u4401

def b16939 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 5, region := 324, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 146 292 13 81 34 100 228 356), lower := (rows 11 146 292 13 81 34 64 128 256), losses := [] }

theorem u16939 : Upper (D 6) (R 6) [10,144,288,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16940 : PairBound 9 := { available := 98, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 13 81 36 98 226 354), lower := (rows 11 146 292 13 81 36 64 128 256), losses := [] }

theorem u16940 : Upper (D 6) (R 6) [10,144,288,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16941 : Route 9 := (fun mask => (mask,id))

def c16941 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16941 : Upper (D 6) (R 6) [10,144,288,5,65,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,65,64] 13 (by decide) (choices 1) [2,4,32] r16941 c16941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4402
  · exact u4403
  · exact u4404

def b16942 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 82 33 100 228 356), lower := (rows 11 146 292 13 82 33 64 128 256), losses := [] }

theorem u16942 : Upper (D 6) (R 6) [10,144,288,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16943 : PairBound 9 := { available := 97, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 13 82 36 97 225 353), lower := (rows 11 146 292 13 82 36 64 128 256), losses := [] }

theorem u16943 : Upper (D 6) (R 6) [10,144,288,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16944 : Route 9 := (fun mask => (mask,id))

def c16944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16944 : Upper (D 6) (R 6) [10,144,288,5,66,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,66,64] 13 (by decide) (choices 1) [1,4,32] r16944 c16944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4405
  · exact u4406
  · exact u4407

def b16945 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 84 33 98 226 354), lower := (rows 11 146 292 13 84 33 64 128 256), losses := [] }

theorem u16945 : Upper (D 6) (R 6) [10,144,288,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16946 : Route 9 := (fun mask => (mask,id))

def c16946 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16946 : Upper (D 6) (R 6) [10,144,288,5,68,2] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,68,2] 13 (by decide) (choices 1) [1,32] r16946 c16946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4408
  · exact u4409

def r16947 : Route 9 := (fun mask => (mask,id))

def c16947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16947 : Upper (D 6) (R 6) [10,144,288,5,68,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,68,64] 13 (by decide) (choices 1) [1,2,32] r16947 c16947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4410
  · exact u4411
  · exact u4412

def b16948 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 112 33 70 198 326), lower := (rows 11 146 292 13 112 33 64 128 256), losses := [] }

theorem u16948 : Upper (D 6) (R 6) [10,144,288,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16949 : Route 9 := (fun mask => (mask,id))

def c16949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16949 : Upper (D 6) (R 6) [10,144,288,5,96,2] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5,96,2] 13 (by decide) (choices 1) [1,4] r16949 c16949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4413
  · exact u4414

def b16950 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 13 112 36 67 195 323), lower := (rows 11 146 292 13 112 36 64 128 256), losses := [] }

theorem u16950 : Upper (D 6) (R 6) [10,144,288,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16951 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 292 13 112 96 71 135 263), lower := (rows 11 146 292 13 112 96 64 128 256), losses := [] }

theorem u16951 : Upper (D 6) (R 6) [10,144,288,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16952 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 292 41 22 33 68 196 324), lower := (rows 11 146 292 41 22 33 64 128 256), losses := [] }

theorem u16952 : Upper (D 6) (R 6) [10,144,288,33,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16953 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 41 22 36 65 193 321), lower := (rows 11 146 292 41 22 36 64 128 256), losses := [] }

theorem u16953 : Upper (D 6) (R 6) [10,144,288,33,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16954 : Route 9 := (fun mask => (mask,id))

def c16954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16954 : Upper (D 6) (R 6) [10,144,288,33,6,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,33,6,64] 13 (by decide) (choices 1) [1,4] r16954 c16954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4415
  · exact u4416

def b16955 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 292 41 81 34 68 196 324), lower := (rows 11 146 292 41 81 34 64 128 256), losses := [] }

theorem u16955 : Upper (D 6) (R 6) [10,144,288,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16956 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 41 81 36 70 198 326), lower := (rows 11 146 292 41 81 36 64 128 256), losses := [] }

theorem u16956 : Upper (D 6) (R 6) [10,144,288,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16957 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 40, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 146 292 41 81 96 70 134 262), lower := (rows 11 146 292 41 81 96 64 128 256), losses := [] }

theorem u16957 : Upper (D 6) (R 6) [10,144,288,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16958 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 292 41 82 33 68 196 324), lower := (rows 11 146 292 41 82 33 64 128 256), losses := [] }

theorem u16958 : Upper (D 6) (R 6) [10,144,288,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16959 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 41 82 36 69 197 325), lower := (rows 11 146 292 41 82 36 64 128 256), losses := [] }

theorem u16959 : Upper (D 6) (R 6) [10,144,288,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16960 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 146 292 41 82 96 69 133 261), lower := (rows 11 146 292 41 82 96 64 128 256), losses := [] }

theorem u16960 : Upper (D 6) (R 6) [10,144,288,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16961 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 292 41 84 33 70 198 326), lower := (rows 11 146 292 41 84 33 64 128 256), losses := [] }

theorem u16961 : Upper (D 6) (R 6) [10,144,288,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16962 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 292 41 84 34 69 197 325), lower := (rows 11 146 292 41 84 34 64 128 256), losses := [] }

theorem u16962 : Upper (D 6) (R 6) [10,144,288,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16963 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 41 84 36 67 195 323), lower := (rows 11 146 292 41 84 36 64 128 256), losses := [] }

theorem u16963 : Upper (D 6) (R 6) [10,144,288,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16964 : PairBound 9 := { available := 7, camps := [], pairs := [(0,2),(2,6),(3,2)], upper := (rows 11 146 292 41 84 96 71 135 263), lower := (rows 11 146 292 41 84 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 10 16 112 64 128 256), good := (rows 11 187 288 41 112 96 96 128 256) },{ target := 6, region := (rows 1 2 12 8 16 32 0 129 257), good := (rows 399 146 292 429 20 32 0 128 256) }] }

theorem u16964 : Upper (D 6) (R 6) [10,144,288,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16965 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 5, region := 324, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 146 292 73 21 34 100 228 356), lower := (rows 11 146 292 73 21 34 64 128 256), losses := [] }

theorem u16965 : Upper (D 6) (R 6) [10,144,288,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16966 : PairBound 9 := { available := 98, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 73 21 36 98 226 354), lower := (rows 11 146 292 73 21 36 64 128 256), losses := [] }

theorem u16966 : Upper (D 6) (R 6) [10,144,288,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16967 : Route 9 := (fun mask => (mask,id))

def c16967 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16967 : Upper (D 6) (R 6) [10,144,288,65,5,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65,5,64] 13 (by decide) (choices 1) [2,4,32] r16967 c16967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4417
  · exact u4418
  · exact u4419

def b16968 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 73 22 33 100 228 356), lower := (rows 11 146 292 73 22 33 64 128 256), losses := [] }

theorem u16968 : Upper (D 6) (R 6) [10,144,288,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16969 : PairBound 9 := { available := 97, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 73 22 36 97 225 353), lower := (rows 11 146 292 73 22 36 64 128 256), losses := [] }

theorem u16969 : Upper (D 6) (R 6) [10,144,288,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16970 : Route 9 := (fun mask => (mask,id))

def c16970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16970 : Upper (D 6) (R 6) [10,144,288,65,6,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65,6,64] 13 (by decide) (choices 1) [1,4,32] r16970 c16970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4420
  · exact u4421
  · exact u4422

def b16971 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 454, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 11 146 292 73 49 34 68 196 324), lower := (rows 11 146 292 73 49 34 64 128 256), losses := [] }

theorem u16971 : Upper (D 6) (R 6) [10,144,288,65,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16972 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 73 49 36 70 198 326), lower := (rows 11 146 292 73 49 36 64 128 256), losses := [] }

theorem u16972 : Upper (D 6) (R 6) [10,144,288,65,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16973 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 48, targets := 6 },{ cop := 4, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 146 292 73 49 96 70 134 262), lower := (rows 11 146 292 73 49 96 64 128 256), losses := [] }

theorem u16973 : Upper (D 6) (R 6) [10,144,288,65,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16974 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 73 50 33 68 196 324), lower := (rows 11 146 292 73 50 33 64 128 256), losses := [] }

theorem u16974 : Upper (D 6) (R 6) [10,144,288,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16975 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 73 50 36 69 197 325), lower := (rows 11 146 292 73 50 36 64 128 256), losses := [] }

theorem u16975 : Upper (D 6) (R 6) [10,144,288,65,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16976 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 11 146 292 73 50 96 69 133 261), lower := (rows 11 146 292 73 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 104 64 128 256), good := (rows 58 146 292 120 50 96 96 128 256) }] }

theorem u16976 : Upper (D 6) (R 6) [10,144,288,65,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16977 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 73 84 33 102 166 294), lower := (rows 11 146 292 73 84 33 64 128 256), losses := [] }

theorem u16977 : Upper (D 6) (R 6) [10,144,288,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16978 : Route 9 := (fun mask => (mask,id))

def c16978 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16978 : Upper (D 6) (R 6) [10,144,288,65,68,2] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65,68,2] 13 (by decide) (choices 1) [1,4,32] r16978 c16978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4423
  · exact u4424
  · exact u4425

def b16979 : PairBound 9 := { available := 35, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 73 84 36 99 163 291), lower := (rows 11 146 292 73 84 36 64 128 256), losses := [] }

theorem u16979 : Upper (D 6) (R 6) [10,144,288,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16979
end Delivery.IrregularNine14.P06
