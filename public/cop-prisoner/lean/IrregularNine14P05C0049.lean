import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0012

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2940 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 164 25 56 34 332 396 268), lower := (rows 7 67 164 25 56 34 64 128 256), losses := [] }

theorem u2940 : Upper (D 5) (R 5) [6,65,160,17,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2940
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2941 : PairBound 9 := { available := 266, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 25 56 36 330 394 266), lower := (rows 7 67 164 25 56 36 64 128 256), losses := [] }

theorem u2941 : Upper (D 5) (R 5) [6,65,160,17,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2941
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2942 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 56, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 164 25 56 40 326 390 262), lower := (rows 7 67 164 25 56 40 64 128 256), losses := [] }

theorem u2942 : Upper (D 5) (R 5) [6,65,160,17,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2942
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2943 : Route 9 := (fun mask => (mask,id))

def c2943 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2943 : Upper (D 5) (R 5) [6,65,160,17,40,256] 13 := by
  apply FastRouting.sound _ _ [6,65,160,17,40,256] 13 (by decide) (choices 1) [2,4,8] r2943 c2943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u729
  · exact u730
  · exact u731

def b2944 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 67 164 25 276 34 104 168 296), lower := (rows 7 67 164 25 276 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 98 164 508 276 34 64 128 256) }] }

theorem u2944 : Upper (D 5) (R 5) [6,65,160,17,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2944
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2945 : Route 9 := (fun mask => (mask,id))

def c2945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2945 : Upper (D 5) (R 5) [6,65,160,17,260,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,17,260,8] 13 (by decide) (choices 1) [2,8,32] r2945 c2945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u732
  · exact u733
  · exact u734

def b2946 : PairBound 9 := { available := 44, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 67 164 25 280 34 108 172 300), lower := (rows 7 67 164 25 280 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 98 164 508 476 34 64 128 256) }] }

theorem u2946 : Upper (D 5) (R 5) [6,65,160,17,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2946
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2947 : PairBound 9 := { available := 42, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 25 280 36 106 170 298), lower := (rows 7 67 164 25 280 36 64 128 256), losses := [] }

theorem u2947 : Upper (D 5) (R 5) [6,65,160,17,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2947
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2948 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 25 280 40 102 166 294), lower := (rows 7 67 164 25 280 40 64 128 256), losses := [] }

theorem u2948 : Upper (D 5) (R 5) [6,65,160,17,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2948
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2949 : PairBound 9 := { available := 12, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 67 164 25 304 34 76 140 268), lower := (rows 7 67 164 25 304 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 98 164 508 304 34 64 128 256) }] }

theorem u2949 : Upper (D 5) (R 5) [6,65,160,17,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2949
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2950 : PairBound 9 := { available := 10, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 25 304 36 74 138 266), lower := (rows 7 67 164 25 304 36 64 128 256), losses := [] }

theorem u2950 : Upper (D 5) (R 5) [6,65,160,17,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2950
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2951 : Route 9 := (fun mask => (mask,id))

def c2951 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2951 : Upper (D 5) (R 5) [6,65,160,17,288,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,17,288,8] 13 (by decide) (choices 1) [2,4,8] r2951 c2951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u735
  · exact u736
  · exact u737

def b2952 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 164 26 56 33 332 396 268), lower := (rows 7 67 164 26 56 33 64 128 256), losses := [] }

theorem u2952 : Upper (D 5) (R 5) [6,65,160,18,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2952
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2953 : PairBound 9 := { available := 265, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 26 56 36 329 393 265), lower := (rows 7 67 164 26 56 36 64 128 256), losses := [] }

theorem u2953 : Upper (D 5) (R 5) [6,65,160,18,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2953
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2954 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 56, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 164 26 56 40 325 389 261), lower := (rows 7 67 164 26 56 40 64 128 256), losses := [] }

theorem u2954 : Upper (D 5) (R 5) [6,65,160,18,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2954
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2955 : Route 9 := (fun mask => (mask,id))

def c2955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2955 : Upper (D 5) (R 5) [6,65,160,18,40,256] 13 := by
  apply FastRouting.sound _ _ [6,65,160,18,40,256] 13 (by decide) (choices 1) [1,4,8] r2955 c2955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u738
  · exact u739
  · exact u740

def b2956 : PairBound 9 := { available := 40, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 26 276 33 104 168 296), lower := (rows 7 67 164 26 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 9 52 32 96 160 288), good := (rows 30 74 500 26 276 508 64 128 256) }] }

theorem u2956 : Upper (D 5) (R 5) [6,65,160,18,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2956
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2957 : Route 9 := (fun mask => (mask,id))

def c2957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2957 : Upper (D 5) (R 5) [6,65,160,18,260,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,18,260,8] 13 (by decide) (choices 1) [1,8,32] r2957 c2957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u741
  · exact u742
  · exact u743

def b2958 : PairBound 9 := { available := 44, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 67 164 26 280 33 108 172 300), lower := (rows 7 67 164 26 280 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 35 72 136 264), good := (rows 37 97 164 508 476 33 64 128 256) }] }

theorem u2958 : Upper (D 5) (R 5) [6,65,160,18,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2958
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2959 : PairBound 9 := { available := 41, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 26 280 36 105 169 297), lower := (rows 7 67 164 26 280 36 64 128 256), losses := [] }

theorem u2959 : Upper (D 5) (R 5) [6,65,160,18,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2959
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2960 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 26 280 40 101 165 293), lower := (rows 7 67 164 26 280 40 64 128 256), losses := [] }

theorem u2960 : Upper (D 5) (R 5) [6,65,160,18,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2960
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2961 : PairBound 9 := { available := 12, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 26 304 33 76 140 268), lower := (rows 7 67 164 26 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 52 9 52 32 105 169 297), good := (rows 478 458 500 478 500 508 64 128 256) }] }

theorem u2961 : Upper (D 5) (R 5) [6,65,160,18,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2961
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2962 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 26 304 36 73 137 265), lower := (rows 7 67 164 26 304 36 64 128 256), losses := [] }

theorem u2962 : Upper (D 5) (R 5) [6,65,160,18,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2962
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2963 : Route 9 := (fun mask => (mask,id))

def c2963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2963 : Upper (D 5) (R 5) [6,65,160,18,288,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,18,288,8] 13 (by decide) (choices 1) [1,4,8] r2963 c2963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u744
  · exact u745
  · exact u746

def b2964 : PairBound 9 := { available := 40, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 28 273 34 104 168 296), lower := (rows 7 67 164 28 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 98 164 476 508 34 64 128 256) }] }

theorem u2964 : Upper (D 5) (R 5) [6,65,160,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2964
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2965 : Route 9 := (fun mask => (mask,id))

def c2965 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2965 : Upper (D 5) (R 5) [6,65,160,20,257,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,20,257,8] 13 (by decide) (choices 1) [2,8,32] r2965 c2965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u747
  · exact u748
  · exact u749

def b2966 : PairBound 9 := { available := 40, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 28 274 33 104 168 296), lower := (rows 7 67 164 28 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 17 32 100 164 292), good := (rows 478 90 492 476 274 508 64 128 256) }] }

theorem u2966 : Upper (D 5) (R 5) [6,65,160,20,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2966
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2967 : Route 9 := (fun mask => (mask,id))

def c2967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2967 : Upper (D 5) (R 5) [6,65,160,20,258,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,20,258,8] 13 (by decide) (choices 1) [1,8,32] r2967 c2967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u750
  · exact u751
  · exact u752

def r2968 : Route 9 := (fun mask => (mask,id))

def c2968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2968 : Upper (D 5) (R 5) [6,65,160,20,264,1] 13 := by
  apply FastRouting.sound _ _ [6,65,160,20,264,1] 13 (by decide) (choices 1) [2,8,32] r2968 c2968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u753
  · exact u754
  · exact u755

def r2969 : Route 9 := (fun mask => (mask,id))

def c2969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2969 : Upper (D 5) (R 5) [6,65,160,20,264,2] 13 := by
  apply FastRouting.sound _ _ [6,65,160,20,264,2] 13 (by decide) (choices 1) [1,8,32] r2969 c2969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u756
  · exact u757
  · exact u758

def b2970 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 28 280 40 99 163 291), lower := (rows 7 67 164 28 280 40 64 128 256), losses := [] }

theorem u2970 : Upper (D 5) (R 5) [6,65,160,20,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2970
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2971 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 67 164 41 274 36 88 152 280), lower := (rows 7 67 164 41 274 36 64 128 256), losses := [] }

theorem u2971 : Upper (D 5) (R 5) [6,65,160,33,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2971
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2972 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 164 41 274 40 92 156 284), lower := (rows 7 67 164 41 274 40 64 128 256), losses := [] }

theorem u2972 : Upper (D 5) (R 5) [6,65,160,33,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2972
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2973 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 274 48 76 140 268), lower := (rows 7 67 164 41 274 48 64 128 256), losses := [] }

theorem u2973 : Upper (D 5) (R 5) [6,65,160,33,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2973
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2974 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 41 276 34 88 152 280), lower := (rows 7 67 164 41 276 34 64 128 256), losses := [] }

theorem u2974 : Upper (D 5) (R 5) [6,65,160,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2974
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2975 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 164 41 276 40 90 154 282), lower := (rows 7 67 164 41 276 40 64 128 256), losses := [] }

theorem u2975 : Upper (D 5) (R 5) [6,65,160,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2975
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2976 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 7 67 164 41 276 48 74 138 266), lower := (rows 7 67 164 41 276 48 64 128 256), losses := [] }

theorem u2976 : Upper (D 5) (R 5) [6,65,160,33,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2976
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2977 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 41 280 34 92 156 284), lower := (rows 7 67 164 41 280 34 64 128 256), losses := [] }

theorem u2977 : Upper (D 5) (R 5) [6,65,160,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2977
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2978 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 67 164 41 280 36 90 154 282), lower := (rows 7 67 164 41 280 36 64 128 256), losses := [] }

theorem u2978 : Upper (D 5) (R 5) [6,65,160,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2978
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2979 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 164 41 280 40 86 150 278), lower := (rows 7 67 164 41 280 40 64 128 256), losses := [] }

theorem u2979 : Upper (D 5) (R 5) [6,65,160,33,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2979
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2980 : Route 9 := (fun mask => (mask,id))

def c2980 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2980 : Upper (D 5) (R 5) [6,65,160,33,264,16] 13 := by
  apply FastRouting.sound _ _ [6,65,160,33,264,16] 13 (by decide) (choices 1) [2,4,8] r2980 c2980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u759
  · exact u760
  · exact u761

def b2981 : PairBound 9 := { available := 24, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 42 273 36 88 152 280), lower := (rows 7 67 164 42 273 36 64 128 256), losses := [] }

theorem u2981 : Upper (D 5) (R 5) [6,65,160,34,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2981
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2982 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 164 42 273 40 92 156 284), lower := (rows 7 67 164 42 273 40 64 128 256), losses := [] }

theorem u2982 : Upper (D 5) (R 5) [6,65,160,34,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2982
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2983 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 42 273 48 76 140 268), lower := (rows 7 67 164 42 273 48 64 128 256), losses := [] }

theorem u2983 : Upper (D 5) (R 5) [6,65,160,34,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2983
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2984 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 42 276 33 88 152 280), lower := (rows 7 67 164 42 276 33 64 128 256), losses := [] }

theorem u2984 : Upper (D 5) (R 5) [6,65,160,34,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2984
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2985 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 164 42 276 40 89 153 281), lower := (rows 7 67 164 42 276 40 64 128 256), losses := [] }

theorem u2985 : Upper (D 5) (R 5) [6,65,160,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2985
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2986 : Route 9 := (fun mask => (mask,id))

def c2986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2986 : Upper (D 5) (R 5) [6,65,160,34,260,16] 13 := by
  apply FastRouting.sound _ _ [6,65,160,34,260,16] 13 (by decide) (choices 1) [1,8] r2986 c2986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u762
  · exact u763

def b2987 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 42 280 33 92 156 284), lower := (rows 7 67 164 42 280 33 64 128 256), losses := [] }

theorem u2987 : Upper (D 5) (R 5) [6,65,160,34,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2987
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2988 : PairBound 9 := { available := 25, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 42 280 36 89 153 281), lower := (rows 7 67 164 42 280 36 64 128 256), losses := [] }

theorem u2988 : Upper (D 5) (R 5) [6,65,160,34,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2988
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2989 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 164 42 280 40 85 149 277), lower := (rows 7 67 164 42 280 40 64 128 256), losses := [] }

theorem u2989 : Upper (D 5) (R 5) [6,65,160,34,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2989
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2990 : Route 9 := (fun mask => (mask,id))

def c2990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2990 : Upper (D 5) (R 5) [6,65,160,34,264,16] 13 := by
  apply FastRouting.sound _ _ [6,65,160,34,264,16] 13 (by decide) (choices 1) [1,4,8] r2990 c2990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u764
  · exact u765
  · exact u766

def b2991 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 164 56 25 34 332 396 268), lower := (rows 7 67 164 56 25 34 64 128 256), losses := [] }

theorem u2991 : Upper (D 5) (R 5) [6,65,160,48,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2991
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2992 : PairBound 9 := { available := 266, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 25 36 330 394 266), lower := (rows 7 67 164 56 25 36 64 128 256), losses := [] }

theorem u2992 : Upper (D 5) (R 5) [6,65,160,48,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2992
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2993 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 56, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 164 56 25 40 326 390 262), lower := (rows 7 67 164 56 25 40 64 128 256), losses := [] }

theorem u2993 : Upper (D 5) (R 5) [6,65,160,48,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2993
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2994 : Route 9 := (fun mask => (mask,id))

def c2994 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2994 : Upper (D 5) (R 5) [6,65,160,48,9,256] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,9,256] 13 (by decide) (choices 1) [2,4,8] r2994 c2994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u767
  · exact u768
  · exact u769

def b2995 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 164 56 26 33 332 396 268), lower := (rows 7 67 164 56 26 33 64 128 256), losses := [] }

theorem u2995 : Upper (D 5) (R 5) [6,65,160,48,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2995
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2996 : PairBound 9 := { available := 265, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 26 36 329 393 265), lower := (rows 7 67 164 56 26 36 64 128 256), losses := [] }

theorem u2996 : Upper (D 5) (R 5) [6,65,160,48,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2996
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2997 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 56, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 164 56 26 40 325 389 261), lower := (rows 7 67 164 56 26 40 64 128 256), losses := [] }

theorem u2997 : Upper (D 5) (R 5) [6,65,160,48,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2997
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2998 : Route 9 := (fun mask => (mask,id))

def c2998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2998 : Upper (D 5) (R 5) [6,65,160,48,10,256] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,10,256] 13 (by decide) (choices 1) [1,4,8] r2998 c2998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u770
  · exact u771
  · exact u772

def b2999 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 273 34 76 140 268), lower := (rows 7 67 164 56 273 34 64 128 256), losses := [] }

theorem u2999 : Upper (D 5) (R 5) [6,65,160,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2999
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2999
end Delivery.IrregularNine14.P05
