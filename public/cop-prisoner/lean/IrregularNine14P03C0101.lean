import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0048
import IrregularNine14P03C0049
import IrregularNine14P03C0050
import IrregularNine14P03C0051
import IrregularNine14P03C0052

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6060 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 35 14 196 200 305 305 369 433 305), lower := (rows 35 14 196 200 16 32 64 128 256), losses := [] }

theorem u6060 : Upper (D 3) (R 3) [34,12,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6060
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6061 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6061 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6061 : Upper (D 3) (R 3) [34,12,192,257] 13 := by
  apply FastRouting.sound _ _ [34,12,192,257] 13 (by decide) (choices 2) [33,65,96,192] r6061 c6061
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2915
  · exact u2916
  · exact u2917
  · exact u2918

def r6062 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6062 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6062 : Upper (D 3) (R 3) [34,12,192,272] 13 := by
  apply FastRouting.sound _ _ [34,12,192,272] 13 (by decide) (choices 2) [33,65,96,192] r6062 c6062
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2919
  · exact u2920
  · exact u2921
  · exact u2922

def b6063 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 196 296 209 241 209 209 465), lower := (rows 35 14 196 296 16 32 64 128 256), losses := [] }

theorem u6063 : Upper (D 3) (R 3) [34,12,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6063
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6064 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 196 328 177 177 241 177 433), lower := (rows 35 14 196 328 16 32 64 128 256), losses := [] }

theorem u6064 : Upper (D 3) (R 3) [34,12,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6064
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6065 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 13 496 496 496 496 496), lower := (rows 35 67 13 13 16 32 64 128 256), losses := [] }

theorem u6065 : Upper (D 3) (R 3) [34,65,9,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6065
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6066 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 25 500 484 484 484 484), lower := (rows 35 67 13 25 16 32 64 128 256), losses := [] }

theorem u6066 : Upper (D 3) (R 3) [34,65,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6066
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6067 : Route 9 := (fun mask => (mask,id))

def c6067 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6067 : Upper (D 3) (R 3) [34,65,9,20] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r6067 c6067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2937
  · exact u2938
  · exact u2939
  · exact u2940
  · exact u2941
  · exact u2942
  · exact u2943
  · exact u2944
  · exact u2945
  · exact u2946

def b6068 : PairBound 9 := { available := 468, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 41 468 500 468 468 468), lower := (rows 35 67 13 41 16 32 64 128 256), losses := [] }

theorem u6068 : Upper (D 3) (R 3) [34,65,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6068
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6069 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 465 497 465 465 465), lower := (rows 35 67 13 44 16 32 64 128 256), losses := [] }

theorem u6069 : Upper (D 3) (R 3) [34,65,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6069
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6070 : PairBound 9 := { available := 453, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 56 469 485 453 453 453), lower := (rows 35 67 13 56 16 32 64 128 256), losses := [] }

theorem u6070 : Upper (D 3) (R 3) [34,65,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6070
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6071 : PairBound 9 := { available := 436, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 73 436 436 500 436 436), lower := (rows 35 67 13 73 16 32 64 128 256), losses := [] }

theorem u6071 : Upper (D 3) (R 3) [34,65,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6071
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6072 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 433 433 497 433 433), lower := (rows 35 67 13 76 16 32 64 128 256), losses := [] }

theorem u6072 : Upper (D 3) (R 3) [34,65,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6072
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6073 : PairBound 9 := { available := 421, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 88 437 421 485 421 421), lower := (rows 35 67 13 88 16 32 64 128 256), losses := [] }

theorem u6073 : Upper (D 3) (R 3) [34,65,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6073
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6074 : PairBound 9 := { available := 405, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 104 405 437 469 405 405), lower := (rows 35 67 13 104 16 32 64 128 256), losses := [] }

theorem u6074 : Upper (D 3) (R 3) [34,65,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6074
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6075 : PairBound 9 := { available := 500, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 500 500 500 500 500), lower := (rows 35 67 13 137 16 32 64 128 256), losses := [] }

theorem u6075 : Upper (D 3) (R 3) [34,65,9,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6075
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6076 : Route 9 := (fun mask => (mask,id))

def c6076 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6076 : Upper (D 3) (R 3) [34,65,9,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r6076 c6076
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2999
  · exact u3000
  · exact u3001
  · exact u3002
  · exact u3003
  · exact u3004
  · exact u3005
  · exact u3006
  · exact u3007
  · exact u3008

theorem m6077_5 : Upper (D 3) (R 3) [34,65,9,144,5] 13 :=
  permutation_upper _ _ _ [34,65,9,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2930

def r6077 : Route 9 := (fun mask => (mask,id))

def c6077 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6077 : Upper (D 3) (R 3) [34,65,9,144] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r6077 c6077
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6077_5
  · exact u3009
  · exact u3010
  · exact u3011
  · exact u3012
  · exact u3013
  · exact u3014
  · exact u3015
  · exact u3016
  · exact u3017
  · exact u3018
  · exact u3019
  · exact u3020
  · exact u3021
  · exact u3022

def b6078 : PairBound 9 := { available := 469, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 168 469 501 469 469 469), lower := (rows 35 67 13 168 16 32 64 128 256), losses := [] }

theorem u6078 : Upper (D 3) (R 3) [34,65,9,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6078
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6079 : PairBound 9 := { available := 437, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 200 437 437 501 437 437), lower := (rows 35 67 13 200 16 32 64 128 256), losses := [] }

theorem u6079 : Upper (D 3) (R 3) [34,65,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6079
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6080 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 265 244 244 244 244 500), lower := (rows 35 67 13 265 16 32 64 128 256), losses := [] }

theorem u6080 : Upper (D 3) (R 3) [34,65,9,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6080
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6081 : Route 9 := (fun mask => (mask,id))

def c6081 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6081 : Upper (D 3) (R 3) [34,65,9,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6081 c6081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3044
  · exact u3045
  · exact u3046
  · exact u3047
  · exact u3048
  · exact u3049

theorem m6082_5 : Upper (D 3) (R 3) [34,65,9,272,5] 13 :=
  permutation_upper _ _ _ [34,65,9,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2933

def r6082 : Route 9 := (fun mask => (mask,id))

def c6082 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6082 : Upper (D 3) (R 3) [34,65,9,272] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r6082 c6082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6082_5
  · exact u3050
  · exact u3051
  · exact u3052
  · exact u3053
  · exact u3054
  · exact u3055
  · exact u3056
  · exact u3057
  · exact u3058

def b6083 : PairBound 9 := { available := 213, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 296 213 245 213 213 469), lower := (rows 35 67 13 296 16 32 64 128 256), losses := [] }

theorem u6083 : Upper (D 3) (R 3) [34,65,9,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6083
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6084 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 328 181 181 245 181 437), lower := (rows 35 67 13 328 16 32 64 128 256), losses := [] }

theorem u6084 : Upper (D 3) (R 3) [34,65,9,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6084
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6085_5 : Upper (D 3) (R 3) [34,65,9,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2936

def r6085 : Route 9 := (fun mask => (mask,id))

def c6085 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6085 : Upper (D 3) (R 3) [34,65,9,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r6085 c6085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6085_5
  · exact u3067
  · exact u3068
  · exact u3069
  · exact u3070
  · exact u3071
  · exact u3072
  · exact u3073
  · exact u3074
  · exact u3075

theorem m6086_9 : Upper (D 3) (R 3) [34,65,17,36,9] 13 :=
  permutation_upper _ _ _ [34,65,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2928

theorem m6086_65 : Upper (D 3) (R 3) [34,65,17,36,65] 13 :=
  permutation_upper _ _ _ [34,65,9,65,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2966

theorem m6086_72 : Upper (D 3) (R 3) [34,65,17,36,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2977

theorem m6086_129 : Upper (D 3) (R 3) [34,65,17,36,129] 13 :=
  permutation_upper _ _ _ [34,65,9,129,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2990

theorem m6086_136 : Upper (D 3) (R 3) [34,65,17,36,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3010

theorem m6086_192 : Upper (D 3) (R 3) [34,65,17,36,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3031

theorem m6086_257 : Upper (D 3) (R 3) [34,65,17,36,257] 13 :=
  permutation_upper _ _ _ [34,65,9,257,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3039

theorem m6086_264 : Upper (D 3) (R 3) [34,65,17,36,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3051

theorem m6086_320 : Upper (D 3) (R 3) [34,65,17,36,320] 13 :=
  permutation_upper _ _ _ [34,65,9,320,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3063

theorem m6086_384 : Upper (D 3) (R 3) [34,65,17,36,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3068

def r6086 : Route 9 := (fun mask => (mask,id))

def c6086 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6086 : Upper (D 3) (R 3) [34,65,17,36] 13 := by
  apply FastRouting.sound _ _ [34,65,17,36] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r6086 c6086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6086_9
  · exact m6086_65
  · exact m6086_72
  · exact m6086_129
  · exact m6086_136
  · exact m6086_192
  · exact m6086_257
  · exact m6086_264
  · exact m6086_320
  · exact m6086_384

theorem m6087_9 : Upper (D 3) (R 3) [34,65,17,68,9] 13 :=
  permutation_upper _ _ _ [34,65,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2929

theorem m6087_33 : Upper (D 3) (R 3) [34,65,17,68,33] 13 :=
  permutation_upper _ _ _ [34,65,9,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2947

theorem m6087_40 : Upper (D 3) (R 3) [34,65,17,68,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2958

theorem m6087_129 : Upper (D 3) (R 3) [34,65,17,68,129] 13 :=
  permutation_upper _ _ _ [34,65,9,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2991

theorem m6087_136 : Upper (D 3) (R 3) [34,65,17,68,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3012

theorem m6087_160 : Upper (D 3) (R 3) [34,65,17,68,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3023

theorem m6087_257 : Upper (D 3) (R 3) [34,65,17,68,257] 13 :=
  permutation_upper _ _ _ [34,65,9,257,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3040

theorem m6087_264 : Upper (D 3) (R 3) [34,65,17,68,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3053

theorem m6087_288 : Upper (D 3) (R 3) [34,65,17,68,288] 13 :=
  permutation_upper _ _ _ [34,65,9,288,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3059

theorem m6087_384 : Upper (D 3) (R 3) [34,65,17,68,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3070

def r6087 : Route 9 := (fun mask => (mask,id))

def c6087 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6087 : Upper (D 3) (R 3) [34,65,17,68] 13 := by
  apply FastRouting.sound _ _ [34,65,17,68] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r6087 c6087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6087_9
  · exact m6087_33
  · exact m6087_40
  · exact m6087_129
  · exact m6087_136
  · exact m6087_160
  · exact m6087_257
  · exact m6087_264
  · exact m6087_288
  · exact m6087_384

theorem m6088_12 : Upper (D 3) (R 3) [34,65,17,129,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2940

theorem m6088_36 : Upper (D 3) (R 3) [34,65,17,129,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2953

theorem m6088_40 : Upper (D 3) (R 3) [34,65,17,129,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2959

theorem m6088_68 : Upper (D 3) (R 3) [34,65,17,129,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2972

theorem m6088_72 : Upper (D 3) (R 3) [34,65,17,129,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2978

theorem m6088_96 : Upper (D 3) (R 3) [34,65,17,129,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2985

theorem m6088_132 : Upper (D 3) (R 3) [34,65,17,129,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3002

theorem m6088_136 : Upper (D 3) (R 3) [34,65,17,129,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3014

theorem m6088_160 : Upper (D 3) (R 3) [34,65,17,129,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3024

theorem m6088_192 : Upper (D 3) (R 3) [34,65,17,129,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3032

theorem m6088_260 : Upper (D 3) (R 3) [34,65,17,129,260] 13 :=
  permutation_upper _ _ _ [34,65,9,260,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3047

theorem m6088_264 : Upper (D 3) (R 3) [34,65,17,129,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3055

theorem m6088_288 : Upper (D 3) (R 3) [34,65,17,129,288] 13 :=
  permutation_upper _ _ _ [34,65,9,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3060

theorem m6088_320 : Upper (D 3) (R 3) [34,65,17,129,320] 13 :=
  permutation_upper _ _ _ [34,65,9,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3064

theorem m6088_384 : Upper (D 3) (R 3) [34,65,17,129,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3072

def r6088 : Route 9 := (fun mask => (mask,id))

def c6088 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u6088 : Upper (D 3) (R 3) [34,65,17,129] 13 := by
  apply FastRouting.sound _ _ [34,65,17,129] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192,260,264,288,320,384] r6088 c6088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6088_12
  · exact m6088_36
  · exact m6088_40
  · exact m6088_68
  · exact m6088_72
  · exact m6088_96
  · exact m6088_132
  · exact m6088_136
  · exact m6088_160
  · exact m6088_192
  · exact m6088_260
  · exact m6088_264
  · exact m6088_288
  · exact m6088_320
  · exact m6088_384

theorem m6089_9 : Upper (D 3) (R 3) [34,65,17,132,9] 13 :=
  permutation_upper _ _ _ [34,65,9,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2930

theorem m6089_33 : Upper (D 3) (R 3) [34,65,17,132,33] 13 :=
  permutation_upper _ _ _ [34,65,9,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2948

theorem m6089_40 : Upper (D 3) (R 3) [34,65,17,132,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2960

theorem m6089_65 : Upper (D 3) (R 3) [34,65,17,132,65] 13 :=
  permutation_upper _ _ _ [34,65,9,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2967

theorem m6089_72 : Upper (D 3) (R 3) [34,65,17,132,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2979

theorem m6089_96 : Upper (D 3) (R 3) [34,65,17,132,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2986

theorem m6089_129 : Upper (D 3) (R 3) [34,65,17,132,129] 13 :=
  permutation_upper _ _ _ [34,65,9,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2992

theorem m6089_136 : Upper (D 3) (R 3) [34,65,17,132,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3015

theorem m6089_160 : Upper (D 3) (R 3) [34,65,17,132,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3025

theorem m6089_192 : Upper (D 3) (R 3) [34,65,17,132,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3033

theorem m6089_257 : Upper (D 3) (R 3) [34,65,17,132,257] 13 :=
  permutation_upper _ _ _ [34,65,9,257,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3041

theorem m6089_264 : Upper (D 3) (R 3) [34,65,17,132,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3056

theorem m6089_288 : Upper (D 3) (R 3) [34,65,17,132,288] 13 :=
  permutation_upper _ _ _ [34,65,9,288,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3061

theorem m6089_320 : Upper (D 3) (R 3) [34,65,17,132,320] 13 :=
  permutation_upper _ _ _ [34,65,9,320,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3065

theorem m6089_384 : Upper (D 3) (R 3) [34,65,17,132,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3073

def r6089 : Route 9 := (fun mask => (mask,id))

def c6089 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u6089 : Upper (D 3) (R 3) [34,65,17,132] 13 := by
  apply FastRouting.sound _ _ [34,65,17,132] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r6089 c6089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6089_9
  · exact m6089_33
  · exact m6089_40
  · exact m6089_65
  · exact m6089_72
  · exact m6089_96
  · exact m6089_129
  · exact m6089_136
  · exact m6089_160
  · exact m6089_192
  · exact m6089_257
  · exact m6089_264
  · exact m6089_288
  · exact m6089_320
  · exact m6089_384

theorem m6090_5 : Upper (D 3) (R 3) [34,65,17,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,5,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2923

theorem m6090_9 : Upper (D 3) (R 3) [34,65,17,160,9] 13 :=
  permutation_upper _ _ _ [34,65,9,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2931

theorem m6090_12 : Upper (D 3) (R 3) [34,65,17,160,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2941

theorem m6090_65 : Upper (D 3) (R 3) [34,65,17,160,65] 13 :=
  permutation_upper _ _ _ [34,65,9,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2968

theorem m6090_68 : Upper (D 3) (R 3) [34,65,17,160,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2973

theorem m6090_72 : Upper (D 3) (R 3) [34,65,17,160,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2980

theorem m6090_129 : Upper (D 3) (R 3) [34,65,17,160,129] 13 :=
  permutation_upper _ _ _ [34,65,9,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2993

theorem m6090_132 : Upper (D 3) (R 3) [34,65,17,160,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3003

theorem m6090_136 : Upper (D 3) (R 3) [34,65,17,160,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3016

theorem m6090_192 : Upper (D 3) (R 3) [34,65,17,160,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3034

theorem m6090_257 : Upper (D 3) (R 3) [34,65,17,160,257] 13 :=
  permutation_upper _ _ _ [34,65,9,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3042

theorem m6090_260 : Upper (D 3) (R 3) [34,65,17,160,260] 13 :=
  permutation_upper _ _ _ [34,65,9,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3048

theorem m6090_264 : Upper (D 3) (R 3) [34,65,17,160,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3057

theorem m6090_320 : Upper (D 3) (R 3) [34,65,17,160,320] 13 :=
  permutation_upper _ _ _ [34,65,9,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3066

theorem m6090_384 : Upper (D 3) (R 3) [34,65,17,160,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3074

def r6090 : Route 9 := (fun mask => (mask,id))

def c6090 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6090 : Upper (D 3) (R 3) [34,65,17,160] 13 := by
  apply FastRouting.sound _ _ [34,65,17,160] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192,257,260,264,320,384] r6090 c6090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6090_5
  · exact m6090_9
  · exact m6090_12
  · exact m6090_65
  · exact m6090_68
  · exact m6090_72
  · exact m6090_129
  · exact m6090_132
  · exact m6090_136
  · exact m6090_192
  · exact m6090_257
  · exact m6090_260
  · exact m6090_264
  · exact m6090_320
  · exact m6090_384

theorem m6091_5 : Upper (D 3) (R 3) [34,65,17,192,5] 13 :=
  permutation_upper _ _ _ [34,65,9,5,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2924

theorem m6091_9 : Upper (D 3) (R 3) [34,65,17,192,9] 13 :=
  permutation_upper _ _ _ [34,65,9,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2932

theorem m6091_12 : Upper (D 3) (R 3) [34,65,17,192,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2942

theorem m6091_33 : Upper (D 3) (R 3) [34,65,17,192,33] 13 :=
  permutation_upper _ _ _ [34,65,9,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2949

theorem m6091_36 : Upper (D 3) (R 3) [34,65,17,192,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2954

theorem m6091_40 : Upper (D 3) (R 3) [34,65,17,192,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2961

theorem m6091_129 : Upper (D 3) (R 3) [34,65,17,192,129] 13 :=
  permutation_upper _ _ _ [34,65,9,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2994

theorem m6091_132 : Upper (D 3) (R 3) [34,65,17,192,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3004

theorem m6091_136 : Upper (D 3) (R 3) [34,65,17,192,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3017

theorem m6091_160 : Upper (D 3) (R 3) [34,65,17,192,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3026

theorem m6091_257 : Upper (D 3) (R 3) [34,65,17,192,257] 13 :=
  permutation_upper _ _ _ [34,65,9,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3043

theorem m6091_260 : Upper (D 3) (R 3) [34,65,17,192,260] 13 :=
  permutation_upper _ _ _ [34,65,9,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3049

theorem m6091_264 : Upper (D 3) (R 3) [34,65,17,192,264] 13 :=
  permutation_upper _ _ _ [34,65,9,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3058

theorem m6091_288 : Upper (D 3) (R 3) [34,65,17,192,288] 13 :=
  permutation_upper _ _ _ [34,65,9,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3062

theorem m6091_384 : Upper (D 3) (R 3) [34,65,17,192,384] 13 :=
  permutation_upper _ _ _ [34,65,9,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3075

def r6091 : Route 9 := (fun mask => (mask,id))

def c6091 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6091 : Upper (D 3) (R 3) [34,65,17,192] 13 := by
  apply FastRouting.sound _ _ [34,65,17,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,257,260,264,288,384] r6091 c6091
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6091_5
  · exact m6091_9
  · exact m6091_12
  · exact m6091_33
  · exact m6091_36
  · exact m6091_40
  · exact m6091_129
  · exact m6091_132
  · exact m6091_136
  · exact m6091_160
  · exact m6091_257
  · exact m6091_260
  · exact m6091_264
  · exact m6091_288
  · exact m6091_384

theorem m6092_12 : Upper (D 3) (R 3) [34,65,17,257,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2943

theorem m6092_36 : Upper (D 3) (R 3) [34,65,17,257,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2955

theorem m6092_40 : Upper (D 3) (R 3) [34,65,17,257,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2962

theorem m6092_68 : Upper (D 3) (R 3) [34,65,17,257,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2974

theorem m6092_72 : Upper (D 3) (R 3) [34,65,17,257,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2981

theorem m6092_96 : Upper (D 3) (R 3) [34,65,17,257,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2987

theorem m6092_132 : Upper (D 3) (R 3) [34,65,17,257,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3005

theorem m6092_136 : Upper (D 3) (R 3) [34,65,17,257,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3018

theorem m6092_160 : Upper (D 3) (R 3) [34,65,17,257,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3027

theorem m6092_192 : Upper (D 3) (R 3) [34,65,17,257,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3035

def r6092 : Route 9 := (fun mask => (mask,id))

def c6092 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6092 : Upper (D 3) (R 3) [34,65,17,257] 13 := by
  apply FastRouting.sound _ _ [34,65,17,257] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192] r6092 c6092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6092_12
  · exact m6092_36
  · exact m6092_40
  · exact m6092_68
  · exact m6092_72
  · exact m6092_96
  · exact m6092_132
  · exact m6092_136
  · exact m6092_160
  · exact m6092_192

theorem m6093_9 : Upper (D 3) (R 3) [34,65,17,260,9] 13 :=
  permutation_upper _ _ _ [34,65,9,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2933

theorem m6093_33 : Upper (D 3) (R 3) [34,65,17,260,33] 13 :=
  permutation_upper _ _ _ [34,65,9,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2950

theorem m6093_40 : Upper (D 3) (R 3) [34,65,17,260,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2963

theorem m6093_65 : Upper (D 3) (R 3) [34,65,17,260,65] 13 :=
  permutation_upper _ _ _ [34,65,9,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2969

theorem m6093_72 : Upper (D 3) (R 3) [34,65,17,260,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2982

theorem m6093_96 : Upper (D 3) (R 3) [34,65,17,260,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2988

theorem m6093_129 : Upper (D 3) (R 3) [34,65,17,260,129] 13 :=
  permutation_upper _ _ _ [34,65,9,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2995

theorem m6093_136 : Upper (D 3) (R 3) [34,65,17,260,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3019

theorem m6093_160 : Upper (D 3) (R 3) [34,65,17,260,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3028

theorem m6093_192 : Upper (D 3) (R 3) [34,65,17,260,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3036

def r6093 : Route 9 := (fun mask => (mask,id))

def c6093 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6093 : Upper (D 3) (R 3) [34,65,17,260] 13 := by
  apply FastRouting.sound _ _ [34,65,17,260] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6093 c6093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6093_9
  · exact m6093_33
  · exact m6093_40
  · exact m6093_65
  · exact m6093_72
  · exact m6093_96
  · exact m6093_129
  · exact m6093_136
  · exact m6093_160
  · exact m6093_192

theorem m6094_5 : Upper (D 3) (R 3) [34,65,17,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,5,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2925

theorem m6094_9 : Upper (D 3) (R 3) [34,65,17,288,9] 13 :=
  permutation_upper _ _ _ [34,65,9,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2934

theorem m6094_12 : Upper (D 3) (R 3) [34,65,17,288,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2944

theorem m6094_65 : Upper (D 3) (R 3) [34,65,17,288,65] 13 :=
  permutation_upper _ _ _ [34,65,9,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2970

theorem m6094_68 : Upper (D 3) (R 3) [34,65,17,288,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2975

theorem m6094_72 : Upper (D 3) (R 3) [34,65,17,288,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2983

theorem m6094_129 : Upper (D 3) (R 3) [34,65,17,288,129] 13 :=
  permutation_upper _ _ _ [34,65,9,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2996

theorem m6094_132 : Upper (D 3) (R 3) [34,65,17,288,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3006

theorem m6094_136 : Upper (D 3) (R 3) [34,65,17,288,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3020

theorem m6094_192 : Upper (D 3) (R 3) [34,65,17,288,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3037

def r6094 : Route 9 := (fun mask => (mask,id))

def c6094 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6094 : Upper (D 3) (R 3) [34,65,17,288] 13 := by
  apply FastRouting.sound _ _ [34,65,17,288] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r6094 c6094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6094_5
  · exact m6094_9
  · exact m6094_12
  · exact m6094_65
  · exact m6094_68
  · exact m6094_72
  · exact m6094_129
  · exact m6094_132
  · exact m6094_136
  · exact m6094_192

theorem m6095_5 : Upper (D 3) (R 3) [34,65,17,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,5,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2926

theorem m6095_9 : Upper (D 3) (R 3) [34,65,17,320,9] 13 :=
  permutation_upper _ _ _ [34,65,9,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2935

theorem m6095_12 : Upper (D 3) (R 3) [34,65,17,320,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2945

theorem m6095_33 : Upper (D 3) (R 3) [34,65,17,320,33] 13 :=
  permutation_upper _ _ _ [34,65,9,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2951

theorem m6095_36 : Upper (D 3) (R 3) [34,65,17,320,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2956

theorem m6095_40 : Upper (D 3) (R 3) [34,65,17,320,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2964

theorem m6095_129 : Upper (D 3) (R 3) [34,65,17,320,129] 13 :=
  permutation_upper _ _ _ [34,65,9,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2997

theorem m6095_132 : Upper (D 3) (R 3) [34,65,17,320,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3007

theorem m6095_136 : Upper (D 3) (R 3) [34,65,17,320,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3021

theorem m6095_160 : Upper (D 3) (R 3) [34,65,17,320,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3029

def r6095 : Route 9 := (fun mask => (mask,id))

def c6095 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6095 : Upper (D 3) (R 3) [34,65,17,320] 13 := by
  apply FastRouting.sound _ _ [34,65,17,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r6095 c6095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6095_5
  · exact m6095_9
  · exact m6095_12
  · exact m6095_33
  · exact m6095_36
  · exact m6095_40
  · exact m6095_129
  · exact m6095_132
  · exact m6095_136
  · exact m6095_160

theorem m6096_5 : Upper (D 3) (R 3) [34,65,17,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,5,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2927

theorem m6096_9 : Upper (D 3) (R 3) [34,65,17,384,9] 13 :=
  permutation_upper _ _ _ [34,65,9,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2936

theorem m6096_12 : Upper (D 3) (R 3) [34,65,17,384,12] 13 :=
  permutation_upper _ _ _ [34,65,9,20,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2946

theorem m6096_33 : Upper (D 3) (R 3) [34,65,17,384,33] 13 :=
  permutation_upper _ _ _ [34,65,9,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2952

theorem m6096_36 : Upper (D 3) (R 3) [34,65,17,384,36] 13 :=
  permutation_upper _ _ _ [34,65,9,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2957

theorem m6096_40 : Upper (D 3) (R 3) [34,65,17,384,40] 13 :=
  permutation_upper _ _ _ [34,65,9,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2965

theorem m6096_65 : Upper (D 3) (R 3) [34,65,17,384,65] 13 :=
  permutation_upper _ _ _ [34,65,9,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2971

theorem m6096_68 : Upper (D 3) (R 3) [34,65,17,384,68] 13 :=
  permutation_upper _ _ _ [34,65,9,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2976

theorem m6096_72 : Upper (D 3) (R 3) [34,65,17,384,72] 13 :=
  permutation_upper _ _ _ [34,65,9,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2984

theorem m6096_96 : Upper (D 3) (R 3) [34,65,17,384,96] 13 :=
  permutation_upper _ _ _ [34,65,9,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2989

theorem m6096_129 : Upper (D 3) (R 3) [34,65,17,384,129] 13 :=
  permutation_upper _ _ _ [34,65,9,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2998

theorem m6096_132 : Upper (D 3) (R 3) [34,65,17,384,132] 13 :=
  permutation_upper _ _ _ [34,65,9,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3008

theorem m6096_136 : Upper (D 3) (R 3) [34,65,17,384,136] 13 :=
  permutation_upper _ _ _ [34,65,9,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3022

theorem m6096_160 : Upper (D 3) (R 3) [34,65,17,384,160] 13 :=
  permutation_upper _ _ _ [34,65,9,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3030

theorem m6096_192 : Upper (D 3) (R 3) [34,65,17,384,192] 13 :=
  permutation_upper _ _ _ [34,65,9,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3038

def r6096 : Route 9 := (fun mask => (mask,id))

def c6096 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6096 : Upper (D 3) (R 3) [34,65,17,384] 13 := by
  apply FastRouting.sound _ _ [34,65,17,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r6096 c6096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6096_5
  · exact m6096_9
  · exact m6096_12
  · exact m6096_33
  · exact m6096_36
  · exact m6096_40
  · exact m6096_65
  · exact m6096_68
  · exact m6096_72
  · exact m6096_96
  · exact m6096_129
  · exact m6096_132
  · exact m6096_136
  · exact m6096_160
  · exact m6096_192

def b6097 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 41 469 485 453 453 453), lower := (rows 35 67 28 41 16 32 64 128 256), losses := [] }

theorem u6097 : Upper (D 3) (R 3) [34,65,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6097
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6098 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 44 465 481 449 449 449), lower := (rows 35 67 28 44 16 32 64 128 256), losses := [] }

theorem u6098 : Upper (D 3) (R 3) [34,65,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6098
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6099 : PairBound 9 := { available := 421, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 437 421 485 421 421), lower := (rows 35 67 28 73 16 32 64 128 256), losses := [] }

theorem u6099 : Upper (D 3) (R 3) [34,65,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6099
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6100 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 433 417 481 417 417), lower := (rows 35 67 28 76 16 32 64 128 256), losses := [] }

theorem u6100 : Upper (D 3) (R 3) [34,65,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6100
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6101 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 405 421 453 389 389), lower := (rows 35 67 28 104 16 32 64 128 256), losses := [] }

theorem u6101 : Upper (D 3) (R 3) [34,65,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6101
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6102_5 : Upper (D 3) (R 3) [34,65,24,129,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2940

theorem m6102_33 : Upper (D 3) (R 3) [34,65,24,129,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3076

theorem m6102_36 : Upper (D 3) (R 3) [34,65,24,129,36] 13 :=
  permutation_upper _ _ _ [34,65,24,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3083

theorem m6102_65 : Upper (D 3) (R 3) [34,65,24,129,65] 13 :=
  permutation_upper _ _ _ [34,65,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3088

theorem m6102_68 : Upper (D 3) (R 3) [34,65,24,129,68] 13 :=
  permutation_upper _ _ _ [34,65,24,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3095

theorem m6102_96 : Upper (D 3) (R 3) [34,65,24,129,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3100

def r6102 : Route 9 := (fun mask => (mask,id))

def c6102 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6102 : Upper (D 3) (R 3) [34,65,24,129] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r6102 c6102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6102_5
  · exact m6102_33
  · exact m6102_36
  · exact m6102_65
  · exact m6102_68
  · exact m6102_96
  · exact u3105
  · exact u3106
  · exact u3107
  · exact u3108
  · exact u3109
  · exact u3110
  · exact u3111
  · exact u3112
  · exact u3113

theorem m6103_33 : Upper (D 3) (R 3) [34,65,24,132,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3077

theorem m6103_65 : Upper (D 3) (R 3) [34,65,24,132,65] 13 :=
  permutation_upper _ _ _ [34,65,24,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3089

theorem m6103_96 : Upper (D 3) (R 3) [34,65,24,132,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3101

theorem m6103_129 : Upper (D 3) (R 3) [34,65,24,132,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3106

def r6103 : Route 9 := (fun mask => (mask,id))

def c6103 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6103 : Upper (D 3) (R 3) [34,65,24,132] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r6103 c6103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6103_33
  · exact m6103_65
  · exact m6103_96
  · exact m6103_129
  · exact u3114
  · exact u3115
  · exact u3116
  · exact u3117
  · exact u3118
  · exact u3119

theorem m6104_5 : Upper (D 3) (R 3) [34,65,24,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2941

theorem m6104_65 : Upper (D 3) (R 3) [34,65,24,160,65] 13 :=
  permutation_upper _ _ _ [34,65,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3090

theorem m6104_68 : Upper (D 3) (R 3) [34,65,24,160,68] 13 :=
  permutation_upper _ _ _ [34,65,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3096

theorem m6104_129 : Upper (D 3) (R 3) [34,65,24,160,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3107

theorem m6104_132 : Upper (D 3) (R 3) [34,65,24,160,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3114

def r6104 : Route 9 := (fun mask => (mask,id))

def c6104 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6104 : Upper (D 3) (R 3) [34,65,24,160] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160] 13 (by decide) (choices 2) [5,65,68,129,132,192,257,260,320,384] r6104 c6104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6104_5
  · exact m6104_65
  · exact m6104_68
  · exact m6104_129
  · exact m6104_132
  · exact u3120
  · exact u3121
  · exact u3122
  · exact u3123
  · exact u3124

theorem m6105_5 : Upper (D 3) (R 3) [34,65,24,192,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2942

theorem m6105_33 : Upper (D 3) (R 3) [34,65,24,192,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3078

theorem m6105_36 : Upper (D 3) (R 3) [34,65,24,192,36] 13 :=
  permutation_upper _ _ _ [34,65,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3084

theorem m6105_129 : Upper (D 3) (R 3) [34,65,24,192,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3108

theorem m6105_132 : Upper (D 3) (R 3) [34,65,24,192,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3115

theorem m6105_160 : Upper (D 3) (R 3) [34,65,24,192,160] 13 :=
  permutation_upper _ _ _ [34,65,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3120

def r6105 : Route 9 := (fun mask => (mask,id))

def c6105 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6105 : Upper (D 3) (R 3) [34,65,24,192] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r6105 c6105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6105_5
  · exact m6105_33
  · exact m6105_36
  · exact m6105_129
  · exact m6105_132
  · exact m6105_160
  · exact u3125
  · exact u3126
  · exact u3127
  · exact u3128

theorem m6106_5 : Upper (D 3) (R 3) [34,65,24,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2943

theorem m6106_33 : Upper (D 3) (R 3) [34,65,24,257,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3079

theorem m6106_36 : Upper (D 3) (R 3) [34,65,24,257,36] 13 :=
  permutation_upper _ _ _ [34,65,24,36,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3085

theorem m6106_65 : Upper (D 3) (R 3) [34,65,24,257,65] 13 :=
  permutation_upper _ _ _ [34,65,24,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3091

theorem m6106_68 : Upper (D 3) (R 3) [34,65,24,257,68] 13 :=
  permutation_upper _ _ _ [34,65,24,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3097

theorem m6106_96 : Upper (D 3) (R 3) [34,65,24,257,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3102

theorem m6106_129 : Upper (D 3) (R 3) [34,65,24,257,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3109

theorem m6106_132 : Upper (D 3) (R 3) [34,65,24,257,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3116

theorem m6106_160 : Upper (D 3) (R 3) [34,65,24,257,160] 13 :=
  permutation_upper _ _ _ [34,65,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3121

theorem m6106_192 : Upper (D 3) (R 3) [34,65,24,257,192] 13 :=
  permutation_upper _ _ _ [34,65,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3125

def r6106 : Route 9 := (fun mask => (mask,id))

def c6106 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6106 : Upper (D 3) (R 3) [34,65,24,257] 13 := by
  apply FastRouting.sound _ _ [34,65,24,257] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r6106 c6106
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6106_5
  · exact m6106_33
  · exact m6106_36
  · exact m6106_65
  · exact m6106_68
  · exact m6106_96
  · exact m6106_129
  · exact m6106_132
  · exact m6106_160
  · exact m6106_192

theorem m6107_33 : Upper (D 3) (R 3) [34,65,24,260,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3080

theorem m6107_65 : Upper (D 3) (R 3) [34,65,24,260,65] 13 :=
  permutation_upper _ _ _ [34,65,24,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3092

theorem m6107_96 : Upper (D 3) (R 3) [34,65,24,260,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3103

theorem m6107_129 : Upper (D 3) (R 3) [34,65,24,260,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3110

theorem m6107_160 : Upper (D 3) (R 3) [34,65,24,260,160] 13 :=
  permutation_upper _ _ _ [34,65,24,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3122

theorem m6107_192 : Upper (D 3) (R 3) [34,65,24,260,192] 13 :=
  permutation_upper _ _ _ [34,65,24,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3126

def r6107 : Route 9 := (fun mask => (mask,id))

def c6107 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6107 : Upper (D 3) (R 3) [34,65,24,260] 13 := by
  apply FastRouting.sound _ _ [34,65,24,260] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6107 c6107
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6107_33
  · exact m6107_65
  · exact m6107_96
  · exact m6107_129
  · exact m6107_160
  · exact m6107_192

theorem m6108_5 : Upper (D 3) (R 3) [34,65,24,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2944

theorem m6108_65 : Upper (D 3) (R 3) [34,65,24,288,65] 13 :=
  permutation_upper _ _ _ [34,65,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3093

theorem m6108_68 : Upper (D 3) (R 3) [34,65,24,288,68] 13 :=
  permutation_upper _ _ _ [34,65,24,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3098

theorem m6108_129 : Upper (D 3) (R 3) [34,65,24,288,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3111

theorem m6108_132 : Upper (D 3) (R 3) [34,65,24,288,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3117

theorem m6108_192 : Upper (D 3) (R 3) [34,65,24,288,192] 13 :=
  permutation_upper _ _ _ [34,65,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3127

def r6108 : Route 9 := (fun mask => (mask,id))

def c6108 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6108 : Upper (D 3) (R 3) [34,65,24,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,288] 13 (by decide) (choices 2) [5,65,68,129,132,192] r6108 c6108
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6108_5
  · exact m6108_65
  · exact m6108_68
  · exact m6108_129
  · exact m6108_132
  · exact m6108_192

theorem m6109_5 : Upper (D 3) (R 3) [34,65,24,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2945

theorem m6109_33 : Upper (D 3) (R 3) [34,65,24,320,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3081

theorem m6109_36 : Upper (D 3) (R 3) [34,65,24,320,36] 13 :=
  permutation_upper _ _ _ [34,65,24,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3086

theorem m6109_129 : Upper (D 3) (R 3) [34,65,24,320,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3112

theorem m6109_132 : Upper (D 3) (R 3) [34,65,24,320,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3118

theorem m6109_160 : Upper (D 3) (R 3) [34,65,24,320,160] 13 :=
  permutation_upper _ _ _ [34,65,24,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3123

def r6109 : Route 9 := (fun mask => (mask,id))

def c6109 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6109 : Upper (D 3) (R 3) [34,65,24,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,320] 13 (by decide) (choices 2) [5,33,36,129,132,160] r6109 c6109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6109_5
  · exact m6109_33
  · exact m6109_36
  · exact m6109_129
  · exact m6109_132
  · exact m6109_160

theorem m6110_5 : Upper (D 3) (R 3) [34,65,24,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2946

theorem m6110_33 : Upper (D 3) (R 3) [34,65,24,384,33] 13 :=
  permutation_upper _ _ _ [34,65,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3082

theorem m6110_36 : Upper (D 3) (R 3) [34,65,24,384,36] 13 :=
  permutation_upper _ _ _ [34,65,24,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3087

theorem m6110_65 : Upper (D 3) (R 3) [34,65,24,384,65] 13 :=
  permutation_upper _ _ _ [34,65,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3094

theorem m6110_68 : Upper (D 3) (R 3) [34,65,24,384,68] 13 :=
  permutation_upper _ _ _ [34,65,24,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3099

theorem m6110_96 : Upper (D 3) (R 3) [34,65,24,384,96] 13 :=
  permutation_upper _ _ _ [34,65,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3104

theorem m6110_129 : Upper (D 3) (R 3) [34,65,24,384,129] 13 :=
  permutation_upper _ _ _ [34,65,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3113

theorem m6110_132 : Upper (D 3) (R 3) [34,65,24,384,132] 13 :=
  permutation_upper _ _ _ [34,65,24,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3119

theorem m6110_160 : Upper (D 3) (R 3) [34,65,24,384,160] 13 :=
  permutation_upper _ _ _ [34,65,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3124

theorem m6110_192 : Upper (D 3) (R 3) [34,65,24,384,192] 13 :=
  permutation_upper _ _ _ [34,65,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3128

def r6110 : Route 9 := (fun mask => (mask,id))

def c6110 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6110 : Upper (D 3) (R 3) [34,65,24,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,384] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r6110 c6110
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6110_5
  · exact m6110_33
  · exact m6110_36
  · exact m6110_65
  · exact m6110_68
  · exact m6110_96
  · exact m6110_129
  · exact m6110_132
  · exact m6110_160
  · exact m6110_192

def b6111 : PairBound 9 := { available := 409, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 76 409 441 473 409 409), lower := (rows 35 67 37 76 16 32 64 128 256), losses := [] }

theorem u6111 : Upper (D 3) (R 3) [34,65,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6111
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6112 : PairBound 9 := { available := 476, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 137 476 508 476 476 476), lower := (rows 35 67 37 137 16 32 64 128 256), losses := [] }

theorem u6112 : Upper (D 3) (R 3) [34,65,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6112
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6113 : PairBound 9 := { available := 473, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 140 473 505 473 473 473), lower := (rows 35 67 37 140 16 32 64 128 256), losses := [] }

theorem u6113 : Upper (D 3) (R 3) [34,65,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6113
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6114 : PairBound 9 := { available := 413, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 200 413 445 477 413 413), lower := (rows 35 67 37 200 16 32 64 128 256), losses := [] }

theorem u6114 : Upper (D 3) (R 3) [34,65,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6114
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6115 : PairBound 9 := { available := 220, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 265 220 252 220 220 476), lower := (rows 35 67 37 265 16 32 64 128 256), losses := [] }

theorem u6115 : Upper (D 3) (R 3) [34,65,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6115
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6116 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 268 217 249 217 217 473), lower := (rows 35 67 37 268 16 32 64 128 256), losses := [] }

theorem u6116 : Upper (D 3) (R 3) [34,65,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6116
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6117 : PairBound 9 := { available := 157, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 328 157 189 221 157 413), lower := (rows 35 67 37 328 16 32 64 128 256), losses := [] }

theorem u6117 : Upper (D 3) (R 3) [34,65,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6117
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6118 : PairBound 9 := { available := 221, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 37 392 221 253 221 221 477), lower := (rows 35 67 37 392 16 32 64 128 256), losses := [] }

theorem u6118 : Upper (D 3) (R 3) [34,65,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6118
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6119 : PairBound 9 := { available := 405, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 405 437 469 405 405), lower := (rows 35 67 44 73 16 32 64 128 256), losses := [] }

theorem u6119 : Upper (D 3) (R 3) [34,65,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6119
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u6119
end Delivery.IrregularNine14.P03
