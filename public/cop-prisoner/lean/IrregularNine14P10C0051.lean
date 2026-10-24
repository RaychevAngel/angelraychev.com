import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0020
import IrregularNine14P10C0021
import IrregularNine14P10C0022
import IrregularNine14P10C0023
import IrregularNine14P10C0030
import IrregularNine14P10C0031
import IrregularNine14P10C0032
import IrregularNine14P10C0033
import IrregularNine14P10C0034
import IrregularNine14P10C0035
import IrregularNine14P10C0036
import IrregularNine14P10C0037

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3060 : PairBound 9 := { available := 409, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 168 409 441 473 409 409), lower := (rows 35 70 100 168 16 32 64 128 256), losses := [] }

theorem u3060 : Upper (D 10) (R 10) [34,68,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3060 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3061 : PairBound 9 := { available := 441, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 392 441 441 505 441 441), lower := (rows 35 70 100 392 16 32 64 128 256), losses := [] }

theorem u3061 : Upper (D 10) (R 10) [34,68,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3061 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3062_40 : Upper (D 10) (R 10) [34,68,129,48,40] 13 :=
  permutation_upper _ _ _ [34,33,40,80,132] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1844

theorem m3062_72 : Upper (D 10) (R 10) [34,68,129,48,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,132] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1934

theorem m3062_136 : Upper (D 10) (R 10) [34,68,129,48,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,68] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1943

theorem m3062_264 : Upper (D 10) (R 10) [34,68,129,48,264] 13 :=
  permutation_upper _ _ _ [34,65,40,144,260] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1948

def r3062 : Route 9 := (fun mask => (mask,id))

def c3062 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3062 : Upper (D 10) (R 10) [34,68,129,48] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r3062 c3062
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3062_40
  · exact m3062_72
  · exact u2070
  · exact m3062_136
  · exact u2071
  · exact u2072
  · exact m3062_264
  · exact u2073
  · exact u2074
  · exact u2075

theorem m3063_40 : Upper (D 10) (R 10) [34,68,129,80,40] 13 :=
  permutation_upper _ _ _ [34,65,40,80,132] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1934

def r3063 : Route 9 := (fun mask => (mask,id))

def c3063 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3063 : Upper (D 10) (R 10) [34,68,129,80] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80] 13 (by decide) (choices 2) [40,136,160,264,288,384] r3063 c3063
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3063_40
  · exact u2076
  · exact u2077
  · exact u2078
  · exact u2079
  · exact u2080

theorem m3064_40 : Upper (D 10) (R 10) [34,68,129,96,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2070

def r3064 : Route 9 := (fun mask => (mask,id))

def c3064 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3064 : Upper (D 10) (R 10) [34,68,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96] 13 (by decide) (choices 2) [40,136,160,264,288,384] r3064 c3064
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3064_40
  · exact u2081
  · exact u2082
  · exact u2083
  · exact u2084
  · exact u2085

theorem m3065_40 : Upper (D 10) (R 10) [34,68,129,144,40] 13 :=
  permutation_upper _ _ _ [34,65,40,144,68] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1943

theorem m3065_72 : Upper (D 10) (R 10) [34,68,129,144,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2076

theorem m3065_96 : Upper (D 10) (R 10) [34,68,129,144,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2081

def r3065 : Route 9 := (fun mask => (mask,id))

def c3065 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3065 : Upper (D 10) (R 10) [34,68,129,144] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144] 13 (by decide) (choices 2) [40,72,96,264,288,320] r3065 c3065
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3065_40
  · exact m3065_72
  · exact m3065_96
  · exact u2086
  · exact u2087
  · exact u2088

theorem m3066_40 : Upper (D 10) (R 10) [34,68,129,160,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2071

theorem m3066_72 : Upper (D 10) (R 10) [34,68,129,160,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2077

theorem m3066_96 : Upper (D 10) (R 10) [34,68,129,160,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2082

def r3066 : Route 9 := (fun mask => (mask,id))

def c3066 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3066 : Upper (D 10) (R 10) [34,68,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160] 13 (by decide) (choices 2) [40,72,96,264,288,320] r3066 c3066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3066_40
  · exact m3066_72
  · exact m3066_96
  · exact u2089
  · exact u2090
  · exact u2091

def b3067 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 304, targets := 64 },{ cop := 3, region := 304, targets := 128 }], pairs := [(4,6),(4,7)], upper := (rows 35 70 133 200 312 312 376 440 312), lower := (rows 35 70 133 200 16 32 64 128 256), losses := [] }

theorem u3067 : Upper (D 10) (R 10) [34,68,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3067 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3068_40 : Upper (D 10) (R 10) [34,68,129,272,40] 13 :=
  permutation_upper _ _ _ [34,65,40,144,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1948

theorem m3068_72 : Upper (D 10) (R 10) [34,68,129,272,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2078

theorem m3068_96 : Upper (D 10) (R 10) [34,68,129,272,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2083

theorem m3068_136 : Upper (D 10) (R 10) [34,68,129,272,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2086

theorem m3068_160 : Upper (D 10) (R 10) [34,68,129,272,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2089

theorem m3068_192 : Upper (D 10) (R 10) [34,68,129,272,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2092

def r3068 : Route 9 := (fun mask => (mask,id))

def c3068 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3068 : Upper (D 10) (R 10) [34,68,129,272] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r3068 c3068
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3068_40
  · exact m3068_72
  · exact m3068_96
  · exact m3068_136
  · exact m3068_160
  · exact m3068_192
  · exact u2094
  · exact u2095
  · exact u2096
  · exact u2097

theorem m3069_40 : Upper (D 10) (R 10) [34,68,129,288,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2073

theorem m3069_72 : Upper (D 10) (R 10) [34,68,129,288,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2079

theorem m3069_96 : Upper (D 10) (R 10) [34,68,129,288,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2084

theorem m3069_136 : Upper (D 10) (R 10) [34,68,129,288,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2087

theorem m3069_160 : Upper (D 10) (R 10) [34,68,129,288,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2090

theorem m3069_192 : Upper (D 10) (R 10) [34,68,129,288,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2093

theorem m3069_264 : Upper (D 10) (R 10) [34,68,129,288,264] 13 :=
  permutation_upper _ _ _ [34,68,129,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2095

def r3069 : Route 9 := (fun mask => (mask,id))

def c3069 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3069 : Upper (D 10) (R 10) [34,68,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r3069 c3069
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3069_40
  · exact m3069_72
  · exact m3069_96
  · exact m3069_136
  · exact m3069_160
  · exact m3069_192
  · exact m3069_264
  · exact u2098
  · exact u2099
  · exact u2100

theorem m3070_40 : Upper (D 10) (R 10) [34,68,129,320,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2074

theorem m3070_136 : Upper (D 10) (R 10) [34,68,129,320,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2088

theorem m3070_160 : Upper (D 10) (R 10) [34,68,129,320,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2091

theorem m3070_264 : Upper (D 10) (R 10) [34,68,129,320,264] 13 :=
  permutation_upper _ _ _ [34,68,129,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2096

theorem m3070_288 : Upper (D 10) (R 10) [34,68,129,320,288] 13 :=
  permutation_upper _ _ _ [34,68,129,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2099

def r3070 : Route 9 := (fun mask => (mask,id))

def c3070 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3070 : Upper (D 10) (R 10) [34,68,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,320] 13 (by decide) (choices 2) [40,136,160,264,288,384] r3070 c3070
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3070_40
  · exact m3070_136
  · exact m3070_160
  · exact m3070_264
  · exact m3070_288
  · exact u2101

theorem m3071_40 : Upper (D 10) (R 10) [34,68,129,384,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2075

theorem m3071_72 : Upper (D 10) (R 10) [34,68,129,384,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2080

theorem m3071_96 : Upper (D 10) (R 10) [34,68,129,384,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2085

theorem m3071_264 : Upper (D 10) (R 10) [34,68,129,384,264] 13 :=
  permutation_upper _ _ _ [34,68,129,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2097

theorem m3071_288 : Upper (D 10) (R 10) [34,68,129,384,288] 13 :=
  permutation_upper _ _ _ [34,68,129,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2100

theorem m3071_320 : Upper (D 10) (R 10) [34,68,129,384,320] 13 :=
  permutation_upper _ _ _ [34,68,129,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2101

def r3071 : Route 9 := (fun mask => (mask,id))

def c3071 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3071 : Upper (D 10) (R 10) [34,68,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,384] 13 (by decide) (choices 2) [40,72,96,264,288,320] r3071 c3071
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3071_40
  · exact m3071_72
  · exact m3071_96
  · exact m3071_264
  · exact m3071_288
  · exact m3071_320

theorem m3072_33 : Upper (D 10) (R 10) [34,68,136,48,33] 13 :=
  permutation_upper _ _ _ [34,36,40,80,129] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1861

theorem m3072_65 : Upper (D 10) (R 10) [34,68,136,48,65] 13 :=
  permutation_upper _ _ _ [34,68,40,80,129] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2011

theorem m3072_129 : Upper (D 10) (R 10) [34,68,136,48,129] 13 :=
  permutation_upper _ _ _ [34,68,40,144,65] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2020

theorem m3072_257 : Upper (D 10) (R 10) [34,68,136,48,257] 13 :=
  permutation_upper _ _ _ [34,68,40,144,257] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2025

def r3072 : Route 9 := (fun mask => (mask,id))

def c3072 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3072 : Upper (D 10) (R 10) [34,68,136,48] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r3072 c3072
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3072_33
  · exact m3072_65
  · exact u2102
  · exact m3072_129
  · exact u2103
  · exact u2104
  · exact m3072_257
  · exact u2105
  · exact u2106
  · exact u2107

def b3073 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 73 432 432 496 432 432), lower := (rows 35 70 140 73 16 32 64 128 256), losses := [] }

theorem u3073 : Upper (D 10) (R 10) [34,68,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3073 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3074 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 88 433 417 481 417 417), lower := (rows 35 70 140 88 16 32 64 128 256), losses := [] }

theorem u3074 : Upper (D 10) (R 10) [34,68,136,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3074 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3075 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 104 433 433 497 433 433), lower := (rows 35 70 140 104 16 32 64 128 256), losses := [] }

theorem u3075 : Upper (D 10) (R 10) [34,68,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3075 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3076 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 137 368 368 368 496 368), lower := (rows 35 70 140 137 16 32 64 128 256), losses := [] }

theorem u3076 : Upper (D 10) (R 10) [34,68,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3076 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3077 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 152 369 353 353 481 353), lower := (rows 35 70 140 152 16 32 64 128 256), losses := [] }

theorem u3077 : Upper (D 10) (R 10) [34,68,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3077 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3078 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 168 369 369 369 497 369), lower := (rows 35 70 140 168 16 32 64 128 256), losses := [] }

theorem u3078 : Upper (D 10) (R 10) [34,68,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3078 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3079 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 6, targets := 288 }], pairs := [(1,5),(1,8)], upper := (rows 35 70 140 200 305 305 369 433 305), lower := (rows 35 70 140 200 16 32 64 128 256), losses := [] }

theorem u3079 : Upper (D 10) (R 10) [34,68,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3079 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r3080 : Route 9 := (fun mask => (mask,id))

def c3080 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3080 : Upper (D 10) (R 10) [34,68,136,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257] 13 (by decide) (choices 2) [96,160,192,288,320,384] r3080 c3080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2134
  · exact u2135
  · exact u2136
  · exact u2137
  · exact u2138
  · exact u2139

theorem m3081_33 : Upper (D 10) (R 10) [34,68,136,272,33] 13 :=
  permutation_upper _ _ _ [34,36,72,144,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1888

def r3081 : Route 9 := (fun mask => (mask,id))

def c3081 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3081 : Upper (D 10) (R 10) [34,68,136,272] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r3081 c3081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3081_33
  · exact u2140
  · exact u2141
  · exact u2142
  · exact u2143
  · exact u2144
  · exact u2145
  · exact u2146
  · exact u2147
  · exact u2148

theorem m3082_33 : Upper (D 10) (R 10) [34,68,136,288,33] 13 :=
  permutation_upper _ _ _ [34,36,72,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1889

def r3082 : Route 9 := (fun mask => (mask,id))

def c3082 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3082 : Upper (D 10) (R 10) [34,68,136,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r3082 c3082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3082_33
  · exact u2149
  · exact u2150
  · exact u2151
  · exact u2152
  · exact u2153
  · exact u2154
  · exact u2155
  · exact u2156
  · exact u2157

def b3083 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 328 433 433 497 433 433), lower := (rows 35 70 140 328 16 32 64 128 256), losses := [] }

theorem u3083 : Upper (D 10) (R 10) [34,68,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3083 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3084 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 392 369 369 369 497 369), lower := (rows 35 70 140 392 16 32 64 128 256), losses := [] }

theorem u3084 : Upper (D 10) (R 10) [34,68,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3084 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3085_9 : Upper (D 10) (R 10) [34,68,144,96,9] 13 :=
  permutation_upper _ _ _ [6,40,96,80,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1353

theorem m3085_33 : Upper (D 10) (R 10) [34,68,144,96,33] 13 :=
  permutation_upper _ _ _ [34,36,72,129,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1882

theorem m3085_40 : Upper (D 10) (R 10) [34,68,144,96,40] 13 :=
  permutation_upper _ _ _ [34,68,136,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2102

theorem m3085_129 : Upper (D 10) (R 10) [34,68,144,96,129] 13 :=
  permutation_upper _ _ _ [34,68,136,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2121

theorem m3085_136 : Upper (D 10) (R 10) [34,68,144,96,136] 13 :=
  permutation_upper _ _ _ [34,68,136,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2124

theorem m3085_160 : Upper (D 10) (R 10) [34,68,144,96,160] 13 :=
  permutation_upper _ _ _ [34,68,136,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2128

theorem m3085_257 : Upper (D 10) (R 10) [34,68,144,96,257] 13 :=
  permutation_upper _ _ _ [34,68,136,257,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2134

theorem m3085_264 : Upper (D 10) (R 10) [34,68,144,96,264] 13 :=
  permutation_upper _ _ _ [34,68,136,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2141

theorem m3085_288 : Upper (D 10) (R 10) [34,68,144,96,288] 13 :=
  permutation_upper _ _ _ [34,68,136,288,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2150

theorem m3085_384 : Upper (D 10) (R 10) [34,68,144,96,384] 13 :=
  permutation_upper _ _ _ [34,68,136,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2163

def r3085 : Route 9 := (fun mask => (mask,id))

def c3085 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3085 : Upper (D 10) (R 10) [34,68,144,96] 13 := by
  apply FastRouting.sound _ _ [34,68,144,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3085 c3085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3085_9
  · exact m3085_33
  · exact m3085_40
  · exact m3085_129
  · exact m3085_136
  · exact m3085_160
  · exact m3085_257
  · exact m3085_264
  · exact m3085_288
  · exact m3085_384

theorem m3086_40 : Upper (D 10) (R 10) [34,68,144,129,40] 13 :=
  permutation_upper _ _ _ [34,68,40,144,65] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2020

theorem m3086_72 : Upper (D 10) (R 10) [34,68,144,129,72] 13 :=
  permutation_upper _ _ _ [34,68,136,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2111

theorem m3086_96 : Upper (D 10) (R 10) [34,68,144,129,96] 13 :=
  permutation_upper _ _ _ [34,68,136,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2116

theorem m3086_264 : Upper (D 10) (R 10) [34,68,144,129,264] 13 :=
  permutation_upper _ _ _ [34,68,136,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2142

theorem m3086_288 : Upper (D 10) (R 10) [34,68,144,129,288] 13 :=
  permutation_upper _ _ _ [34,68,136,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2151

theorem m3086_320 : Upper (D 10) (R 10) [34,68,144,129,320] 13 :=
  permutation_upper _ _ _ [34,68,136,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2158

def r3086 : Route 9 := (fun mask => (mask,id))

def c3086 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3086 : Upper (D 10) (R 10) [34,68,144,129] 13 := by
  apply FastRouting.sound _ _ [34,68,144,129] 13 (by decide) (choices 2) [40,72,96,264,288,320] r3086 c3086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3086_40
  · exact m3086_72
  · exact m3086_96
  · exact m3086_264
  · exact m3086_288
  · exact m3086_320

theorem m3087_9 : Upper (D 10) (R 10) [34,68,144,160,9] 13 :=
  permutation_upper _ _ _ [6,40,96,144,65] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1365

theorem m3087_33 : Upper (D 10) (R 10) [34,68,144,160,33] 13 :=
  permutation_upper _ _ _ [34,36,72,129,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1883

theorem m3087_40 : Upper (D 10) (R 10) [34,68,144,160,40] 13 :=
  permutation_upper _ _ _ [34,68,136,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2103

theorem m3087_65 : Upper (D 10) (R 10) [34,68,144,160,65] 13 :=
  permutation_upper _ _ _ [34,68,136,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2108

theorem m3087_72 : Upper (D 10) (R 10) [34,68,144,160,72] 13 :=
  permutation_upper _ _ _ [34,68,136,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2112

theorem m3087_96 : Upper (D 10) (R 10) [34,68,144,160,96] 13 :=
  permutation_upper _ _ _ [34,68,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2117

theorem m3087_257 : Upper (D 10) (R 10) [34,68,144,160,257] 13 :=
  permutation_upper _ _ _ [34,68,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2135

theorem m3087_264 : Upper (D 10) (R 10) [34,68,144,160,264] 13 :=
  permutation_upper _ _ _ [34,68,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2143

theorem m3087_288 : Upper (D 10) (R 10) [34,68,144,160,288] 13 :=
  permutation_upper _ _ _ [34,68,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2152

theorem m3087_320 : Upper (D 10) (R 10) [34,68,144,160,320] 13 :=
  permutation_upper _ _ _ [34,68,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2159

def r3087 : Route 9 := (fun mask => (mask,id))

def c3087 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3087 : Upper (D 10) (R 10) [34,68,144,160] 13 := by
  apply FastRouting.sound _ _ [34,68,144,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3087 c3087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3087_9
  · exact m3087_33
  · exact m3087_40
  · exact m3087_65
  · exact m3087_72
  · exact m3087_96
  · exact m3087_257
  · exact m3087_264
  · exact m3087_288
  · exact m3087_320

theorem m3088_9 : Upper (D 10) (R 10) [34,68,144,192,9] 13 :=
  permutation_upper _ _ _ [6,40,192,80,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1404

theorem m3088_33 : Upper (D 10) (R 10) [34,68,144,192,33] 13 :=
  permutation_upper _ _ _ [34,36,72,129,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1884

theorem m3088_40 : Upper (D 10) (R 10) [34,68,144,192,40] 13 :=
  permutation_upper _ _ _ [34,68,136,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2104

theorem m3088_257 : Upper (D 10) (R 10) [34,68,144,192,257] 13 :=
  permutation_upper _ _ _ [34,68,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2136

theorem m3088_264 : Upper (D 10) (R 10) [34,68,144,192,264] 13 :=
  permutation_upper _ _ _ [34,68,136,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2144

theorem m3088_288 : Upper (D 10) (R 10) [34,68,144,192,288] 13 :=
  permutation_upper _ _ _ [34,68,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2153

def r3088 : Route 9 := (fun mask => (mask,id))

def c3088 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3088 : Upper (D 10) (R 10) [34,68,144,192] 13 := by
  apply FastRouting.sound _ _ [34,68,144,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r3088 c3088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3088_9
  · exact m3088_33
  · exact m3088_40
  · exact m3088_257
  · exact m3088_264
  · exact m3088_288

theorem m3089_40 : Upper (D 10) (R 10) [34,68,144,257,40] 13 :=
  permutation_upper _ _ _ [34,68,40,144,257] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2025

theorem m3089_72 : Upper (D 10) (R 10) [34,68,144,257,72] 13 :=
  permutation_upper _ _ _ [34,68,136,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2113

theorem m3089_96 : Upper (D 10) (R 10) [34,68,144,257,96] 13 :=
  permutation_upper _ _ _ [34,68,136,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2118

theorem m3089_136 : Upper (D 10) (R 10) [34,68,144,257,136] 13 :=
  permutation_upper _ _ _ [34,68,136,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2125

theorem m3089_160 : Upper (D 10) (R 10) [34,68,144,257,160] 13 :=
  permutation_upper _ _ _ [34,68,136,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2129

theorem m3089_192 : Upper (D 10) (R 10) [34,68,144,257,192] 13 :=
  permutation_upper _ _ _ [34,68,136,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2132

theorem m3089_264 : Upper (D 10) (R 10) [34,68,144,257,264] 13 :=
  permutation_upper _ _ _ [34,68,136,272,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2145

theorem m3089_288 : Upper (D 10) (R 10) [34,68,144,257,288] 13 :=
  permutation_upper _ _ _ [34,68,136,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2154

theorem m3089_320 : Upper (D 10) (R 10) [34,68,144,257,320] 13 :=
  permutation_upper _ _ _ [34,68,136,320,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2160

theorem m3089_384 : Upper (D 10) (R 10) [34,68,144,257,384] 13 :=
  permutation_upper _ _ _ [34,68,136,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2164

def r3089 : Route 9 := (fun mask => (mask,id))

def c3089 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3089 : Upper (D 10) (R 10) [34,68,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,144,257] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r3089 c3089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3089_40
  · exact m3089_72
  · exact m3089_96
  · exact m3089_136
  · exact m3089_160
  · exact m3089_192
  · exact m3089_264
  · exact m3089_288
  · exact m3089_320
  · exact m3089_384

theorem m3090_9 : Upper (D 10) (R 10) [34,68,144,288,9] 13 :=
  permutation_upper _ _ _ [6,40,96,144,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1370

theorem m3090_33 : Upper (D 10) (R 10) [34,68,144,288,33] 13 :=
  permutation_upper _ _ _ [34,36,72,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1885

theorem m3090_40 : Upper (D 10) (R 10) [34,68,144,288,40] 13 :=
  permutation_upper _ _ _ [34,68,136,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2105

theorem m3090_65 : Upper (D 10) (R 10) [34,68,144,288,65] 13 :=
  permutation_upper _ _ _ [34,68,136,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2109

theorem m3090_72 : Upper (D 10) (R 10) [34,68,144,288,72] 13 :=
  permutation_upper _ _ _ [34,68,136,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2114

theorem m3090_96 : Upper (D 10) (R 10) [34,68,144,288,96] 13 :=
  permutation_upper _ _ _ [34,68,136,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2119

theorem m3090_129 : Upper (D 10) (R 10) [34,68,144,288,129] 13 :=
  permutation_upper _ _ _ [34,68,136,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2122

theorem m3090_136 : Upper (D 10) (R 10) [34,68,144,288,136] 13 :=
  permutation_upper _ _ _ [34,68,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2126

theorem m3090_160 : Upper (D 10) (R 10) [34,68,144,288,160] 13 :=
  permutation_upper _ _ _ [34,68,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2130

theorem m3090_192 : Upper (D 10) (R 10) [34,68,144,288,192] 13 :=
  permutation_upper _ _ _ [34,68,136,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2133

theorem m3090_257 : Upper (D 10) (R 10) [34,68,144,288,257] 13 :=
  permutation_upper _ _ _ [34,68,136,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2137

theorem m3090_264 : Upper (D 10) (R 10) [34,68,144,288,264] 13 :=
  permutation_upper _ _ _ [34,68,136,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2146

theorem m3090_288 : Upper (D 10) (R 10) [34,68,144,288,288] 13 :=
  permutation_upper _ _ _ [34,68,136,288,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2155

theorem m3090_320 : Upper (D 10) (R 10) [34,68,144,288,320] 13 :=
  permutation_upper _ _ _ [34,68,136,320,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2161

theorem m3090_384 : Upper (D 10) (R 10) [34,68,144,288,384] 13 :=
  permutation_upper _ _ _ [34,68,136,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2165

def r3090 : Route 9 := (fun mask => (mask,id))

def c3090 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3090 : Upper (D 10) (R 10) [34,68,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,144,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r3090 c3090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3090_9
  · exact m3090_33
  · exact m3090_40
  · exact m3090_65
  · exact m3090_72
  · exact m3090_96
  · exact m3090_129
  · exact m3090_136
  · exact m3090_160
  · exact m3090_192
  · exact m3090_257
  · exact m3090_264
  · exact m3090_288
  · exact m3090_320
  · exact m3090_384

theorem m3091_9 : Upper (D 10) (R 10) [34,68,144,320,9] 13 :=
  permutation_upper _ _ _ [6,40,192,80,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1406

theorem m3091_33 : Upper (D 10) (R 10) [34,68,144,320,33] 13 :=
  permutation_upper _ _ _ [34,36,72,129,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1886

theorem m3091_40 : Upper (D 10) (R 10) [34,68,144,320,40] 13 :=
  permutation_upper _ _ _ [34,68,136,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2106

theorem m3091_129 : Upper (D 10) (R 10) [34,68,144,320,129] 13 :=
  permutation_upper _ _ _ [34,68,136,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2123

theorem m3091_136 : Upper (D 10) (R 10) [34,68,144,320,136] 13 :=
  permutation_upper _ _ _ [34,68,136,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2127

theorem m3091_160 : Upper (D 10) (R 10) [34,68,144,320,160] 13 :=
  permutation_upper _ _ _ [34,68,136,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2131

theorem m3091_257 : Upper (D 10) (R 10) [34,68,144,320,257] 13 :=
  permutation_upper _ _ _ [34,68,136,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2138

theorem m3091_264 : Upper (D 10) (R 10) [34,68,144,320,264] 13 :=
  permutation_upper _ _ _ [34,68,136,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2147

theorem m3091_288 : Upper (D 10) (R 10) [34,68,144,320,288] 13 :=
  permutation_upper _ _ _ [34,68,136,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2156

theorem m3091_384 : Upper (D 10) (R 10) [34,68,144,320,384] 13 :=
  permutation_upper _ _ _ [34,68,136,384,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2166

def r3091 : Route 9 := (fun mask => (mask,id))

def c3091 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3091 : Upper (D 10) (R 10) [34,68,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,144,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3091 c3091
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3091_9
  · exact m3091_33
  · exact m3091_40
  · exact m3091_129
  · exact m3091_136
  · exact m3091_160
  · exact m3091_257
  · exact m3091_264
  · exact m3091_288
  · exact m3091_384

theorem m3092_9 : Upper (D 10) (R 10) [34,68,144,384,9] 13 :=
  permutation_upper _ _ _ [6,40,192,272,65] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1422

theorem m3092_33 : Upper (D 10) (R 10) [34,68,144,384,33] 13 :=
  permutation_upper _ _ _ [34,36,72,129,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1887

theorem m3092_40 : Upper (D 10) (R 10) [34,68,144,384,40] 13 :=
  permutation_upper _ _ _ [34,68,136,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2107

theorem m3092_65 : Upper (D 10) (R 10) [34,68,144,384,65] 13 :=
  permutation_upper _ _ _ [34,68,136,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2110

theorem m3092_72 : Upper (D 10) (R 10) [34,68,144,384,72] 13 :=
  permutation_upper _ _ _ [34,68,136,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2115

theorem m3092_96 : Upper (D 10) (R 10) [34,68,144,384,96] 13 :=
  permutation_upper _ _ _ [34,68,136,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2120

theorem m3092_257 : Upper (D 10) (R 10) [34,68,144,384,257] 13 :=
  permutation_upper _ _ _ [34,68,136,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2139

theorem m3092_264 : Upper (D 10) (R 10) [34,68,144,384,264] 13 :=
  permutation_upper _ _ _ [34,68,136,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2148

theorem m3092_288 : Upper (D 10) (R 10) [34,68,144,384,288] 13 :=
  permutation_upper _ _ _ [34,68,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2157

theorem m3092_320 : Upper (D 10) (R 10) [34,68,144,384,320] 13 :=
  permutation_upper _ _ _ [34,68,136,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2162

def r3092 : Route 9 := (fun mask => (mask,id))

def c3092 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3092 : Upper (D 10) (R 10) [34,68,144,384] 13 := by
  apply FastRouting.sound _ _ [34,68,144,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3092 c3092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3092_9
  · exact m3092_33
  · exact m3092_40
  · exact m3092_65
  · exact m3092_72
  · exact m3092_96
  · exact m3092_257
  · exact m3092_264
  · exact m3092_288
  · exact m3092_320

theorem m3093_9 : Upper (D 10) (R 10) [34,68,160,48,9] 13 :=
  permutation_upper _ _ _ [6,33,40,80,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1207

theorem m3093_65 : Upper (D 10) (R 10) [34,68,160,48,65] 13 :=
  permutation_upper _ _ _ [34,68,40,80,160] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2012

theorem m3093_72 : Upper (D 10) (R 10) [34,68,160,48,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,160] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1935

theorem m3093_129 : Upper (D 10) (R 10) [34,68,160,48,129] 13 :=
  permutation_upper _ _ _ [34,68,40,144,96] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2021

theorem m3093_136 : Upper (D 10) (R 10) [34,68,160,48,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,96] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1944

theorem m3093_257 : Upper (D 10) (R 10) [34,68,160,48,257] 13 :=
  permutation_upper _ _ _ [34,68,40,144,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2026

theorem m3093_264 : Upper (D 10) (R 10) [34,68,160,48,264] 13 :=
  permutation_upper _ _ _ [34,65,40,144,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1949

def r3093 : Route 9 := (fun mask => (mask,id))

def c3093 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u3093 : Upper (D 10) (R 10) [34,68,160,48] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r3093 c3093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3093_9
  · exact m3093_65
  · exact m3093_72
  · exact m3093_129
  · exact m3093_136
  · exact u2167
  · exact m3093_257
  · exact m3093_264
  · exact u2168
  · exact u2169

def b3094 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 73 440 440 504 440 440), lower := (rows 35 70 164 73 16 32 64 128 256), losses := [] }

theorem u3094 : Upper (D 10) (R 10) [34,68,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3094 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3095_9 : Upper (D 10) (R 10) [34,68,160,80,9] 13 :=
  permutation_upper _ _ _ [6,40,65,80,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1292

theorem m3095_33 : Upper (D 10) (R 10) [34,68,160,80,33] 13 :=
  permutation_upper _ _ _ [34,36,72,160,65] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1890

theorem m3095_40 : Upper (D 10) (R 10) [34,68,160,80,40] 13 :=
  permutation_upper _ _ _ [34,65,40,80,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1935

def r3095 : Route 9 := (fun mask => (mask,id))

def c3095 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3095 : Upper (D 10) (R 10) [34,68,160,80] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3095 c3095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3095_9
  · exact m3095_33
  · exact m3095_40
  · exact u2174
  · exact u2175
  · exact u2176
  · exact u2177
  · exact u2178
  · exact u2179
  · exact u2180

theorem m3096_9 : Upper (D 10) (R 10) [34,68,160,96,9] 13 :=
  permutation_upper _ _ _ [6,40,96,80,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1354

def r3096 : Route 9 := (fun mask => (mask,id))

def c3096 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3096 : Upper (D 10) (R 10) [34,68,160,96] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96] 13 (by decide) (choices 2) [9,129,136,257,264,384] r3096 c3096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3096_9
  · exact u2181
  · exact u2182
  · exact u2183
  · exact u2184
  · exact u2185

theorem m3097_40 : Upper (D 10) (R 10) [34,68,160,129,40] 13 :=
  permutation_upper _ _ _ [34,68,40,144,96] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2021

theorem m3097_72 : Upper (D 10) (R 10) [34,68,160,129,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2174

theorem m3097_96 : Upper (D 10) (R 10) [34,68,160,129,96] 13 :=
  permutation_upper _ _ _ [34,68,160,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2181

def r3097 : Route 9 := (fun mask => (mask,id))

def c3097 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3097 : Upper (D 10) (R 10) [34,68,160,129] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129] 13 (by decide) (choices 2) [40,72,96,264,288,320] r3097 c3097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3097_40
  · exact m3097_72
  · exact m3097_96
  · exact u2186
  · exact u2187
  · exact u2188

theorem m3098_9 : Upper (D 10) (R 10) [34,68,160,144,9] 13 :=
  permutation_upper _ _ _ [6,40,65,144,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1296

theorem m3098_33 : Upper (D 10) (R 10) [34,68,160,144,33] 13 :=
  permutation_upper _ _ _ [34,36,72,160,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1891

theorem m3098_40 : Upper (D 10) (R 10) [34,68,160,144,40] 13 :=
  permutation_upper _ _ _ [34,65,40,144,96] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1944

theorem m3098_65 : Upper (D 10) (R 10) [34,68,160,144,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2170

theorem m3098_72 : Upper (D 10) (R 10) [34,68,160,144,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2175

theorem m3098_96 : Upper (D 10) (R 10) [34,68,160,144,96] 13 :=
  permutation_upper _ _ _ [34,68,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2182

def r3098 : Route 9 := (fun mask => (mask,id))

def c3098 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3098 : Upper (D 10) (R 10) [34,68,160,144] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3098 c3098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3098_9
  · exact m3098_33
  · exact m3098_40
  · exact m3098_65
  · exact m3098_72
  · exact m3098_96
  · exact u2189
  · exact u2190
  · exact u2191
  · exact u2192

def b3099 : PairBound 9 := { available := 345, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 35 70 164 168 345 377 345 473 345), lower := (rows 35 70 164 168 16 32 64 128 256), losses := [] }

theorem u3099 : Upper (D 10) (R 10) [34,68,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3099 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3100_9 : Upper (D 10) (R 10) [34,68,160,192,9] 13 :=
  permutation_upper _ _ _ [6,40,192,80,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1405

theorem m3100_33 : Upper (D 10) (R 10) [34,68,160,192,33] 13 :=
  permutation_upper _ _ _ [34,36,72,160,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1892

theorem m3100_40 : Upper (D 10) (R 10) [34,68,160,192,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2167

def r3100 : Route 9 := (fun mask => (mask,id))

def c3100 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3100 : Upper (D 10) (R 10) [34,68,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r3100 c3100
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3100_9
  · exact m3100_33
  · exact m3100_40
  · exact u2196
  · exact u2197
  · exact u2198

theorem m3101_40 : Upper (D 10) (R 10) [34,68,160,257,40] 13 :=
  permutation_upper _ _ _ [34,68,40,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2026

theorem m3101_72 : Upper (D 10) (R 10) [34,68,160,257,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2177

theorem m3101_96 : Upper (D 10) (R 10) [34,68,160,257,96] 13 :=
  permutation_upper _ _ _ [34,68,160,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2183

theorem m3101_136 : Upper (D 10) (R 10) [34,68,160,257,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2189

theorem m3101_160 : Upper (D 10) (R 10) [34,68,160,257,160] 13 :=
  permutation_upper _ _ _ [34,68,160,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2193

theorem m3101_192 : Upper (D 10) (R 10) [34,68,160,257,192] 13 :=
  permutation_upper _ _ _ [34,68,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2196

def r3101 : Route 9 := (fun mask => (mask,id))

def c3101 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3101 : Upper (D 10) (R 10) [34,68,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r3101 c3101
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3101_40
  · exact m3101_72
  · exact m3101_96
  · exact m3101_136
  · exact m3101_160
  · exact m3101_192
  · exact u2199
  · exact u2200
  · exact u2201
  · exact u2202

theorem m3102_9 : Upper (D 10) (R 10) [34,68,160,272,9] 13 :=
  permutation_upper _ _ _ [6,40,65,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1299

theorem m3102_33 : Upper (D 10) (R 10) [34,68,160,272,33] 13 :=
  permutation_upper _ _ _ [34,36,72,160,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1893

theorem m3102_40 : Upper (D 10) (R 10) [34,68,160,272,40] 13 :=
  permutation_upper _ _ _ [34,65,40,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1949

theorem m3102_65 : Upper (D 10) (R 10) [34,68,160,272,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2171

theorem m3102_72 : Upper (D 10) (R 10) [34,68,160,272,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2178

theorem m3102_96 : Upper (D 10) (R 10) [34,68,160,272,96] 13 :=
  permutation_upper _ _ _ [34,68,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2184

theorem m3102_129 : Upper (D 10) (R 10) [34,68,160,272,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2186

theorem m3102_136 : Upper (D 10) (R 10) [34,68,160,272,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2190

theorem m3102_160 : Upper (D 10) (R 10) [34,68,160,272,160] 13 :=
  permutation_upper _ _ _ [34,68,160,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2194

theorem m3102_192 : Upper (D 10) (R 10) [34,68,160,272,192] 13 :=
  permutation_upper _ _ _ [34,68,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2197

theorem m3102_257 : Upper (D 10) (R 10) [34,68,160,272,257] 13 :=
  permutation_upper _ _ _ [34,68,160,257,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2199

def r3102 : Route 9 := (fun mask => (mask,id))

def c3102 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3102 : Upper (D 10) (R 10) [34,68,160,272] 13 := by
  apply FastRouting.sound _ _ [34,68,160,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r3102 c3102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3102_9
  · exact m3102_33
  · exact m3102_40
  · exact m3102_65
  · exact m3102_72
  · exact m3102_96
  · exact m3102_129
  · exact m3102_136
  · exact m3102_160
  · exact m3102_192
  · exact m3102_257
  · exact u2203
  · exact u2204
  · exact u2205
  · exact u2206

theorem m3103_9 : Upper (D 10) (R 10) [34,68,160,288,9] 13 :=
  permutation_upper _ _ _ [6,40,96,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1371

theorem m3103_65 : Upper (D 10) (R 10) [34,68,160,288,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2172

theorem m3103_72 : Upper (D 10) (R 10) [34,68,160,288,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2179

theorem m3103_129 : Upper (D 10) (R 10) [34,68,160,288,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2187

theorem m3103_136 : Upper (D 10) (R 10) [34,68,160,288,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2191

theorem m3103_192 : Upper (D 10) (R 10) [34,68,160,288,192] 13 :=
  permutation_upper _ _ _ [34,68,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2198

theorem m3103_257 : Upper (D 10) (R 10) [34,68,160,288,257] 13 :=
  permutation_upper _ _ _ [34,68,160,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2200

theorem m3103_264 : Upper (D 10) (R 10) [34,68,160,288,264] 13 :=
  permutation_upper _ _ _ [34,68,160,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2204

def r3103 : Route 9 := (fun mask => (mask,id))

def c3103 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u3103 : Upper (D 10) (R 10) [34,68,160,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,288] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r3103 c3103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3103_9
  · exact m3103_65
  · exact m3103_72
  · exact m3103_129
  · exact m3103_136
  · exact m3103_192
  · exact m3103_257
  · exact m3103_264
  · exact u2207
  · exact u2208

theorem m3104_9 : Upper (D 10) (R 10) [34,68,160,320,9] 13 :=
  permutation_upper _ _ _ [6,40,192,80,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1407

theorem m3104_33 : Upper (D 10) (R 10) [34,68,160,320,33] 13 :=
  permutation_upper _ _ _ [34,36,72,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1894

theorem m3104_40 : Upper (D 10) (R 10) [34,68,160,320,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2168

theorem m3104_129 : Upper (D 10) (R 10) [34,68,160,320,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2188

theorem m3104_136 : Upper (D 10) (R 10) [34,68,160,320,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2192

theorem m3104_160 : Upper (D 10) (R 10) [34,68,160,320,160] 13 :=
  permutation_upper _ _ _ [34,68,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2195

theorem m3104_257 : Upper (D 10) (R 10) [34,68,160,320,257] 13 :=
  permutation_upper _ _ _ [34,68,160,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2201

theorem m3104_264 : Upper (D 10) (R 10) [34,68,160,320,264] 13 :=
  permutation_upper _ _ _ [34,68,160,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2205

theorem m3104_288 : Upper (D 10) (R 10) [34,68,160,320,288] 13 :=
  permutation_upper _ _ _ [34,68,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2207

def r3104 : Route 9 := (fun mask => (mask,id))

def c3104 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3104 : Upper (D 10) (R 10) [34,68,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3104 c3104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3104_9
  · exact m3104_33
  · exact m3104_40
  · exact m3104_129
  · exact m3104_136
  · exact m3104_160
  · exact m3104_257
  · exact m3104_264
  · exact m3104_288
  · exact u2209

theorem m3105_9 : Upper (D 10) (R 10) [34,68,160,384,9] 13 :=
  permutation_upper _ _ _ [6,40,192,272,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1423

theorem m3105_33 : Upper (D 10) (R 10) [34,68,160,384,33] 13 :=
  permutation_upper _ _ _ [34,36,72,160,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1895

theorem m3105_40 : Upper (D 10) (R 10) [34,68,160,384,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2169

theorem m3105_65 : Upper (D 10) (R 10) [34,68,160,384,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2173

theorem m3105_72 : Upper (D 10) (R 10) [34,68,160,384,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2180

theorem m3105_96 : Upper (D 10) (R 10) [34,68,160,384,96] 13 :=
  permutation_upper _ _ _ [34,68,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2185

theorem m3105_257 : Upper (D 10) (R 10) [34,68,160,384,257] 13 :=
  permutation_upper _ _ _ [34,68,160,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2202

theorem m3105_264 : Upper (D 10) (R 10) [34,68,160,384,264] 13 :=
  permutation_upper _ _ _ [34,68,160,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2206

theorem m3105_288 : Upper (D 10) (R 10) [34,68,160,384,288] 13 :=
  permutation_upper _ _ _ [34,68,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2208

theorem m3105_320 : Upper (D 10) (R 10) [34,68,160,384,320] 13 :=
  permutation_upper _ _ _ [34,68,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2209

def r3105 : Route 9 := (fun mask => (mask,id))

def c3105 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3105 : Upper (D 10) (R 10) [34,68,160,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3105 c3105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3105_9
  · exact m3105_33
  · exact m3105_40
  · exact m3105_65
  · exact m3105_72
  · exact m3105_96
  · exact m3105_257
  · exact m3105_264
  · exact m3105_288
  · exact m3105_320

def b3106 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 137 312 312 376 440 312), lower := (rows 35 70 196 137 16 32 64 128 256), losses := [] }

theorem u3106 : Upper (D 10) (R 10) [34,68,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3106 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3107 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 168 313 313 377 441 313), lower := (rows 35 70 196 168 16 32 64 128 256), losses := [] }

theorem u3107 : Upper (D 10) (R 10) [34,68,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3107 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3108 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 265 440 440 504 440 440), lower := (rows 35 70 196 265 16 32 64 128 256), losses := [] }

theorem u3108 : Upper (D 10) (R 10) [34,68,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3108 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3109 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 296 441 441 505 441 441), lower := (rows 35 70 196 296 16 32 64 128 256), losses := [] }

theorem u3109 : Upper (D 10) (R 10) [34,68,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3109 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3110 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 392 313 313 377 441 313), lower := (rows 35 70 196 392 16 32 64 128 256), losses := [] }

theorem u3110 : Upper (D 10) (R 10) [34,68,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3110 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3111_9 : Upper (D 10) (R 10) [34,68,384,48,9] 13 :=
  permutation_upper _ _ _ [6,33,40,80,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1208

theorem m3111_33 : Upper (D 10) (R 10) [34,68,384,48,33] 13 :=
  permutation_upper _ _ _ [34,36,40,80,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1862

theorem m3111_40 : Upper (D 10) (R 10) [34,68,384,48,40] 13 :=
  permutation_upper _ _ _ [34,33,40,80,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1845

theorem m3111_65 : Upper (D 10) (R 10) [34,68,384,48,65] 13 :=
  permutation_upper _ _ _ [34,68,40,80,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2013

theorem m3111_72 : Upper (D 10) (R 10) [34,68,384,48,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1936

theorem m3111_129 : Upper (D 10) (R 10) [34,68,384,48,129] 13 :=
  permutation_upper _ _ _ [34,68,40,144,320] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2027

theorem m3111_136 : Upper (D 10) (R 10) [34,68,384,48,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,320] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1950

def r3111 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3111 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3111 : Upper (D 10) (R 10) [34,68,384,48] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,384] r3111 c3111
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3111_9
  · exact m3111_33
  · exact m3111_40
  · exact m3111_65
  · exact m3111_72
  · exact u2222
  · exact m3111_129
  · exact m3111_136
  · exact u2223
  · exact u2224
  · exact u2225

def b3112 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 388 73 440 440 504 440 440), lower := (rows 35 70 388 73 16 32 64 128 256), losses := [] }

theorem u3112 : Upper (D 10) (R 10) [34,68,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3112 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3113_9 : Upper (D 10) (R 10) [34,68,384,80,9] 13 :=
  permutation_upper _ _ _ [6,40,65,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1293

theorem m3113_33 : Upper (D 10) (R 10) [34,68,384,80,33] 13 :=
  permutation_upper _ _ _ [34,36,72,384,65] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1896

theorem m3113_40 : Upper (D 10) (R 10) [34,68,384,80,40] 13 :=
  permutation_upper _ _ _ [34,65,40,80,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1936

def r3113 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3113 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3113 : Upper (D 10) (R 10) [34,68,384,80] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,384] r3113 c3113
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3113_9
  · exact m3113_33
  · exact m3113_40
  · exact u2228
  · exact u2229
  · exact u2230
  · exact u2231

theorem m3114_9 : Upper (D 10) (R 10) [34,68,384,96,9] 13 :=
  permutation_upper _ _ _ [6,40,96,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1355

theorem m3114_33 : Upper (D 10) (R 10) [34,68,384,96,33] 13 :=
  permutation_upper _ _ _ [34,36,72,384,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1897

theorem m3114_40 : Upper (D 10) (R 10) [34,68,384,96,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2222

def r3114 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3114 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3114 : Upper (D 10) (R 10) [34,68,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,384] r3114 c3114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3114_9
  · exact m3114_33
  · exact m3114_40
  · exact u2232
  · exact u2233
  · exact u2234
  · exact u2235

theorem m3115_40 : Upper (D 10) (R 10) [34,68,384,129,40] 13 :=
  permutation_upper _ _ _ [34,68,40,144,320] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2027

theorem m3115_72 : Upper (D 10) (R 10) [34,68,384,129,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2228

theorem m3115_96 : Upper (D 10) (R 10) [34,68,384,129,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2232

def r3115 : Route 9 := (fun mask => (mask,id))

def c3115 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3115 : Upper (D 10) (R 10) [34,68,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129] 13 (by decide) (choices 2) [40,72,96,264,288,320] r3115 c3115
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3115_40
  · exact m3115_72
  · exact m3115_96
  · exact u2236
  · exact u2237
  · exact u2238

theorem m3116_9 : Upper (D 10) (R 10) [34,68,384,144,9] 13 :=
  permutation_upper _ _ _ [6,40,65,144,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1300

theorem m3116_33 : Upper (D 10) (R 10) [34,68,384,144,33] 13 :=
  permutation_upper _ _ _ [34,36,72,384,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1898

theorem m3116_40 : Upper (D 10) (R 10) [34,68,384,144,40] 13 :=
  permutation_upper _ _ _ [34,65,40,144,320] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1950

theorem m3116_65 : Upper (D 10) (R 10) [34,68,384,144,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2226

theorem m3116_72 : Upper (D 10) (R 10) [34,68,384,144,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2229

theorem m3116_96 : Upper (D 10) (R 10) [34,68,384,144,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2233

theorem m3116_257 : Upper (D 10) (R 10) [34,68,384,144,257] 13 :=
  permutation_upper _ _ _ [34,68,384,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2236

def r3116 : Route 9 := (fun mask => (mask,id))

def c3116 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3116 : Upper (D 10) (R 10) [34,68,384,144] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3116 c3116
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3116_9
  · exact m3116_33
  · exact m3116_40
  · exact m3116_65
  · exact m3116_72
  · exact m3116_96
  · exact m3116_257
  · exact u2239
  · exact u2240
  · exact u2241

theorem m3117_9 : Upper (D 10) (R 10) [34,68,384,160,9] 13 :=
  permutation_upper _ _ _ [6,40,96,144,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1372

theorem m3117_33 : Upper (D 10) (R 10) [34,68,384,160,33] 13 :=
  permutation_upper _ _ _ [34,36,72,384,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1899

theorem m3117_40 : Upper (D 10) (R 10) [34,68,384,160,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2223

theorem m3117_65 : Upper (D 10) (R 10) [34,68,384,160,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2227

theorem m3117_72 : Upper (D 10) (R 10) [34,68,384,160,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2230

theorem m3117_96 : Upper (D 10) (R 10) [34,68,384,160,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2234

theorem m3117_257 : Upper (D 10) (R 10) [34,68,384,160,257] 13 :=
  permutation_upper _ _ _ [34,68,384,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2237

theorem m3117_264 : Upper (D 10) (R 10) [34,68,384,160,264] 13 :=
  permutation_upper _ _ _ [34,68,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2240

def r3117 : Route 9 := (fun mask => (mask,id))

def c3117 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3117 : Upper (D 10) (R 10) [34,68,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3117 c3117
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3117_9
  · exact m3117_33
  · exact m3117_40
  · exact m3117_65
  · exact m3117_72
  · exact m3117_96
  · exact m3117_257
  · exact m3117_264
  · exact u2242
  · exact u2243

theorem m3118_9 : Upper (D 10) (R 10) [34,68,384,192,9] 13 :=
  permutation_upper _ _ _ [6,40,192,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1408

theorem m3118_33 : Upper (D 10) (R 10) [34,68,384,192,33] 13 :=
  permutation_upper _ _ _ [34,36,72,384,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1900

theorem m3118_40 : Upper (D 10) (R 10) [34,68,384,192,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2224

theorem m3118_257 : Upper (D 10) (R 10) [34,68,384,192,257] 13 :=
  permutation_upper _ _ _ [34,68,384,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2238

theorem m3118_264 : Upper (D 10) (R 10) [34,68,384,192,264] 13 :=
  permutation_upper _ _ _ [34,68,384,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2241

theorem m3118_288 : Upper (D 10) (R 10) [34,68,384,192,288] 13 :=
  permutation_upper _ _ _ [34,68,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2243

def r3118 : Route 9 := (fun mask => (mask,id))

def c3118 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3118 : Upper (D 10) (R 10) [34,68,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r3118 c3118
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3118_9
  · exact m3118_33
  · exact m3118_40
  · exact m3118_257
  · exact m3118_264
  · exact m3118_288

def b3119 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 35 70 388 392 121 121 121 249 377), lower := (rows 35 70 388 392 16 32 64 128 256), losses := [] }

theorem u3119 : Upper (D 10) (R 10) [34,68,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3119 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u3119
end Delivery.IrregularNine14.P10
