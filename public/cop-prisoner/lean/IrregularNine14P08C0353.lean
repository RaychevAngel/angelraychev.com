import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0211
import IrregularNine14P08C0233
import IrregularNine14P08C0234
import IrregularNine14P08C0235
import IrregularNine14P08C0236

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21180 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 138 433 433 497 433 433), lower := (rows 97 14 69 138 16 32 64 128 256), losses := [] }

theorem u21180 : Upper (D 8) (R 8) [96,12,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21181 : PairBound 9 := { available := 419, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 152 435 419 483 419 419), lower := (rows 97 14 69 152 16 32 64 128 256), losses := [] }

theorem u21181 : Upper (D 8) (R 8) [96,12,65,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21182 : PairBound 9 := { available := 435, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 168 435 435 499 435 435), lower := (rows 97 14 69 168 16 32 64 128 256), losses := [] }

theorem u21182 : Upper (D 8) (R 8) [96,12,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21183 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 265 178 178 242 178 434), lower := (rows 97 14 69 265 16 32 64 128 256), losses := [] }

theorem u21183 : Upper (D 8) (R 8) [96,12,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21184 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 266 177 177 241 177 433), lower := (rows 97 14 69 266 16 32 64 128 256), losses := [] }

theorem u21184 : Upper (D 8) (R 8) [96,12,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21185 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 280 179 163 227 163 419), lower := (rows 97 14 69 280 16 32 64 128 256), losses := [] }

theorem u21185 : Upper (D 8) (R 8) [96,12,65,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21186 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 296 179 179 243 179 435), lower := (rows 97 14 69 296 16 32 64 128 256), losses := [] }

theorem u21186 : Upper (D 8) (R 8) [96,12,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21187 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 392 179 179 243 179 435), lower := (rows 97 14 69 392 16 32 64 128 256), losses := [] }

theorem u21187 : Upper (D 8) (R 8) [96,12,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21188 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 137 433 433 497 433 433), lower := (rows 97 14 70 137 16 32 64 128 256), losses := [] }

theorem u21188 : Upper (D 8) (R 8) [96,12,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21189 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 152 433 417 481 417 417), lower := (rows 97 14 70 152 16 32 64 128 256), losses := [] }

theorem u21189 : Upper (D 8) (R 8) [96,12,66,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21190 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 168 433 433 497 433 433), lower := (rows 97 14 70 168 16 32 64 128 256), losses := [] }

theorem u21190 : Upper (D 8) (R 8) [96,12,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21191 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 265 177 177 241 177 433), lower := (rows 97 14 70 265 16 32 64 128 256), losses := [] }

theorem u21191 : Upper (D 8) (R 8) [96,12,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21192 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 280 177 161 225 161 417), lower := (rows 97 14 70 280 16 32 64 128 256), losses := [] }

theorem u21192 : Upper (D 8) (R 8) [96,12,66,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21193 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 296 177 177 241 177 433), lower := (rows 97 14 70 296 16 32 64 128 256), losses := [] }

theorem u21193 : Upper (D 8) (R 8) [96,12,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21194 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 70 392 177 177 241 177 433), lower := (rows 97 14 70 392 16 32 64 128 256), losses := [] }

theorem u21194 : Upper (D 8) (R 8) [96,12,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21195_3 : Upper (D 8) (R 8) [96,12,80,129,3] 13 :=
  permutation_upper _ _ _ [96,5,24,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12679

def r21195 : Route 9 := (fun mask => (mask,id))

def c21195 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21195 : Upper (D 8) (R 8) [96,12,80,129] 13 := by
  apply FastRouting.sound _ _ [96,12,80,129] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r21195 c21195
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21195_3
  · exact u14003
  · exact u14004
  · exact u14005
  · exact u14006
  · exact u14007
  · exact u14008
  · exact u14009
  · exact u14010
  · exact u14011

def b21196 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 84 138 433 417 481 417 417), lower := (rows 97 14 84 138 16 32 64 128 256), losses := [] }

theorem u21196 : Upper (D 8) (R 8) [96,12,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21197_3 : Upper (D 8) (R 8) [96,12,80,160,3] 13 :=
  permutation_upper _ _ _ [96,5,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12680

def r21197 : Route 9 := (fun mask => (mask,id))

def c21197 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21197 : Upper (D 8) (R 8) [96,12,80,160] 13 := by
  apply FastRouting.sound _ _ [96,12,80,160] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r21197 c21197
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21197_3
  · exact u14017
  · exact u14018
  · exact u14019
  · exact u14020
  · exact u14021
  · exact u14022
  · exact u14023
  · exact u14024
  · exact u14025

theorem m21198_3 : Upper (D 8) (R 8) [96,12,80,257,3] 13 :=
  permutation_upper _ _ _ [96,5,24,66,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12681

def r21198 : Route 9 := (fun mask => (mask,id))

def c21198 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21198 : Upper (D 8) (R 8) [96,12,80,257] 13 := by
  apply FastRouting.sound _ _ [96,12,80,257] 13 (by decide) (choices 2) [3,33,34,129,130,160] r21198 c21198
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21198_3
  · exact u14026
  · exact u14027
  · exact u14028
  · exact u14029
  · exact u14030

def b21199 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 84 266 177 161 225 161 417), lower := (rows 97 14 84 266 16 32 64 128 256), losses := [] }

theorem u21199 : Upper (D 8) (R 8) [96,12,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21200_3 : Upper (D 8) (R 8) [96,12,80,288,3] 13 :=
  permutation_upper _ _ _ [96,5,24,66,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12682

def r21200 : Route 9 := (fun mask => (mask,id))

def c21200 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21200 : Upper (D 8) (R 8) [96,12,80,288] 13 := by
  apply FastRouting.sound _ _ [96,12,80,288] 13 (by decide) (choices 2) [3,33,34,129,130,160] r21200 c21200
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21200_3
  · exact u14033
  · exact u14034
  · exact u14035
  · exact u14036
  · exact u14037

theorem m21201_3 : Upper (D 8) (R 8) [96,12,80,384,3] 13 :=
  permutation_upper _ _ _ [96,5,24,66,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12683

def r21201 : Route 9 := (fun mask => (mask,id))

def c21201 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21201 : Upper (D 8) (R 8) [96,12,80,384] 13 := by
  apply FastRouting.sound _ _ [96,12,80,384] 13 (by decide) (choices 2) [3,33,34,129,130,160] r21201 c21201
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21201_3
  · exact u14038
  · exact u14039
  · exact u14040
  · exact u14041
  · exact u14042

def b21202 : PairBound 9 := { available := 435, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 435 435 499 435 435), lower := (rows 97 14 100 137 16 32 64 128 256), losses := [] }

theorem u21202 : Upper (D 8) (R 8) [96,12,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21203 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 138 433 433 497 433 433), lower := (rows 97 14 100 138 16 32 64 128 256), losses := [] }

theorem u21203 : Upper (D 8) (R 8) [96,12,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21204 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 152 435 419 483 419 419), lower := (rows 97 14 100 152 16 32 64 128 256), losses := [] }

theorem u21204 : Upper (D 8) (R 8) [96,12,96,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21205 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 168 403 435 467 403 403), lower := (rows 97 14 100 168 16 32 64 128 256), losses := [] }

theorem u21205 : Upper (D 8) (R 8) [96,12,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21206 : PairBound 9 := { available := 179, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 265 179 179 243 179 435), lower := (rows 97 14 100 265 16 32 64 128 256), losses := [] }

theorem u21206 : Upper (D 8) (R 8) [96,12,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21207 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 266 177 177 241 177 433), lower := (rows 97 14 100 266 16 32 64 128 256), losses := [] }

theorem u21207 : Upper (D 8) (R 8) [96,12,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21208 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 280 179 163 227 163 419), lower := (rows 97 14 100 280 16 32 64 128 256), losses := [] }

theorem u21208 : Upper (D 8) (R 8) [96,12,96,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21209 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 296 147 179 211 147 403), lower := (rows 97 14 100 296 16 32 64 128 256), losses := [] }

theorem u21209 : Upper (D 8) (R 8) [96,12,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21210 : PairBound 9 := { available := 179, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 392 179 179 243 179 435), lower := (rows 97 14 100 392 16 32 64 128 256), losses := [] }

theorem u21210 : Upper (D 8) (R 8) [96,12,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21211 : PairBound 9 := { available := 370, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 370 370 370 498 370), lower := (rows 97 14 133 137 16 32 64 128 256), losses := [] }

theorem u21211 : Upper (D 8) (R 8) [96,12,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21212 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 133 138 369 369 369 497 369), lower := (rows 97 14 133 138 16 32 64 128 256), losses := [] }

theorem u21212 : Upper (D 8) (R 8) [96,12,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21213 : PairBound 9 := { available := 355, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 371 355 355 483 355), lower := (rows 97 14 133 152 16 32 64 128 256), losses := [] }

theorem u21213 : Upper (D 8) (R 8) [96,12,129,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21214 : PairBound 9 := { available := 371, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 371 371 371 499 371), lower := (rows 97 14 133 168 16 32 64 128 256), losses := [] }

theorem u21214 : Upper (D 8) (R 8) [96,12,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21215 : PairBound 9 := { available := 307, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 200 307 307 371 435 307), lower := (rows 97 14 133 200 16 32 64 128 256), losses := [] }

theorem u21215 : Upper (D 8) (R 8) [96,12,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21216 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 265 242 242 242 242 498), lower := (rows 97 14 133 265 16 32 64 128 256), losses := [] }

theorem u21216 : Upper (D 8) (R 8) [96,12,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r21217 : Route 9 := (fun mask => (mask,id))

def c21217 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21217 : Upper (D 8) (R 8) [96,12,129,258] 13 := by
  apply FastRouting.sound _ _ [96,12,129,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21217 c21217
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u14103
  · exact u14104
  · exact u14105
  · exact u14106
  · exact u14107
  · exact u14108

theorem m21218_3 : Upper (D 8) (R 8) [96,12,129,272,3] 13 :=
  permutation_upper _ _ _ [96,5,24,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12692

def r21218 : Route 9 := (fun mask => (mask,id))

def c21218 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21218 : Upper (D 8) (R 8) [96,12,129,272] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21218 c21218
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21218_3
  · exact u14109
  · exact u14110
  · exact u14111
  · exact u14112
  · exact u14113
  · exact u14114
  · exact u14115
  · exact u14116
  · exact u14117

theorem m21219_3 : Upper (D 8) (R 8) [96,12,129,288,3] 13 :=
  permutation_upper _ _ _ [96,5,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12693

def r21219 : Route 9 := (fun mask => (mask,id))

def c21219 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21219 : Upper (D 8) (R 8) [96,12,129,288] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21219 c21219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21219_3
  · exact u14118
  · exact u14119
  · exact u14120
  · exact u14121
  · exact u14122
  · exact u14123
  · exact u14124
  · exact u14125
  · exact u14126

theorem m21220_3 : Upper (D 8) (R 8) [96,12,129,320,3] 13 :=
  permutation_upper _ _ _ [96,5,24,129,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12694

def r21220 : Route 9 := (fun mask => (mask,id))

def c21220 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21220 : Upper (D 8) (R 8) [96,12,129,320] 13 := by
  apply FastRouting.sound _ _ [96,12,129,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r21220 c21220
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21220_3
  · exact u14127
  · exact u14128
  · exact u14129
  · exact u14130
  · exact u14131

def b21221 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 392 115 115 115 243 371), lower := (rows 97 14 133 392 16 32 64 128 256), losses := [] }

theorem u21221 : Upper (D 8) (R 8) [96,12,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21222 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 152 369 353 353 481 353), lower := (rows 97 14 134 152 16 32 64 128 256), losses := [] }

theorem u21222 : Upper (D 8) (R 8) [96,12,130,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21223 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 168 369 369 369 497 369), lower := (rows 97 14 134 168 16 32 64 128 256), losses := [] }

theorem u21223 : Upper (D 8) (R 8) [96,12,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21224 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 200 305 305 369 433 305), lower := (rows 97 14 134 200 16 32 64 128 256), losses := [] }

theorem u21224 : Upper (D 8) (R 8) [96,12,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r21225 : Route 9 := (fun mask => (mask,id))

def c21225 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21225 : Upper (D 8) (R 8) [96,12,130,257] 13 := by
  apply FastRouting.sound _ _ [96,12,130,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21225 c21225
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u14142
  · exact u14143
  · exact u14144
  · exact u14145
  · exact u14146
  · exact u14147

def r21226 : Route 9 := (fun mask => (mask,id))

def c21226 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21226 : Upper (D 8) (R 8) [96,12,130,272] 13 := by
  apply FastRouting.sound _ _ [96,12,130,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21226 c21226
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u14148
  · exact u14149
  · exact u14150
  · exact u14151
  · exact u14152
  · exact u14153

def r21227 : Route 9 := (fun mask => (mask,id))

def c21227 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21227 : Upper (D 8) (R 8) [96,12,130,288] 13 := by
  apply FastRouting.sound _ _ [96,12,130,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21227 c21227
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u14154
  · exact u14155
  · exact u14156
  · exact u14157
  · exact u14158
  · exact u14159

def b21228 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 134 328 177 177 241 177 433), lower := (rows 97 14 134 328 16 32 64 128 256), losses := [] }

theorem u21228 : Upper (D 8) (R 8) [96,12,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21229 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 392 113 113 113 241 369), lower := (rows 97 14 134 392 16 32 64 128 256), losses := [] }

theorem u21229 : Upper (D 8) (R 8) [96,12,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21230 : PairBound 9 := { available := 355, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 168 371 355 355 483 355), lower := (rows 97 14 148 168 16 32 64 128 256), losses := [] }

theorem u21230 : Upper (D 8) (R 8) [96,12,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21231 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 200 307 291 355 419 291), lower := (rows 97 14 148 200 16 32 64 128 256), losses := [] }

theorem u21231 : Upper (D 8) (R 8) [96,12,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21232_3 : Upper (D 8) (R 8) [96,12,144,257,3] 13 :=
  permutation_upper _ _ _ [96,5,24,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12698

def r21232 : Route 9 := (fun mask => (mask,id))

def c21232 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21232 : Upper (D 8) (R 8) [96,12,144,257] 13 := by
  apply FastRouting.sound _ _ [96,12,144,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21232 c21232
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21232_3
  · exact u14172
  · exact u14173
  · exact u14174
  · exact u14175
  · exact u14176
  · exact u14177
  · exact u14178
  · exact u14179
  · exact u14180

def r21233 : Route 9 := (fun mask => (mask,id))

def c21233 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21233 : Upper (D 8) (R 8) [96,12,144,258] 13 := by
  apply FastRouting.sound _ _ [96,12,144,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21233 c21233
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u14181
  · exact u14182
  · exact u14183
  · exact u14184
  · exact u14185
  · exact u14186

theorem m21234_3 : Upper (D 8) (R 8) [96,12,144,288,3] 13 :=
  permutation_upper _ _ _ [96,5,24,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12699

def r21234 : Route 9 := (fun mask => (mask,id))

def c21234 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21234 : Upper (D 8) (R 8) [96,12,144,288] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21234 c21234
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21234_3
  · exact u14187
  · exact u14188
  · exact u14189
  · exact u14190
  · exact u14191
  · exact u14192
  · exact u14193
  · exact u14194
  · exact u14195

theorem m21235_3 : Upper (D 8) (R 8) [96,12,144,320,3] 13 :=
  permutation_upper _ _ _ [96,5,24,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12700

def r21235 : Route 9 := (fun mask => (mask,id))

def c21235 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21235 : Upper (D 8) (R 8) [96,12,144,320] 13 := by
  apply FastRouting.sound _ _ [96,12,144,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r21235 c21235
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21235_3
  · exact u14196
  · exact u14197
  · exact u14198
  · exact u14199
  · exact u14200

def b21236 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 148 392 115 99 99 227 355), lower := (rows 97 14 148 392 16 32 64 128 256), losses := [] }

theorem u21236 : Upper (D 8) (R 8) [96,12,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21237 : PairBound 9 := { available := 339, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 164 168 339 371 339 467 339), lower := (rows 97 14 164 168 16 32 64 128 256), losses := [] }

theorem u21237 : Upper (D 8) (R 8) [96,12,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21238 : PairBound 9 := { available := 307, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 200 307 307 371 435 307), lower := (rows 97 14 164 200 16 32 64 128 256), losses := [] }

theorem u21238 : Upper (D 8) (R 8) [96,12,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21239_3 : Upper (D 8) (R 8) [96,12,160,257,3] 13 :=
  permutation_upper _ _ _ [96,5,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12704

def r21239 : Route 9 := (fun mask => (mask,id))

def c21239 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21239 : Upper (D 8) (R 8) [96,12,160,257] 13 := by
  apply FastRouting.sound _ _ [96,12,160,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21239 c21239
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21239_3
  · exact u14211
  · exact u14212
  · exact u14213
  · exact u14214
  · exact u14215
  · exact u14216
  · exact u14217
  · exact u14218
  · exact u14219

#print axioms u21239
end Delivery.IrregularNine14.P08
