import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0024
import IrregularNine14P10C0025
import IrregularNine14P10C0026
import IrregularNine14P10C0027
import IrregularNine14P10C0028
import IrregularNine14P10C0029
import IrregularNine14P10C0030
import IrregularNine14P10C0032
import IrregularNine14P10C0033
import IrregularNine14P10C0034
import IrregularNine14P10C0035
import IrregularNine14P10C0036
import IrregularNine14P10C0037
import IrregularNine14P10C0038
import IrregularNine14P10C0039
import IrregularNine14P10C0040
import IrregularNine14P10C0041
import IrregularNine14P10C0042

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m3360_5 : Upper (D 10) (R 10) [66,144,288,320,5] 13 :=
  permutation_upper _ _ _ [6,72,160,257,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1633

theorem m3360_9 : Upper (D 10) (R 10) [66,144,288,320,9] 13 :=
  permutation_upper _ _ _ [6,72,192,257,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1680

theorem m3360_12 : Upper (D 10) (R 10) [66,144,288,320,12] 13 :=
  permutation_upper _ _ _ [6,96,192,144,257] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1787

theorem m3360_33 : Upper (D 10) (R 10) [66,144,288,320,33] 13 :=
  permutation_upper _ _ _ [34,68,129,288,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2099

theorem m3360_36 : Upper (D 10) (R 10) [66,144,288,320,36] 13 :=
  permutation_upper _ _ _ [34,96,129,260,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2290

theorem m3360_40 : Upper (D 10) (R 10) [66,144,288,320,40] 13 :=
  permutation_upper _ _ _ [34,192,72,257,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2327

theorem m3360_129 : Upper (D 10) (R 10) [66,144,288,320,129] 13 :=
  permutation_upper _ _ _ [66,68,129,288,384] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2370

theorem m3360_132 : Upper (D 10) (R 10) [66,144,288,320,132] 13 :=
  permutation_upper _ _ _ [66,68,160,257,384] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2383

theorem m3360_136 : Upper (D 10) (R 10) [66,144,288,320,136] 13 :=
  permutation_upper _ _ _ [66,68,384,129,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2386

theorem m3360_160 : Upper (D 10) (R 10) [66,144,288,320,160] 13 :=
  permutation_upper _ _ _ [66,96,129,288,384] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2395

def r3360 : Route 9 := (fun mask => (mask,id))

def c3360 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u3360 : Upper (D 10) (R 10) [66,144,288,320] 13 := by
  apply FastRouting.sound _ _ [66,144,288,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r3360 c3360
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3360_5
  · exact m3360_9
  · exact m3360_12
  · exact m3360_33
  · exact m3360_36
  · exact m3360_40
  · exact m3360_129
  · exact m3360_132
  · exact m3360_136
  · exact m3360_160

theorem m3361_5 : Upper (D 10) (R 10) [66,144,288,384,5] 13 :=
  permutation_upper _ _ _ [6,72,160,257,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1636

theorem m3361_9 : Upper (D 10) (R 10) [66,144,288,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1711

theorem m3361_12 : Upper (D 10) (R 10) [66,144,288,384,12] 13 :=
  permutation_upper _ _ _ [6,96,192,129,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1785

theorem m3361_33 : Upper (D 10) (R 10) [66,144,288,384,33] 13 :=
  permutation_upper _ _ _ [34,68,129,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2100

theorem m3361_36 : Upper (D 10) (R 10) [66,144,288,384,36] 13 :=
  permutation_upper _ _ _ [34,96,129,192,260] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2286

theorem m3361_40 : Upper (D 10) (R 10) [66,144,288,384,40] 13 :=
  permutation_upper _ _ _ [34,192,65,160,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2313

theorem m3361_65 : Upper (D 10) (R 10) [66,144,288,384,65] 13 :=
  permutation_upper _ _ _ [66,68,129,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2370

theorem m3361_68 : Upper (D 10) (R 10) [66,144,288,384,68] 13 :=
  permutation_upper _ _ _ [66,132,72,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2424

theorem m3361_72 : Upper (D 10) (R 10) [66,144,288,384,72] 13 :=
  permutation_upper _ _ _ [66,132,72,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2426

theorem m3361_96 : Upper (D 10) (R 10) [66,144,288,384,96] 13 :=
  permutation_upper _ _ _ [66,132,96,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2434

def r3361 : Route 9 := (fun mask => (mask,id))

def c3361 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u3361 : Upper (D 10) (R 10) [66,144,288,384] 13 := by
  apply FastRouting.sound _ _ [66,144,288,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r3361 c3361
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3361_5
  · exact m3361_9
  · exact m3361_12
  · exact m3361_33
  · exact m3361_36
  · exact m3361_40
  · exact m3361_65
  · exact m3361_68
  · exact m3361_72
  · exact m3361_96

theorem m3362_5 : Upper (D 10) (R 10) [66,144,320,384,5] 13 :=
  permutation_upper _ _ _ [6,72,192,257,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1682

theorem m3362_9 : Upper (D 10) (R 10) [66,144,320,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,129,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1712

theorem m3362_12 : Upper (D 10) (R 10) [66,144,320,384,12] 13 :=
  permutation_upper _ _ _ [6,192,320,129,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1839

theorem m3362_33 : Upper (D 10) (R 10) [66,144,320,384,33] 13 :=
  permutation_upper _ _ _ [34,68,129,320,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2101

theorem m3362_36 : Upper (D 10) (R 10) [66,144,320,384,36] 13 :=
  permutation_upper _ _ _ [34,192,72,257,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2330

theorem m3362_40 : Upper (D 10) (R 10) [66,144,320,384,40] 13 :=
  permutation_upper _ _ _ [34,192,65,260,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2317

def r3362 : Route 9 := (fun mask => (mask,id))

def c3362 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3362 : Upper (D 10) (R 10) [66,144,320,384] 13 := by
  apply FastRouting.sound _ _ [66,144,320,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r3362 c3362
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3362_5
  · exact m3362_9
  · exact m3362_12
  · exact m3362_33
  · exact m3362_36
  · exact m3362_40

def b3363 : PairBound 9 := { available := 309, camps := [{ cop := 1, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 67 162 76 168 309 309 373 437 309), lower := (rows 67 162 76 168 16 32 64 128 256), losses := [] }

theorem u3363 : Upper (D 10) (R 10) [66,160,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3363 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3364_5 : Upper (D 10) (R 10) [66,160,72,288,5] 13 :=
  permutation_upper _ _ _ [6,72,80,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1543

theorem m3364_33 : Upper (D 10) (R 10) [66,160,72,288,33] 13 :=
  permutation_upper _ _ _ [34,68,160,80,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2179

theorem m3364_36 : Upper (D 10) (R 10) [66,160,72,288,36] 13 :=
  permutation_upper _ _ _ [34,68,160,80,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2179

theorem m3364_129 : Upper (D 10) (R 10) [66,160,72,288,129] 13 :=
  permutation_upper _ _ _ [66,132,96,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2428

theorem m3364_132 : Upper (D 10) (R 10) [66,160,72,288,132] 13 :=
  permutation_upper _ _ _ [66,132,288,96,136] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2451

theorem m3364_257 : Upper (D 10) (R 10) [66,160,72,288,257] 13 :=
  permutation_upper _ _ _ [66,132,288,96,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2451

theorem m3364_260 : Upper (D 10) (R 10) [66,160,72,288,260] 13 :=
  permutation_upper _ _ _ [66,132,96,144,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2428

theorem m3364_288 : Upper (D 10) (R 10) [66,160,72,288,288] 13 :=
  permutation_upper _ _ _ [66,160,72,288,160] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2470

def r3364 : Route 9 := (fun mask => (mask,id))

def c3364 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3364 : Upper (D 10) (R 10) [66,160,72,288] 13 := by
  apply FastRouting.sound _ _ [66,160,72,288] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r3364 c3364
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3364_5
  · exact m3364_33
  · exact m3364_36
  · exact m3364_129
  · exact m3364_132
  · exact u2470
  · exact m3364_257
  · exact m3364_260
  · exact m3364_288
  · exact u2471

theorem m3365_5 : Upper (D 10) (R 10) [66,160,72,384,5] 13 :=
  permutation_upper _ _ _ [6,72,80,160,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1544

theorem m3365_33 : Upper (D 10) (R 10) [66,160,72,384,33] 13 :=
  permutation_upper _ _ _ [34,68,160,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2180

theorem m3365_36 : Upper (D 10) (R 10) [66,160,72,384,36] 13 :=
  permutation_upper _ _ _ [34,68,384,80,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2230

theorem m3365_257 : Upper (D 10) (R 10) [66,160,72,384,257] 13 :=
  permutation_upper _ _ _ [66,132,288,144,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2457

theorem m3365_260 : Upper (D 10) (R 10) [66,160,72,384,260] 13 :=
  permutation_upper _ _ _ [66,132,320,144,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2463

def r3365 : Route 9 := (fun mask => (mask,id))

def c3365 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3365 : Upper (D 10) (R 10) [66,160,72,384] 13 := by
  apply FastRouting.sound _ _ [66,160,72,384] 13 (by decide) (choices 2) [5,33,36,257,260,288] r3365 c3365
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3365_5
  · exact m3365_33
  · exact m3365_36
  · exact m3365_257
  · exact m3365_260
  · exact u2472

theorem m3366_5 : Upper (D 10) (R 10) [66,160,80,288,5] 13 :=
  permutation_upper _ _ _ [6,65,72,160,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1441

theorem m3366_9 : Upper (D 10) (R 10) [66,160,80,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,288,65] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1648

theorem m3366_12 : Upper (D 10) (R 10) [66,160,80,288,12] 13 :=
  permutation_upper _ _ _ [6,65,160,80,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1493

theorem m3366_33 : Upper (D 10) (R 10) [66,160,80,288,33] 13 :=
  permutation_upper _ _ _ [34,68,160,65,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2172

theorem m3366_36 : Upper (D 10) (R 10) [66,160,80,288,36] 13 :=
  permutation_upper _ _ _ [34,65,72,160,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1973

theorem m3366_40 : Upper (D 10) (R 10) [66,160,80,288,40] 13 :=
  permutation_upper _ _ _ [34,96,129,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2281

theorem m3366_129 : Upper (D 10) (R 10) [66,160,80,288,129] 13 :=
  permutation_upper _ _ _ [66,132,72,160,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2418

theorem m3366_132 : Upper (D 10) (R 10) [66,160,80,288,132] 13 :=
  permutation_upper _ _ _ [66,129,72,160,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2402

theorem m3366_136 : Upper (D 10) (R 10) [66,160,80,288,136] 13 :=
  permutation_upper _ _ _ [66,132,288,80,160] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2448

theorem m3366_160 : Upper (D 10) (R 10) [66,160,80,288,160] 13 :=
  permutation_upper _ _ _ [66,160,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2469

theorem m3366_257 : Upper (D 10) (R 10) [66,160,80,288,257] 13 :=
  permutation_upper _ _ _ [66,132,72,288,160] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2422

theorem m3366_260 : Upper (D 10) (R 10) [66,160,80,288,260] 13 :=
  permutation_upper _ _ _ [66,129,72,288,160] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2405

theorem m3366_264 : Upper (D 10) (R 10) [66,160,80,288,264] 13 :=
  permutation_upper _ _ _ [66,96,129,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2389

theorem m3366_288 : Upper (D 10) (R 10) [66,160,80,288,288] 13 :=
  permutation_upper _ _ _ [66,160,72,288,160] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2470

theorem m3366_384 : Upper (D 10) (R 10) [66,160,80,288,384] 13 :=
  permutation_upper _ _ _ [66,160,72,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2472

def r3366 : Route 9 := (fun mask => (mask,id))

def c3366 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3366 : Upper (D 10) (R 10) [66,160,80,288] 13 := by
  apply FastRouting.sound _ _ [66,160,80,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,257,260,264,288,384] r3366 c3366
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3366_5
  · exact m3366_9
  · exact m3366_12
  · exact m3366_33
  · exact m3366_36
  · exact m3366_40
  · exact m3366_129
  · exact m3366_132
  · exact m3366_136
  · exact m3366_160
  · exact m3366_257
  · exact m3366_260
  · exact m3366_264
  · exact m3366_288
  · exact m3366_384

theorem m3367_5 : Upper (D 10) (R 10) [66,160,80,384,5] 13 :=
  permutation_upper _ _ _ [6,65,72,160,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1442

theorem m3367_9 : Upper (D 10) (R 10) [66,160,80,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,160,65] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1720

theorem m3367_12 : Upper (D 10) (R 10) [66,160,80,384,12] 13 :=
  permutation_upper _ _ _ [6,65,384,80,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1530

theorem m3367_33 : Upper (D 10) (R 10) [66,160,80,384,33] 13 :=
  permutation_upper _ _ _ [34,68,160,65,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2173

theorem m3367_36 : Upper (D 10) (R 10) [66,160,80,384,36] 13 :=
  permutation_upper _ _ _ [34,65,72,160,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1974

theorem m3367_40 : Upper (D 10) (R 10) [66,160,80,384,40] 13 :=
  permutation_upper _ _ _ [34,192,96,257,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2350

theorem m3367_257 : Upper (D 10) (R 10) [66,160,80,384,257] 13 :=
  permutation_upper _ _ _ [66,132,72,288,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2424

theorem m3367_260 : Upper (D 10) (R 10) [66,160,80,384,260] 13 :=
  permutation_upper _ _ _ [66,129,72,288,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2407

theorem m3367_264 : Upper (D 10) (R 10) [66,160,80,384,264] 13 :=
  permutation_upper _ _ _ [66,132,384,80,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2466

theorem m3367_288 : Upper (D 10) (R 10) [66,160,80,384,288] 13 :=
  permutation_upper _ _ _ [66,160,72,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2471

def r3367 : Route 9 := (fun mask => (mask,id))

def c3367 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3367 : Upper (D 10) (R 10) [66,160,80,384] 13 := by
  apply FastRouting.sound _ _ [66,160,80,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3367 c3367
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3367_5
  · exact m3367_9
  · exact m3367_12
  · exact m3367_33
  · exact m3367_36
  · exact m3367_40
  · exact m3367_257
  · exact m3367_260
  · exact m3367_264
  · exact m3367_288

theorem m3368_9 : Upper (D 10) (R 10) [66,160,96,132,9] 13 :=
  permutation_upper _ _ _ [6,72,144,160,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1575

theorem m3368_33 : Upper (D 10) (R 10) [66,160,96,132,33] 13 :=
  permutation_upper _ _ _ [34,68,160,96,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2182

theorem m3368_40 : Upper (D 10) (R 10) [66,160,96,132,40] 13 :=
  permutation_upper _ _ _ [34,68,160,96,136] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2182

theorem m3368_257 : Upper (D 10) (R 10) [66,160,96,132,257] 13 :=
  permutation_upper _ _ _ [66,132,288,160,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2458

theorem m3368_264 : Upper (D 10) (R 10) [66,160,96,132,264] 13 :=
  permutation_upper _ _ _ [66,132,288,160,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2458

def r3368 : Route 9 := (fun mask => (mask,id))

def c3368 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3368 : Upper (D 10) (R 10) [66,160,96,132] 13 := by
  apply FastRouting.sound _ _ [66,160,96,132] 13 (by decide) (choices 2) [9,33,40,257,264,288] r3368 c3368
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3368_9
  · exact m3368_33
  · exact m3368_40
  · exact m3368_257
  · exact m3368_264
  · exact u2473

theorem m3369_5 : Upper (D 10) (R 10) [66,160,96,144,5] 13 :=
  permutation_upper _ _ _ [6,72,96,160,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1556

theorem m3369_9 : Upper (D 10) (R 10) [66,160,96,144,9] 13 :=
  permutation_upper _ _ _ [6,65,136,96,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1459

theorem m3369_12 : Upper (D 10) (R 10) [66,160,96,144,12] 13 :=
  permutation_upper _ _ _ [6,65,160,96,136] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1495

theorem m3369_33 : Upper (D 10) (R 10) [66,160,96,144,33] 13 :=
  permutation_upper _ _ _ [34,68,160,96,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2181

theorem m3369_36 : Upper (D 10) (R 10) [66,160,96,144,36] 13 :=
  permutation_upper _ _ _ [34,96,72,160,129] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2268

theorem m3369_40 : Upper (D 10) (R 10) [66,160,96,144,40] 13 :=
  permutation_upper _ _ _ [34,65,96,132,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1977

theorem m3369_257 : Upper (D 10) (R 10) [66,160,96,144,257] 13 :=
  permutation_upper _ _ _ [66,132,264,96,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2444

theorem m3369_260 : Upper (D 10) (R 10) [66,160,96,144,260] 13 :=
  permutation_upper _ _ _ [66,132,288,96,264] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2453

theorem m3369_264 : Upper (D 10) (R 10) [66,160,96,144,264] 13 :=
  permutation_upper _ _ _ [66,129,96,260,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2411

def r3369 : Route 9 := (fun mask => (mask,id))

def c3369 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3369 : Upper (D 10) (R 10) [66,160,96,144] 13 := by
  apply FastRouting.sound _ _ [66,160,96,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3369 c3369
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3369_5
  · exact m3369_9
  · exact m3369_12
  · exact m3369_33
  · exact m3369_36
  · exact m3369_40
  · exact m3369_257
  · exact m3369_260
  · exact m3369_264
  · exact u2474

def b3370 : PairBound 9 := { available := 285, camps := [{ cop := 1, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 67 162 100 168 285 317 349 413 285), lower := (rows 67 162 100 168 16 32 64 128 256), losses := [] }

theorem u3370 : Upper (D 10) (R 10) [66,160,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3370 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3371_9 : Upper (D 10) (R 10) [66,160,96,260,9] 13 :=
  permutation_upper _ _ _ [6,72,144,160,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1577

theorem m3371_33 : Upper (D 10) (R 10) [66,160,96,260,33] 13 :=
  permutation_upper _ _ _ [34,68,160,96,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2184

theorem m3371_40 : Upper (D 10) (R 10) [66,160,96,260,40] 13 :=
  permutation_upper _ _ _ [34,68,160,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2191

theorem m3371_129 : Upper (D 10) (R 10) [66,160,96,260,129] 13 :=
  permutation_upper _ _ _ [66,132,96,160,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2430

theorem m3371_136 : Upper (D 10) (R 10) [66,160,96,260,136] 13 :=
  permutation_upper _ _ _ [66,132,288,96,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2453

theorem m3371_160 : Upper (D 10) (R 10) [66,160,96,260,160] 13 :=
  permutation_upper _ _ _ [66,160,96,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2475

theorem m3371_257 : Upper (D 10) (R 10) [66,160,96,260,257] 13 :=
  permutation_upper _ _ _ [66,132,288,80,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2448

theorem m3371_264 : Upper (D 10) (R 10) [66,160,96,260,264] 13 :=
  permutation_upper _ _ _ [66,68,160,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2381

theorem m3371_288 : Upper (D 10) (R 10) [66,160,96,260,288] 13 :=
  permutation_upper _ _ _ [66,160,96,144,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2474

def r3371 : Route 9 := (fun mask => (mask,id))

def c3371 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3371 : Upper (D 10) (R 10) [66,160,96,260] 13 := by
  apply FastRouting.sound _ _ [66,160,96,260] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3371 c3371
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3371_9
  · exact m3371_33
  · exact m3371_40
  · exact m3371_129
  · exact m3371_136
  · exact m3371_160
  · exact m3371_257
  · exact m3371_264
  · exact m3371_288
  · exact u2477

theorem m3372_5 : Upper (D 10) (R 10) [66,160,96,272,5] 13 :=
  permutation_upper _ _ _ [6,72,96,160,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1557

theorem m3372_9 : Upper (D 10) (R 10) [66,160,96,272,9] 13 :=
  permutation_upper _ _ _ [6,65,136,288,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1472

theorem m3372_12 : Upper (D 10) (R 10) [66,160,96,272,12] 13 :=
  permutation_upper _ _ _ [6,65,160,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1500

theorem m3372_33 : Upper (D 10) (R 10) [66,160,96,272,33] 13 :=
  permutation_upper _ _ _ [34,68,160,96,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2183

theorem m3372_36 : Upper (D 10) (R 10) [66,160,96,272,36] 13 :=
  permutation_upper _ _ _ [34,96,72,160,257] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2269

theorem m3372_40 : Upper (D 10) (R 10) [66,160,96,272,40] 13 :=
  permutation_upper _ _ _ [34,65,136,288,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1997

theorem m3372_129 : Upper (D 10) (R 10) [66,160,96,272,129] 13 :=
  permutation_upper _ _ _ [66,132,96,160,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2429

theorem m3372_132 : Upper (D 10) (R 10) [66,160,96,272,132] 13 :=
  permutation_upper _ _ _ [66,132,288,160,264] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2458

theorem m3372_136 : Upper (D 10) (R 10) [66,160,96,272,136] 13 :=
  permutation_upper _ _ _ [66,129,96,260,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2411

theorem m3372_160 : Upper (D 10) (R 10) [66,160,96,272,160] 13 :=
  permutation_upper _ _ _ [66,160,96,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2476

theorem m3372_257 : Upper (D 10) (R 10) [66,160,96,272,257] 13 :=
  permutation_upper _ _ _ [66,68,136,288,160] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2375

theorem m3372_260 : Upper (D 10) (R 10) [66,160,96,272,260] 13 :=
  permutation_upper _ _ _ [66,68,160,144,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2381

theorem m3372_264 : Upper (D 10) (R 10) [66,160,96,272,264] 13 :=
  permutation_upper _ _ _ [66,65,136,288,160] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2364

theorem m3372_288 : Upper (D 10) (R 10) [66,160,96,272,288] 13 :=
  permutation_upper _ _ _ [66,96,136,288,160] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2396

def r3372 : Route 9 := (fun mask => (mask,id))

def c3372 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3372 : Upper (D 10) (R 10) [66,160,96,272] 13 := by
  apply FastRouting.sound _ _ [66,160,96,272] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,257,260,264,288,384] r3372 c3372
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3372_5
  · exact m3372_9
  · exact m3372_12
  · exact m3372_33
  · exact m3372_36
  · exact m3372_40
  · exact m3372_129
  · exact m3372_132
  · exact m3372_136
  · exact m3372_160
  · exact m3372_257
  · exact m3372_260
  · exact m3372_264
  · exact m3372_288
  · exact u2478

theorem m3373_5 : Upper (D 10) (R 10) [66,160,96,288,5] 13 :=
  permutation_upper _ _ _ [6,72,96,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1558

theorem m3373_9 : Upper (D 10) (R 10) [66,160,96,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,288,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1649

theorem m3373_12 : Upper (D 10) (R 10) [66,160,96,288,12] 13 :=
  permutation_upper _ _ _ [6,96,160,80,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1759

theorem m3373_129 : Upper (D 10) (R 10) [66,160,96,288,129] 13 :=
  permutation_upper _ _ _ [66,132,96,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2431

theorem m3373_132 : Upper (D 10) (R 10) [66,160,96,288,132] 13 :=
  permutation_upper _ _ _ [66,160,96,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2473

theorem m3373_136 : Upper (D 10) (R 10) [66,160,96,288,136] 13 :=
  permutation_upper _ _ _ [66,160,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2474

theorem m3373_257 : Upper (D 10) (R 10) [66,160,96,288,257] 13 :=
  permutation_upper _ _ _ [66,132,288,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2452

theorem m3373_260 : Upper (D 10) (R 10) [66,160,96,288,260] 13 :=
  permutation_upper _ _ _ [66,160,96,144,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2474

theorem m3373_264 : Upper (D 10) (R 10) [66,160,96,288,264] 13 :=
  permutation_upper _ _ _ [66,96,136,288,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2396

def r3373 : Route 9 := (fun mask => (mask,id))

def c3373 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3373 : Upper (D 10) (R 10) [66,160,96,288] 13 := by
  apply FastRouting.sound _ _ [66,160,96,288] 13 (by decide) (choices 2) [5,9,12,129,132,136,257,260,264,384] r3373 c3373
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3373_5
  · exact m3373_9
  · exact m3373_12
  · exact m3373_129
  · exact m3373_132
  · exact m3373_136
  · exact m3373_257
  · exact m3373_260
  · exact m3373_264
  · exact u2479

theorem m3374_5 : Upper (D 10) (R 10) [66,160,96,384,5] 13 :=
  permutation_upper _ _ _ [6,72,96,160,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1559

theorem m3374_9 : Upper (D 10) (R 10) [66,160,96,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,160,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1721

theorem m3374_12 : Upper (D 10) (R 10) [66,160,96,384,12] 13 :=
  permutation_upper _ _ _ [6,96,384,80,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1816

theorem m3374_33 : Upper (D 10) (R 10) [66,160,96,384,33] 13 :=
  permutation_upper _ _ _ [34,68,160,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2185

theorem m3374_36 : Upper (D 10) (R 10) [66,160,96,384,36] 13 :=
  permutation_upper _ _ _ [34,96,72,160,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2271

theorem m3374_40 : Upper (D 10) (R 10) [66,160,96,384,40] 13 :=
  permutation_upper _ _ _ [34,192,96,260,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2355

theorem m3374_257 : Upper (D 10) (R 10) [66,160,96,384,257] 13 :=
  permutation_upper _ _ _ [66,132,288,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2460

theorem m3374_260 : Upper (D 10) (R 10) [66,160,96,384,260] 13 :=
  permutation_upper _ _ _ [66,160,96,260,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2477

theorem m3374_264 : Upper (D 10) (R 10) [66,160,96,384,264] 13 :=
  permutation_upper _ _ _ [66,160,96,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2478

theorem m3374_288 : Upper (D 10) (R 10) [66,160,96,384,288] 13 :=
  permutation_upper _ _ _ [66,160,96,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2479

def r3374 : Route 9 := (fun mask => (mask,id))

def c3374 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3374 : Upper (D 10) (R 10) [66,160,96,384] 13 := by
  apply FastRouting.sound _ _ [66,160,96,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3374 c3374
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3374_5
  · exact m3374_9
  · exact m3374_12
  · exact m3374_33
  · exact m3374_36
  · exact m3374_40
  · exact m3374_257
  · exact m3374_260
  · exact m3374_264
  · exact m3374_288

theorem m3375_5 : Upper (D 10) (R 10) [66,160,136,320,5] 13 :=
  permutation_upper _ _ _ [6,72,144,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1578

theorem m3375_33 : Upper (D 10) (R 10) [66,160,136,320,33] 13 :=
  permutation_upper _ _ _ [34,68,160,144,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2192

theorem m3375_36 : Upper (D 10) (R 10) [66,160,136,320,36] 13 :=
  permutation_upper _ _ _ [34,68,384,96,136] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2233

theorem m3375_257 : Upper (D 10) (R 10) [66,160,136,320,257] 13 :=
  permutation_upper _ _ _ [66,132,288,192,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2461

theorem m3375_260 : Upper (D 10) (R 10) [66,160,136,320,260] 13 :=
  permutation_upper _ _ _ [66,132,320,160,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2464

def r3375 : Route 9 := (fun mask => (mask,id))

def c3375 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3375 : Upper (D 10) (R 10) [66,160,136,320] 13 := by
  apply FastRouting.sound _ _ [66,160,136,320] 13 (by decide) (choices 2) [5,33,36,257,260,288] r3375 c3375
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3375_5
  · exact m3375_33
  · exact m3375_36
  · exact m3375_257
  · exact m3375_260
  · exact u2480

theorem m3376_5 : Upper (D 10) (R 10) [66,160,144,288,5] 13 :=
  permutation_upper _ _ _ [6,65,136,96,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1460

theorem m3376_9 : Upper (D 10) (R 10) [66,160,144,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,288,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1653

theorem m3376_12 : Upper (D 10) (R 10) [66,160,144,288,12] 13 :=
  permutation_upper _ _ _ [6,65,160,96,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1496

theorem m3376_33 : Upper (D 10) (R 10) [66,160,144,288,33] 13 :=
  permutation_upper _ _ _ [34,68,160,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2187

theorem m3376_36 : Upper (D 10) (R 10) [66,160,144,288,36] 13 :=
  permutation_upper _ _ _ [34,65,96,132,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1979

theorem m3376_40 : Upper (D 10) (R 10) [66,160,144,288,40] 13 :=
  permutation_upper _ _ _ [34,96,129,160,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2284

theorem m3376_65 : Upper (D 10) (R 10) [66,160,144,288,65] 13 :=
  permutation_upper _ _ _ [66,68,160,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2379

theorem m3376_68 : Upper (D 10) (R 10) [66,160,144,288,68] 13 :=
  permutation_upper _ _ _ [66,129,72,160,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2402

theorem m3376_72 : Upper (D 10) (R 10) [66,160,144,288,72] 13 :=
  permutation_upper _ _ _ [66,132,288,96,136] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2451

theorem m3376_96 : Upper (D 10) (R 10) [66,160,144,288,96] 13 :=
  permutation_upper _ _ _ [66,160,96,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2473

theorem m3376_257 : Upper (D 10) (R 10) [66,160,144,288,257] 13 :=
  permutation_upper _ _ _ [66,132,264,96,160] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2443

theorem m3376_260 : Upper (D 10) (R 10) [66,160,144,288,260] 13 :=
  permutation_upper _ _ _ [66,129,96,160,260] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2409

theorem m3376_264 : Upper (D 10) (R 10) [66,160,144,288,264] 13 :=
  permutation_upper _ _ _ [66,96,129,160,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2391

theorem m3376_288 : Upper (D 10) (R 10) [66,160,144,288,288] 13 :=
  permutation_upper _ _ _ [66,160,96,160,260] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2475

theorem m3376_320 : Upper (D 10) (R 10) [66,160,144,288,320] 13 :=
  permutation_upper _ _ _ [66,160,136,320,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2480

def r3376 : Route 9 := (fun mask => (mask,id))

def c3376 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3376 : Upper (D 10) (R 10) [66,160,144,288] 13 := by
  apply FastRouting.sound _ _ [66,160,144,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,257,260,264,288,320] r3376 c3376
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3376_5
  · exact m3376_9
  · exact m3376_12
  · exact m3376_33
  · exact m3376_36
  · exact m3376_40
  · exact m3376_65
  · exact m3376_68
  · exact m3376_72
  · exact m3376_96
  · exact m3376_257
  · exact m3376_260
  · exact m3376_264
  · exact m3376_288
  · exact m3376_320

theorem m3377_5 : Upper (D 10) (R 10) [66,160,144,320,5] 13 :=
  permutation_upper _ _ _ [6,65,136,96,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1461

theorem m3377_9 : Upper (D 10) (R 10) [66,160,144,320,9] 13 :=
  permutation_upper _ _ _ [6,72,192,288,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1689

theorem m3377_12 : Upper (D 10) (R 10) [66,160,144,320,12] 13 :=
  permutation_upper _ _ _ [6,65,384,96,136] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1531

theorem m3377_33 : Upper (D 10) (R 10) [66,160,144,320,33] 13 :=
  permutation_upper _ _ _ [34,68,160,129,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2188

theorem m3377_36 : Upper (D 10) (R 10) [66,160,144,320,36] 13 :=
  permutation_upper _ _ _ [34,65,96,132,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1980

theorem m3377_40 : Upper (D 10) (R 10) [66,160,144,320,40] 13 :=
  permutation_upper _ _ _ [34,192,72,288,257] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2341

theorem m3377_257 : Upper (D 10) (R 10) [66,160,144,320,257] 13 :=
  permutation_upper _ _ _ [66,132,264,96,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2445

theorem m3377_260 : Upper (D 10) (R 10) [66,160,144,320,260] 13 :=
  permutation_upper _ _ _ [66,129,96,260,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2412

theorem m3377_264 : Upper (D 10) (R 10) [66,160,144,320,264] 13 :=
  permutation_upper _ _ _ [66,132,384,96,264] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2467

theorem m3377_288 : Upper (D 10) (R 10) [66,160,144,320,288] 13 :=
  permutation_upper _ _ _ [66,160,96,260,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2477

def r3377 : Route 9 := (fun mask => (mask,id))

def c3377 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3377 : Upper (D 10) (R 10) [66,160,144,320] 13 := by
  apply FastRouting.sound _ _ [66,160,144,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3377 c3377
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3377_5
  · exact m3377_9
  · exact m3377_12
  · exact m3377_33
  · exact m3377_36
  · exact m3377_40
  · exact m3377_257
  · exact m3377_260
  · exact m3377_264
  · exact m3377_288

def b3378 : PairBound 9 := { available := 377, camps := [{ cop := 1, region := 4, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 67 162 164 268 377 377 377 505 377), lower := (rows 67 162 164 268 16 32 64 128 256), losses := [] }

theorem u3378 : Upper (D 10) (R 10) [66,160,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3378 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3379 : PairBound 9 := { available := 349, camps := [{ cop := 1, region := 4, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 67 162 164 296 349 381 349 477 349), lower := (rows 67 162 164 296 16 32 64 128 256), losses := [] }

theorem u3379 : Upper (D 10) (R 10) [66,160,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3379 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3380 : PairBound 9 := { available := 317, camps := [{ cop := 1, region := 4, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 67 162 164 328 317 317 381 445 317), lower := (rows 67 162 164 328 16 32 64 128 256), losses := [] }

theorem u3380 : Upper (D 10) (R 10) [66,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3380 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3381_9 : Upper (D 10) (R 10) [66,160,192,260,9] 13 :=
  permutation_upper _ _ _ [6,72,144,288,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1585

theorem m3381_33 : Upper (D 10) (R 10) [66,160,192,260,33] 13 :=
  permutation_upper _ _ _ [34,68,160,192,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2197

theorem m3381_40 : Upper (D 10) (R 10) [66,160,192,260,40] 13 :=
  permutation_upper _ _ _ [34,68,384,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2240

theorem m3381_257 : Upper (D 10) (R 10) [66,160,192,260,257] 13 :=
  permutation_upper _ _ _ [66,132,288,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2450

theorem m3381_264 : Upper (D 10) (R 10) [66,160,192,260,264] 13 :=
  permutation_upper _ _ _ [66,68,384,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2387

def r3381 : Route 9 := (fun mask => (mask,id))

def c3381 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3381 : Upper (D 10) (R 10) [66,160,192,260] 13 := by
  apply FastRouting.sound _ _ [66,160,192,260] 13 (by decide) (choices 2) [9,33,40,257,264,288] r3381 c3381
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3381_9
  · exact m3381_33
  · exact m3381_40
  · exact m3381_257
  · exact m3381_264
  · exact u2483

theorem m3382_5 : Upper (D 10) (R 10) [66,160,192,272,5] 13 :=
  permutation_upper _ _ _ [6,72,192,160,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1678

theorem m3382_9 : Upper (D 10) (R 10) [66,160,192,272,9] 13 :=
  permutation_upper _ _ _ [6,65,136,288,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1476

theorem m3382_12 : Upper (D 10) (R 10) [66,160,192,272,12] 13 :=
  permutation_upper _ _ _ [6,65,384,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1534

theorem m3382_33 : Upper (D 10) (R 10) [66,160,192,272,33] 13 :=
  permutation_upper _ _ _ [34,68,160,192,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2196

theorem m3382_36 : Upper (D 10) (R 10) [66,160,192,272,36] 13 :=
  permutation_upper _ _ _ [34,192,72,160,257] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2324

theorem m3382_40 : Upper (D 10) (R 10) [66,160,192,272,40] 13 :=
  permutation_upper _ _ _ [34,65,136,288,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2001

theorem m3382_257 : Upper (D 10) (R 10) [66,160,192,272,257] 13 :=
  permutation_upper _ _ _ [66,68,136,288,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2377

theorem m3382_260 : Upper (D 10) (R 10) [66,160,192,272,260] 13 :=
  permutation_upper _ _ _ [66,68,384,144,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2387

theorem m3382_264 : Upper (D 10) (R 10) [66,160,192,272,264] 13 :=
  permutation_upper _ _ _ [66,65,136,288,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2365

theorem m3382_288 : Upper (D 10) (R 10) [66,160,192,272,288] 13 :=
  permutation_upper _ _ _ [66,96,136,288,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2397

def r3382 : Route 9 := (fun mask => (mask,id))

def c3382 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3382 : Upper (D 10) (R 10) [66,160,192,272] 13 := by
  apply FastRouting.sound _ _ [66,160,192,272] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3382 c3382
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3382_5
  · exact m3382_9
  · exact m3382_12
  · exact m3382_33
  · exact m3382_36
  · exact m3382_40
  · exact m3382_257
  · exact m3382_260
  · exact m3382_264
  · exact m3382_288

theorem m3383_5 : Upper (D 10) (R 10) [66,160,192,288,5] 13 :=
  permutation_upper _ _ _ [6,72,192,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1679

theorem m3383_9 : Upper (D 10) (R 10) [66,160,192,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,288,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1655

theorem m3383_12 : Upper (D 10) (R 10) [66,160,192,288,12] 13 :=
  permutation_upper _ _ _ [6,96,384,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1824

theorem m3383_33 : Upper (D 10) (R 10) [66,160,192,288,33] 13 :=
  permutation_upper _ _ _ [34,68,160,192,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2198

theorem m3383_36 : Upper (D 10) (R 10) [66,160,192,288,36] 13 :=
  permutation_upper _ _ _ [34,192,72,160,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2326

theorem m3383_40 : Upper (D 10) (R 10) [66,160,192,288,40] 13 :=
  permutation_upper _ _ _ [34,96,136,288,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2297

theorem m3383_257 : Upper (D 10) (R 10) [66,160,192,288,257] 13 :=
  permutation_upper _ _ _ [66,132,288,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2455

theorem m3383_260 : Upper (D 10) (R 10) [66,160,192,288,260] 13 :=
  permutation_upper _ _ _ [66,160,192,260,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2483

theorem m3383_264 : Upper (D 10) (R 10) [66,160,192,288,264] 13 :=
  permutation_upper _ _ _ [66,96,136,288,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2397

def r3383 : Route 9 := (fun mask => (mask,id))

def c3383 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3383 : Upper (D 10) (R 10) [66,160,192,288] 13 := by
  apply FastRouting.sound _ _ [66,160,192,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3383 c3383
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3383_5
  · exact m3383_9
  · exact m3383_12
  · exact m3383_33
  · exact m3383_36
  · exact m3383_40
  · exact m3383_257
  · exact m3383_260
  · exact m3383_264
  · exact u2484

def b3384 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 243, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 162 268 328 181 181 245 181 437), lower := (rows 67 162 268 328 16 32 64 128 256), losses := [] }

theorem u3384 : Upper (D 10) (R 10) [66,160,264,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3384 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3385 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 243, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 162 268 392 117 117 117 245 373), lower := (rows 67 162 268 392 16 32 64 128 256), losses := [] }

theorem u3385 : Upper (D 10) (R 10) [66,160,264,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3385 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3386_5 : Upper (D 10) (R 10) [66,160,272,288,5] 13 :=
  permutation_upper _ _ _ [6,65,136,288,96] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1471

theorem m3386_9 : Upper (D 10) (R 10) [66,160,272,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,288,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1650

theorem m3386_12 : Upper (D 10) (R 10) [66,160,272,288,12] 13 :=
  permutation_upper _ _ _ [6,65,96,144,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1447

theorem m3386_33 : Upper (D 10) (R 10) [66,160,272,288,33] 13 :=
  permutation_upper _ _ _ [34,68,160,257,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2200

theorem m3386_36 : Upper (D 10) (R 10) [66,160,272,288,36] 13 :=
  permutation_upper _ _ _ [34,65,96,144,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1982

theorem m3386_40 : Upper (D 10) (R 10) [66,160,272,288,40] 13 :=
  permutation_upper _ _ _ [34,96,65,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2257

theorem m3386_65 : Upper (D 10) (R 10) [66,160,272,288,65] 13 :=
  permutation_upper _ _ _ [66,68,160,257,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2382

theorem m3386_68 : Upper (D 10) (R 10) [66,160,272,288,68] 13 :=
  permutation_upper _ _ _ [66,129,72,288,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2405

theorem m3386_72 : Upper (D 10) (R 10) [66,160,272,288,72] 13 :=
  permutation_upper _ _ _ [66,132,96,144,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2428

theorem m3386_96 : Upper (D 10) (R 10) [66,160,272,288,96] 13 :=
  permutation_upper _ _ _ [66,160,96,144,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2474

theorem m3386_129 : Upper (D 10) (R 10) [66,160,272,288,129] 13 :=
  permutation_upper _ _ _ [66,132,96,257,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2432

theorem m3386_132 : Upper (D 10) (R 10) [66,160,272,288,132] 13 :=
  permutation_upper _ _ _ [66,129,96,160,260] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2409

theorem m3386_136 : Upper (D 10) (R 10) [66,160,272,288,136] 13 :=
  permutation_upper _ _ _ [66,132,96,160,264] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2430

theorem m3386_160 : Upper (D 10) (R 10) [66,160,272,288,160] 13 :=
  permutation_upper _ _ _ [66,160,96,160,264] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2476

theorem m3386_192 : Upper (D 10) (R 10) [66,160,272,288,192] 13 :=
  permutation_upper _ _ _ [66,160,192,260,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2483

def r3386 : Route 9 := (fun mask => (mask,id))

def c3386 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3386 : Upper (D 10) (R 10) [66,160,272,288] 13 := by
  apply FastRouting.sound _ _ [66,160,272,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r3386 c3386
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3386_5
  · exact m3386_9
  · exact m3386_12
  · exact m3386_33
  · exact m3386_36
  · exact m3386_40
  · exact m3386_65
  · exact m3386_68
  · exact m3386_72
  · exact m3386_96
  · exact m3386_129
  · exact m3386_132
  · exact m3386_136
  · exact m3386_160
  · exact m3386_192

theorem m3387_5 : Upper (D 10) (R 10) [66,160,272,320,5] 13 :=
  permutation_upper _ _ _ [6,65,136,288,192] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1473

theorem m3387_9 : Upper (D 10) (R 10) [66,160,272,320,9] 13 :=
  permutation_upper _ _ _ [6,72,192,288,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1687

theorem m3387_12 : Upper (D 10) (R 10) [66,160,272,320,12] 13 :=
  permutation_upper _ _ _ [6,65,192,144,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1518

theorem m3387_33 : Upper (D 10) (R 10) [66,160,272,320,33] 13 :=
  permutation_upper _ _ _ [34,68,160,257,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2201

theorem m3387_36 : Upper (D 10) (R 10) [66,160,272,320,36] 13 :=
  permutation_upper _ _ _ [34,65,136,288,192] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1998

theorem m3387_40 : Upper (D 10) (R 10) [66,160,272,320,40] 13 :=
  permutation_upper _ _ _ [34,192,65,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2312

theorem m3387_129 : Upper (D 10) (R 10) [66,160,272,320,129] 13 :=
  permutation_upper _ _ _ [66,132,96,257,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2433

theorem m3387_132 : Upper (D 10) (R 10) [66,160,272,320,132] 13 :=
  permutation_upper _ _ _ [66,129,96,260,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2412

theorem m3387_136 : Upper (D 10) (R 10) [66,160,272,320,136] 13 :=
  permutation_upper _ _ _ [66,132,320,160,264] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2464

theorem m3387_160 : Upper (D 10) (R 10) [66,160,272,320,160] 13 :=
  permutation_upper _ _ _ [66,160,160,260,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2481

def r3387 : Route 9 := (fun mask => (mask,id))

def c3387 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u3387 : Upper (D 10) (R 10) [66,160,272,320] 13 := by
  apply FastRouting.sound _ _ [66,160,272,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r3387 c3387
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3387_5
  · exact m3387_9
  · exact m3387_12
  · exact m3387_33
  · exact m3387_36
  · exact m3387_40
  · exact m3387_129
  · exact m3387_132
  · exact m3387_136
  · exact m3387_160

theorem m3388_5 : Upper (D 10) (R 10) [66,160,272,384,5] 13 :=
  permutation_upper _ _ _ [6,65,136,288,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1475

theorem m3388_9 : Upper (D 10) (R 10) [66,160,272,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,160,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1722

theorem m3388_12 : Upper (D 10) (R 10) [66,160,272,384,12] 13 :=
  permutation_upper _ _ _ [6,65,192,160,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1519

theorem m3388_33 : Upper (D 10) (R 10) [66,160,272,384,33] 13 :=
  permutation_upper _ _ _ [34,68,160,257,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2202

theorem m3388_36 : Upper (D 10) (R 10) [66,160,272,384,36] 13 :=
  permutation_upper _ _ _ [34,65,136,288,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2000

theorem m3388_40 : Upper (D 10) (R 10) [66,160,272,384,40] 13 :=
  permutation_upper _ _ _ [34,192,65,160,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2314

theorem m3388_65 : Upper (D 10) (R 10) [66,160,272,384,65] 13 :=
  permutation_upper _ _ _ [66,68,160,257,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2383

theorem m3388_68 : Upper (D 10) (R 10) [66,160,272,384,68] 13 :=
  permutation_upper _ _ _ [66,129,72,288,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2407

theorem m3388_72 : Upper (D 10) (R 10) [66,160,272,384,72] 13 :=
  permutation_upper _ _ _ [66,132,320,144,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2463

theorem m3388_96 : Upper (D 10) (R 10) [66,160,272,384,96] 13 :=
  permutation_upper _ _ _ [66,160,96,260,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2477

def r3388 : Route 9 := (fun mask => (mask,id))

def c3388 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u3388 : Upper (D 10) (R 10) [66,160,272,384] 13 := by
  apply FastRouting.sound _ _ [66,160,272,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r3388 c3388
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3388_5
  · exact m3388_9
  · exact m3388_12
  · exact m3388_33
  · exact m3388_36
  · exact m3388_40
  · exact m3388_65
  · exact m3388_68
  · exact m3388_72
  · exact m3388_96

def b3389 : PairBound 9 := { available := 221, camps := [{ cop := 2, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 67 162 292 296 221 253 221 221 477), lower := (rows 67 162 292 296 16 32 64 128 256), losses := [] }

theorem u3389 : Upper (D 10) (R 10) [66,160,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3389 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3390_5 : Upper (D 10) (R 10) [66,160,288,320,5] 13 :=
  permutation_upper _ _ _ [6,72,160,288,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1652

theorem m3390_9 : Upper (D 10) (R 10) [66,160,288,320,9] 13 :=
  permutation_upper _ _ _ [6,72,192,288,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1688

theorem m3390_12 : Upper (D 10) (R 10) [66,160,288,320,12] 13 :=
  permutation_upper _ _ _ [6,96,192,144,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1789

theorem m3390_33 : Upper (D 10) (R 10) [66,160,288,320,33] 13 :=
  permutation_upper _ _ _ [34,68,160,288,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2207

theorem m3390_36 : Upper (D 10) (R 10) [66,160,288,320,36] 13 :=
  permutation_upper _ _ _ [34,96,136,288,192] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2295

theorem m3390_40 : Upper (D 10) (R 10) [66,160,288,320,40] 13 :=
  permutation_upper _ _ _ [34,192,72,288,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2340

theorem m3390_129 : Upper (D 10) (R 10) [66,160,288,320,129] 13 :=
  permutation_upper _ _ _ [66,132,96,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2434

theorem m3390_132 : Upper (D 10) (R 10) [66,160,288,320,132] 13 :=
  permutation_upper _ _ _ [66,160,96,260,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2477

theorem m3390_136 : Upper (D 10) (R 10) [66,160,288,320,136] 13 :=
  permutation_upper _ _ _ [66,160,136,320,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2480

theorem m3390_160 : Upper (D 10) (R 10) [66,160,288,320,160] 13 :=
  permutation_upper _ _ _ [66,160,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2482

def r3390 : Route 9 := (fun mask => (mask,id))

def c3390 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u3390 : Upper (D 10) (R 10) [66,160,288,320] 13 := by
  apply FastRouting.sound _ _ [66,160,288,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r3390 c3390
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3390_5
  · exact m3390_9
  · exact m3390_12
  · exact m3390_33
  · exact m3390_36
  · exact m3390_40
  · exact m3390_129
  · exact m3390_132
  · exact m3390_136
  · exact m3390_160

theorem m3391_5 : Upper (D 10) (R 10) [66,160,288,384,5] 13 :=
  permutation_upper _ _ _ [6,72,160,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1656

theorem m3391_9 : Upper (D 10) (R 10) [66,160,288,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1723

theorem m3391_12 : Upper (D 10) (R 10) [66,160,288,384,12] 13 :=
  permutation_upper _ _ _ [6,96,192,160,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1791

theorem m3391_33 : Upper (D 10) (R 10) [66,160,288,384,33] 13 :=
  permutation_upper _ _ _ [34,68,160,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2208

theorem m3391_36 : Upper (D 10) (R 10) [66,160,288,384,36] 13 :=
  permutation_upper _ _ _ [34,96,136,288,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2296

theorem m3391_40 : Upper (D 10) (R 10) [66,160,288,384,40] 13 :=
  permutation_upper _ _ _ [34,192,96,160,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2349

theorem m3391_65 : Upper (D 10) (R 10) [66,160,288,384,65] 13 :=
  permutation_upper _ _ _ [66,68,160,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2384

theorem m3391_68 : Upper (D 10) (R 10) [66,160,288,384,68] 13 :=
  permutation_upper _ _ _ [66,160,72,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2471

theorem m3391_72 : Upper (D 10) (R 10) [66,160,288,384,72] 13 :=
  permutation_upper _ _ _ [66,160,72,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2472

theorem m3391_96 : Upper (D 10) (R 10) [66,160,288,384,96] 13 :=
  permutation_upper _ _ _ [66,160,96,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2479

def r3391 : Route 9 := (fun mask => (mask,id))

def c3391 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u3391 : Upper (D 10) (R 10) [66,160,288,384] 13 := by
  apply FastRouting.sound _ _ [66,160,288,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r3391 c3391
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3391_5
  · exact m3391_9
  · exact m3391_12
  · exact m3391_33
  · exact m3391_36
  · exact m3391_40
  · exact m3391_65
  · exact m3391_68
  · exact m3391_72
  · exact m3391_96

theorem m3392_5 : Upper (D 10) (R 10) [66,160,320,384,5] 13 :=
  permutation_upper _ _ _ [6,72,192,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1690

theorem m3392_9 : Upper (D 10) (R 10) [66,160,320,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1724

theorem m3392_12 : Upper (D 10) (R 10) [66,160,320,384,12] 13 :=
  permutation_upper _ _ _ [6,192,320,144,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1841

theorem m3392_33 : Upper (D 10) (R 10) [66,160,320,384,33] 13 :=
  permutation_upper _ _ _ [34,68,160,320,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2209

theorem m3392_36 : Upper (D 10) (R 10) [66,160,320,384,36] 13 :=
  permutation_upper _ _ _ [34,192,72,288,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2344

theorem m3392_40 : Upper (D 10) (R 10) [66,160,320,384,40] 13 :=
  permutation_upper _ _ _ [34,192,96,260,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2356

def r3392 : Route 9 := (fun mask => (mask,id))

def c3392 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3392 : Upper (D 10) (R 10) [66,160,320,384] 13 := by
  apply FastRouting.sound _ _ [66,160,320,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r3392 c3392
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3392_5
  · exact m3392_9
  · exact m3392_12
  · exact m3392_33
  · exact m3392_36
  · exact m3392_40

def b3393 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 194 164 296 317 317 381 445 317), lower := (rows 67 194 164 296 16 32 64 128 256), losses := [] }

theorem u3393 : Upper (D 10) (R 10) [66,192,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3393 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3394 : PairBound 9 := { available := 61, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 194 292 392 61 61 125 189 317), lower := (rows 67 194 292 392 16 32 64 128 256), losses := [] }

theorem u3394 : Upper (D 10) (R 10) [66,192,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3394 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3395 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 67 386 76 392 53 53 117 181 309), lower := (rows 67 386 76 392 16 32 64 128 256), losses := [] }

theorem u3395 : Upper (D 10) (R 10) [66,384,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3395 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3396_5 : Upper (D 10) (R 10) [66,384,80,160,5] 13 :=
  permutation_upper _ _ _ [6,65,72,384,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1443

theorem m3396_9 : Upper (D 10) (R 10) [66,384,80,160,9] 13 :=
  permutation_upper _ _ _ [6,72,160,384,65] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1662

theorem m3396_12 : Upper (D 10) (R 10) [66,384,80,160,12] 13 :=
  permutation_upper _ _ _ [6,65,160,80,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1494

theorem m3396_33 : Upper (D 10) (R 10) [66,384,80,160,33] 13 :=
  permutation_upper _ _ _ [34,68,384,65,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2227

theorem m3396_36 : Upper (D 10) (R 10) [66,384,80,160,36] 13 :=
  permutation_upper _ _ _ [34,65,72,384,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1976

theorem m3396_40 : Upper (D 10) (R 10) [66,384,80,160,40] 13 :=
  permutation_upper _ _ _ [34,96,129,144,320] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2282

theorem m3396_257 : Upper (D 10) (R 10) [66,384,80,160,257] 13 :=
  permutation_upper _ _ _ [66,132,72,384,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2426

theorem m3396_260 : Upper (D 10) (R 10) [66,384,80,160,260] 13 :=
  permutation_upper _ _ _ [66,129,72,384,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2408

theorem m3396_264 : Upper (D 10) (R 10) [66,384,80,160,264] 13 :=
  permutation_upper _ _ _ [66,132,288,80,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2450

theorem m3396_288 : Upper (D 10) (R 10) [66,384,80,160,288] 13 :=
  permutation_upper _ _ _ [66,160,72,384,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2472

def r3396 : Route 9 := (fun mask => (mask,id))

def c3396 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3396 : Upper (D 10) (R 10) [66,384,80,160] 13 := by
  apply FastRouting.sound _ _ [66,384,80,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3396 c3396
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3396_5
  · exact m3396_9
  · exact m3396_12
  · exact m3396_33
  · exact m3396_36
  · exact m3396_40
  · exact m3396_257
  · exact m3396_260
  · exact m3396_264
  · exact m3396_288

theorem m3397_5 : Upper (D 10) (R 10) [66,384,96,144,5] 13 :=
  permutation_upper _ _ _ [6,72,96,384,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1561

theorem m3397_9 : Upper (D 10) (R 10) [66,384,96,144,9] 13 :=
  permutation_upper _ _ _ [6,65,136,320,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1477

theorem m3397_12 : Upper (D 10) (R 10) [66,384,96,144,12] 13 :=
  permutation_upper _ _ _ [6,65,160,144,320] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1501

theorem m3397_33 : Upper (D 10) (R 10) [66,384,96,144,33] 13 :=
  permutation_upper _ _ _ [34,68,384,96,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2232

theorem m3397_36 : Upper (D 10) (R 10) [66,384,96,144,36] 13 :=
  permutation_upper _ _ _ [34,96,72,384,129] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2272

theorem m3397_40 : Upper (D 10) (R 10) [66,384,96,144,40] 13 :=
  permutation_upper _ _ _ [34,65,136,320,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2002

theorem m3397_257 : Upper (D 10) (R 10) [66,384,96,144,257] 13 :=
  permutation_upper _ _ _ [66,132,264,192,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2446

theorem m3397_260 : Upper (D 10) (R 10) [66,384,96,144,260] 13 :=
  permutation_upper _ _ _ [66,132,288,192,264] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2461

theorem m3397_264 : Upper (D 10) (R 10) [66,384,96,144,264] 13 :=
  permutation_upper _ _ _ [66,129,192,260,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2414

theorem m3397_288 : Upper (D 10) (R 10) [66,384,96,144,288] 13 :=
  permutation_upper _ _ _ [66,160,192,260,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2483

def r3397 : Route 9 := (fun mask => (mask,id))

def c3397 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3397 : Upper (D 10) (R 10) [66,384,96,144] 13 := by
  apply FastRouting.sound _ _ [66,384,96,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3397 c3397
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3397_5
  · exact m3397_9
  · exact m3397_12
  · exact m3397_33
  · exact m3397_36
  · exact m3397_40
  · exact m3397_257
  · exact m3397_260
  · exact m3397_264
  · exact m3397_288

theorem m3398_5 : Upper (D 10) (R 10) [66,384,96,160,5] 13 :=
  permutation_upper _ _ _ [6,72,96,384,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1562

theorem m3398_9 : Upper (D 10) (R 10) [66,384,96,160,9] 13 :=
  permutation_upper _ _ _ [6,72,160,384,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1663

theorem m3398_12 : Upper (D 10) (R 10) [66,384,96,160,12] 13 :=
  permutation_upper _ _ _ [6,96,160,80,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1760

theorem m3398_33 : Upper (D 10) (R 10) [66,384,96,160,33] 13 :=
  permutation_upper _ _ _ [34,68,384,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2234

theorem m3398_36 : Upper (D 10) (R 10) [66,384,96,160,36] 13 :=
  permutation_upper _ _ _ [34,96,72,384,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2273

theorem m3398_40 : Upper (D 10) (R 10) [66,384,96,160,40] 13 :=
  permutation_upper _ _ _ [34,96,136,320,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2298

theorem m3398_257 : Upper (D 10) (R 10) [66,384,96,160,257] 13 :=
  permutation_upper _ _ _ [66,132,320,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2465

theorem m3398_260 : Upper (D 10) (R 10) [66,384,96,160,260] 13 :=
  permutation_upper _ _ _ [66,160,136,320,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2480

theorem m3398_264 : Upper (D 10) (R 10) [66,384,96,160,264] 13 :=
  permutation_upper _ _ _ [66,160,192,260,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2483

def r3398 : Route 9 := (fun mask => (mask,id))

def c3398 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3398 : Upper (D 10) (R 10) [66,384,96,160] 13 := by
  apply FastRouting.sound _ _ [66,384,96,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3398 c3398
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3398_5
  · exact m3398_9
  · exact m3398_12
  · exact m3398_33
  · exact m3398_36
  · exact m3398_40
  · exact m3398_257
  · exact m3398_260
  · exact m3398_264
  · exact u2485

def b3399 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 67 386 100 392 61 61 125 189 317), lower := (rows 67 386 100 392 16 32 64 128 256), losses := [] }

theorem u3399 : Upper (D 10) (R 10) [66,384,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3399 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3400_5 : Upper (D 10) (R 10) [66,384,136,320,5] 13 :=
  permutation_upper _ _ _ [6,72,144,384,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1587

theorem m3400_33 : Upper (D 10) (R 10) [66,384,136,320,33] 13 :=
  permutation_upper _ _ _ [34,68,384,144,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2241

theorem m3400_36 : Upper (D 10) (R 10) [66,384,136,320,36] 13 :=
  permutation_upper _ _ _ [34,68,384,144,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2241

def r3400 : Route 9 := (fun mask => (mask,id))

def c3400 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3400 : Upper (D 10) (R 10) [66,384,136,320] 13 := by
  apply FastRouting.sound _ _ [66,384,136,320] 13 (by decide) (choices 2) [5,33,36] r3400 c3400
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3400_5
  · exact m3400_33
  · exact m3400_36

theorem m3401_5 : Upper (D 10) (R 10) [66,384,144,288,5] 13 :=
  permutation_upper _ _ _ [6,65,136,320,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1478

theorem m3401_9 : Upper (D 10) (R 10) [66,384,144,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,384,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1664

theorem m3401_12 : Upper (D 10) (R 10) [66,384,144,288,12] 13 :=
  permutation_upper _ _ _ [6,65,160,192,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1504

theorem m3401_33 : Upper (D 10) (R 10) [66,384,144,288,33] 13 :=
  permutation_upper _ _ _ [34,68,384,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2237

theorem m3401_36 : Upper (D 10) (R 10) [66,384,144,288,36] 13 :=
  permutation_upper _ _ _ [34,65,136,320,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2003

theorem m3401_40 : Upper (D 10) (R 10) [66,384,144,288,40] 13 :=
  permutation_upper _ _ _ [34,96,129,192,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2287

theorem m3401_65 : Upper (D 10) (R 10) [66,384,144,288,65] 13 :=
  permutation_upper _ _ _ [66,68,384,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2386

theorem m3401_68 : Upper (D 10) (R 10) [66,384,144,288,68] 13 :=
  permutation_upper _ _ _ [66,129,72,384,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2408

theorem m3401_72 : Upper (D 10) (R 10) [66,384,144,288,72] 13 :=
  permutation_upper _ _ _ [66,132,288,144,320] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2457

theorem m3401_96 : Upper (D 10) (R 10) [66,384,144,288,96] 13 :=
  permutation_upper _ _ _ [66,160,136,320,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2480

def r3401 : Route 9 := (fun mask => (mask,id))

def c3401 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u3401 : Upper (D 10) (R 10) [66,384,144,288] 13 := by
  apply FastRouting.sound _ _ [66,384,144,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r3401 c3401
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3401_5
  · exact m3401_9
  · exact m3401_12
  · exact m3401_33
  · exact m3401_36
  · exact m3401_40
  · exact m3401_65
  · exact m3401_68
  · exact m3401_72
  · exact m3401_96

theorem m3402_5 : Upper (D 10) (R 10) [66,384,144,320,5] 13 :=
  permutation_upper _ _ _ [6,65,136,320,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1479

theorem m3402_9 : Upper (D 10) (R 10) [66,384,144,320,9] 13 :=
  permutation_upper _ _ _ [6,72,192,384,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1692

theorem m3402_12 : Upper (D 10) (R 10) [66,384,144,320,12] 13 :=
  permutation_upper _ _ _ [6,65,384,144,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1535

theorem m3402_33 : Upper (D 10) (R 10) [66,384,144,320,33] 13 :=
  permutation_upper _ _ _ [34,68,384,129,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2238

theorem m3402_36 : Upper (D 10) (R 10) [66,384,144,320,36] 13 :=
  permutation_upper _ _ _ [34,65,136,320,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2004

theorem m3402_40 : Upper (D 10) (R 10) [66,384,144,320,40] 13 :=
  permutation_upper _ _ _ [34,192,72,384,257] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2345

def r3402 : Route 9 := (fun mask => (mask,id))

def c3402 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3402 : Upper (D 10) (R 10) [66,384,144,320] 13 := by
  apply FastRouting.sound _ _ [66,384,144,320] 13 (by decide) (choices 2) [5,9,12,33,36,40] r3402 c3402
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3402_5
  · exact m3402_9
  · exact m3402_12
  · exact m3402_33
  · exact m3402_36
  · exact m3402_40

theorem m3403_5 : Upper (D 10) (R 10) [66,384,160,288,5] 13 :=
  permutation_upper _ _ _ [6,72,160,384,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1665

theorem m3403_9 : Upper (D 10) (R 10) [66,384,160,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,384,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1665

theorem m3403_12 : Upper (D 10) (R 10) [66,384,160,288,12] 13 :=
  permutation_upper _ _ _ [6,96,160,192,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1765

theorem m3403_33 : Upper (D 10) (R 10) [66,384,160,288,33] 13 :=
  permutation_upper _ _ _ [34,68,384,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2242

theorem m3403_36 : Upper (D 10) (R 10) [66,384,160,288,36] 13 :=
  permutation_upper _ _ _ [34,96,136,320,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2299

theorem m3403_40 : Upper (D 10) (R 10) [66,384,160,288,40] 13 :=
  permutation_upper _ _ _ [34,96,136,320,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2299

theorem m3403_65 : Upper (D 10) (R 10) [66,384,160,288,65] 13 :=
  permutation_upper _ _ _ [66,68,384,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2388

theorem m3403_68 : Upper (D 10) (R 10) [66,384,160,288,68] 13 :=
  permutation_upper _ _ _ [66,160,72,384,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2472

theorem m3403_72 : Upper (D 10) (R 10) [66,384,160,288,72] 13 :=
  permutation_upper _ _ _ [66,160,72,384,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2472

theorem m3403_96 : Upper (D 10) (R 10) [66,384,160,288,96] 13 :=
  permutation_upper _ _ _ [66,384,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2485

def r3403 : Route 9 := (fun mask => (mask,id))

def c3403 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u3403 : Upper (D 10) (R 10) [66,384,160,288] 13 := by
  apply FastRouting.sound _ _ [66,384,160,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r3403 c3403
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3403_5
  · exact m3403_9
  · exact m3403_12
  · exact m3403_33
  · exact m3403_36
  · exact m3403_40
  · exact m3403_65
  · exact m3403_68
  · exact m3403_72
  · exact m3403_96

theorem m3404_5 : Upper (D 10) (R 10) [66,384,160,320,5] 13 :=
  permutation_upper _ _ _ [6,72,160,384,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1666

theorem m3404_9 : Upper (D 10) (R 10) [66,384,160,320,9] 13 :=
  permutation_upper _ _ _ [6,72,192,384,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1693

theorem m3404_12 : Upper (D 10) (R 10) [66,384,160,320,12] 13 :=
  permutation_upper _ _ _ [6,96,384,144,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1825

theorem m3404_33 : Upper (D 10) (R 10) [66,384,160,320,33] 13 :=
  permutation_upper _ _ _ [34,68,384,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2243

theorem m3404_36 : Upper (D 10) (R 10) [66,384,160,320,36] 13 :=
  permutation_upper _ _ _ [34,96,136,320,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2300

theorem m3404_40 : Upper (D 10) (R 10) [66,384,160,320,40] 13 :=
  permutation_upper _ _ _ [34,192,72,384,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2347

def r3404 : Route 9 := (fun mask => (mask,id))

def c3404 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3404 : Upper (D 10) (R 10) [66,384,160,320] 13 := by
  apply FastRouting.sound _ _ [66,384,160,320] 13 (by decide) (choices 2) [5,9,12,33,36,40] r3404 c3404
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3404_5
  · exact m3404_9
  · exact m3404_12
  · exact m3404_33
  · exact m3404_36
  · exact m3404_40

theorem m3405_3 : Upper (D 10) (R 10) [80,96,160,288,3] 13 :=
  permutation_upper _ _ _ [6,65,96,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1448

theorem m3405_5 : Upper (D 10) (R 10) [80,96,160,288,5] 13 :=
  permutation_upper _ _ _ [6,65,160,96,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1497

theorem m3405_6 : Upper (D 10) (R 10) [80,96,160,288,6] 13 :=
  permutation_upper _ _ _ [6,96,160,65,288] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1753

theorem m3405_9 : Upper (D 10) (R 10) [80,96,160,288,9] 13 :=
  permutation_upper _ _ _ [6,65,160,96,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1497

theorem m3405_10 : Upper (D 10) (R 10) [80,96,160,288,10] 13 :=
  permutation_upper _ _ _ [6,96,160,65,288] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1753

theorem m3405_12 : Upper (D 10) (R 10) [80,96,160,288,12] 13 :=
  permutation_upper _ _ _ [6,96,160,257,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1768

theorem m3405_129 : Upper (D 10) (R 10) [80,96,160,288,129] 13 :=
  permutation_upper _ _ _ [66,129,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2410

theorem m3405_130 : Upper (D 10) (R 10) [80,96,160,288,130] 13 :=
  permutation_upper _ _ _ [66,132,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2431

theorem m3405_132 : Upper (D 10) (R 10) [80,96,160,288,132] 13 :=
  permutation_upper _ _ _ [66,96,129,160,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2392

theorem m3405_136 : Upper (D 10) (R 10) [80,96,160,288,136] 13 :=
  permutation_upper _ _ _ [66,132,288,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2452

theorem m3405_257 : Upper (D 10) (R 10) [80,96,160,288,257] 13 :=
  permutation_upper _ _ _ [66,129,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2410

theorem m3405_258 : Upper (D 10) (R 10) [80,96,160,288,258] 13 :=
  permutation_upper _ _ _ [66,132,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2431

theorem m3405_260 : Upper (D 10) (R 10) [80,96,160,288,260] 13 :=
  permutation_upper _ _ _ [66,132,288,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2452

theorem m3405_264 : Upper (D 10) (R 10) [80,96,160,288,264] 13 :=
  permutation_upper _ _ _ [66,96,129,160,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2392

theorem m3405_384 : Upper (D 10) (R 10) [80,96,160,288,384] 13 :=
  permutation_upper _ _ _ [66,384,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2485

def r3405 : Route 9 := (fun mask => (mask,id))

def c3405 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3405 : Upper (D 10) (R 10) [80,96,160,288] 13 := by
  apply FastRouting.sound _ _ [80,96,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,257,258,260,264,384] r3405 c3405
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3405_3
  · exact m3405_5
  · exact m3405_6
  · exact m3405_9
  · exact m3405_10
  · exact m3405_12
  · exact m3405_129
  · exact m3405_130
  · exact m3405_132
  · exact m3405_136
  · exact m3405_257
  · exact m3405_258
  · exact m3405_260
  · exact m3405_264
  · exact m3405_384

theorem m3406_3 : Upper (D 10) (R 10) [80,96,160,384,3] 13 :=
  permutation_upper _ _ _ [6,65,96,160,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1449

theorem m3406_5 : Upper (D 10) (R 10) [80,96,160,384,5] 13 :=
  permutation_upper _ _ _ [6,65,160,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1498

theorem m3406_6 : Upper (D 10) (R 10) [80,96,160,384,6] 13 :=
  permutation_upper _ _ _ [6,96,160,65,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1754

theorem m3406_9 : Upper (D 10) (R 10) [80,96,160,384,9] 13 :=
  permutation_upper _ _ _ [6,65,384,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1532

theorem m3406_10 : Upper (D 10) (R 10) [80,96,160,384,10] 13 :=
  permutation_upper _ _ _ [6,96,384,65,160] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1813

theorem m3406_12 : Upper (D 10) (R 10) [80,96,160,384,12] 13 :=
  permutation_upper _ _ _ [6,96,192,257,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1793

theorem m3406_33 : Upper (D 10) (R 10) [80,96,160,384,33] 13 :=
  permutation_upper _ _ _ [34,65,96,160,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1983

theorem m3406_34 : Upper (D 10) (R 10) [80,96,160,384,34] 13 :=
  permutation_upper _ _ _ [34,96,65,160,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2258

theorem m3406_36 : Upper (D 10) (R 10) [80,96,160,384,36] 13 :=
  permutation_upper _ _ _ [34,96,129,160,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2285

theorem m3406_40 : Upper (D 10) (R 10) [80,96,160,384,40] 13 :=
  permutation_upper _ _ _ [34,192,96,257,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2352

theorem m3406_257 : Upper (D 10) (R 10) [80,96,160,384,257] 13 :=
  permutation_upper _ _ _ [66,129,96,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2413

theorem m3406_258 : Upper (D 10) (R 10) [80,96,160,384,258] 13 :=
  permutation_upper _ _ _ [66,132,96,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2434

theorem m3406_260 : Upper (D 10) (R 10) [80,96,160,384,260] 13 :=
  permutation_upper _ _ _ [66,132,288,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2455

theorem m3406_264 : Upper (D 10) (R 10) [80,96,160,384,264] 13 :=
  permutation_upper _ _ _ [66,132,384,96,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2468

theorem m3406_288 : Upper (D 10) (R 10) [80,96,160,384,288] 13 :=
  permutation_upper _ _ _ [66,160,96,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2479

def r3406 : Route 9 := (fun mask => (mask,id))

def c3406 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3406 : Upper (D 10) (R 10) [80,96,160,384] 13 := by
  apply FastRouting.sound _ _ [80,96,160,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r3406 c3406
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3406_3
  · exact m3406_5
  · exact m3406_6
  · exact m3406_9
  · exact m3406_10
  · exact m3406_12
  · exact m3406_33
  · exact m3406_34
  · exact m3406_36
  · exact m3406_40
  · exact m3406_257
  · exact m3406_258
  · exact m3406_260
  · exact m3406_264
  · exact m3406_288

theorem m3407_3 : Upper (D 10) (R 10) [80,160,192,288,3] 13 :=
  permutation_upper _ _ _ [6,65,160,192,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1505

theorem m3407_5 : Upper (D 10) (R 10) [80,160,192,288,5] 13 :=
  permutation_upper _ _ _ [6,65,192,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1520

theorem m3407_6 : Upper (D 10) (R 10) [80,160,192,288,6] 13 :=
  permutation_upper _ _ _ [6,96,192,129,288] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1786

theorem m3407_9 : Upper (D 10) (R 10) [80,160,192,288,9] 13 :=
  permutation_upper _ _ _ [6,65,160,288,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1511

theorem m3407_10 : Upper (D 10) (R 10) [80,160,192,288,10] 13 :=
  permutation_upper _ _ _ [6,96,160,257,320] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1769

theorem m3407_12 : Upper (D 10) (R 10) [80,160,192,288,12] 13 :=
  permutation_upper _ _ _ [6,96,384,129,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1821

theorem m3407_33 : Upper (D 10) (R 10) [80,160,192,288,33] 13 :=
  permutation_upper _ _ _ [34,65,160,192,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2006

theorem m3407_34 : Upper (D 10) (R 10) [80,160,192,288,34] 13 :=
  permutation_upper _ _ _ [34,96,129,192,288] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2288

theorem m3407_36 : Upper (D 10) (R 10) [80,160,192,288,36] 13 :=
  permutation_upper _ _ _ [34,192,65,160,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2315

theorem m3407_40 : Upper (D 10) (R 10) [80,160,192,288,40] 13 :=
  permutation_upper _ _ _ [34,96,129,288,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2293

theorem m3407_257 : Upper (D 10) (R 10) [80,160,192,288,257] 13 :=
  permutation_upper _ _ _ [66,129,96,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2413

theorem m3407_258 : Upper (D 10) (R 10) [80,160,192,288,258] 13 :=
  permutation_upper _ _ _ [66,132,288,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2460

theorem m3407_260 : Upper (D 10) (R 10) [80,160,192,288,260] 13 :=
  permutation_upper _ _ _ [66,132,320,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2465

theorem m3407_264 : Upper (D 10) (R 10) [80,160,192,288,264] 13 :=
  permutation_upper _ _ _ [66,96,129,288,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2395

theorem m3407_288 : Upper (D 10) (R 10) [80,160,192,288,288] 13 :=
  permutation_upper _ _ _ [66,160,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2482

def r3407 : Route 9 := (fun mask => (mask,id))

def c3407 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3407 : Upper (D 10) (R 10) [80,160,192,288] 13 := by
  apply FastRouting.sound _ _ [80,160,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r3407 c3407
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3407_3
  · exact m3407_5
  · exact m3407_6
  · exact m3407_9
  · exact m3407_10
  · exact m3407_12
  · exact m3407_33
  · exact m3407_34
  · exact m3407_36
  · exact m3407_40
  · exact m3407_257
  · exact m3407_258
  · exact m3407_260
  · exact m3407_264
  · exact m3407_288

theorem m3408_3 : Upper (D 10) (R 10) [80,160,288,384,3] 13 :=
  permutation_upper _ _ _ [6,65,160,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1512

theorem m3408_5 : Upper (D 10) (R 10) [80,160,288,384,5] 13 :=
  permutation_upper _ _ _ [6,65,160,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1512

theorem m3408_6 : Upper (D 10) (R 10) [80,160,288,384,6] 13 :=
  permutation_upper _ _ _ [6,96,160,192,257] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1764

theorem m3408_9 : Upper (D 10) (R 10) [80,160,288,384,9] 13 :=
  permutation_upper _ _ _ [6,65,384,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1536

theorem m3408_10 : Upper (D 10) (R 10) [80,160,288,384,10] 13 :=
  permutation_upper _ _ _ [6,96,192,160,257] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1790

theorem m3408_12 : Upper (D 10) (R 10) [80,160,288,384,12] 13 :=
  permutation_upper _ _ _ [6,96,192,160,257] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1790

theorem m3408_33 : Upper (D 10) (R 10) [80,160,288,384,33] 13 :=
  permutation_upper _ _ _ [34,65,160,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2007

theorem m3408_34 : Upper (D 10) (R 10) [80,160,288,384,34] 13 :=
  permutation_upper _ _ _ [34,96,129,288,320] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2292

theorem m3408_36 : Upper (D 10) (R 10) [80,160,288,384,36] 13 :=
  permutation_upper _ _ _ [34,96,129,288,320] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2292

theorem m3408_40 : Upper (D 10) (R 10) [80,160,288,384,40] 13 :=
  permutation_upper _ _ _ [34,192,96,160,257] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2348

theorem m3408_65 : Upper (D 10) (R 10) [80,160,288,384,65] 13 :=
  permutation_upper _ _ _ [66,65,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2366

theorem m3408_66 : Upper (D 10) (R 10) [80,160,288,384,66] 13 :=
  permutation_upper _ _ _ [66,68,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2384

theorem m3408_68 : Upper (D 10) (R 10) [80,160,288,384,68] 13 :=
  permutation_upper _ _ _ [66,68,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2384

theorem m3408_72 : Upper (D 10) (R 10) [80,160,288,384,72] 13 :=
  permutation_upper _ _ _ [66,68,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2388

theorem m3408_96 : Upper (D 10) (R 10) [80,160,288,384,96] 13 :=
  permutation_upper _ _ _ [66,96,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2398

def r3408 : Route 9 := (fun mask => (mask,id))

def c3408 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u3408 : Upper (D 10) (R 10) [80,160,288,384] 13 := by
  apply FastRouting.sound _ _ [80,160,288,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r3408 c3408
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3408_3
  · exact m3408_5
  · exact m3408_6
  · exact m3408_9
  · exact m3408_10
  · exact m3408_12
  · exact m3408_33
  · exact m3408_34
  · exact m3408_36
  · exact m3408_40
  · exact m3408_65
  · exact m3408_66
  · exact m3408_68
  · exact m3408_72
  · exact m3408_96

theorem m3409_3 : Upper (D 10) (R 10) [80,160,320,384,3] 13 :=
  permutation_upper _ _ _ [6,65,160,320,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1513

theorem m3409_5 : Upper (D 10) (R 10) [80,160,320,384,5] 13 :=
  permutation_upper _ _ _ [6,65,192,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1521

theorem m3409_6 : Upper (D 10) (R 10) [80,160,320,384,6] 13 :=
  permutation_upper _ _ _ [6,96,384,129,320] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1822

theorem m3409_9 : Upper (D 10) (R 10) [80,160,320,384,9] 13 :=
  permutation_upper _ _ _ [6,65,384,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1537

theorem m3409_10 : Upper (D 10) (R 10) [80,160,320,384,10] 13 :=
  permutation_upper _ _ _ [6,96,192,257,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1794

theorem m3409_12 : Upper (D 10) (R 10) [80,160,320,384,12] 13 :=
  permutation_upper _ _ _ [6,192,320,129,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1840

theorem m3409_33 : Upper (D 10) (R 10) [80,160,320,384,33] 13 :=
  permutation_upper _ _ _ [34,65,160,320,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2008

theorem m3409_34 : Upper (D 10) (R 10) [80,160,320,384,34] 13 :=
  permutation_upper _ _ _ [34,96,129,320,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2294

theorem m3409_36 : Upper (D 10) (R 10) [80,160,320,384,36] 13 :=
  permutation_upper _ _ _ [34,192,65,288,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2318

theorem m3409_40 : Upper (D 10) (R 10) [80,160,320,384,40] 13 :=
  permutation_upper _ _ _ [34,192,96,257,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2353

def r3409 : Route 9 := (fun mask => (mask,id))

def c3409 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3409 : Upper (D 10) (R 10) [80,160,320,384] 13 := by
  apply FastRouting.sound _ _ [80,160,320,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r3409 c3409
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3409_3
  · exact m3409_5
  · exact m3409_6
  · exact m3409_9
  · exact m3409_10
  · exact m3409_12
  · exact m3409_33
  · exact m3409_34
  · exact m3409_36
  · exact m3409_40

def b3410 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 2, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 97 98 164 392 287 319 351 415 287), lower := (rows 97 98 164 392 16 32 64 128 256), losses := [] }

theorem u3410 : Upper (D 10) (R 10) [96,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3410 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3411_3 : Upper (D 10) (R 10) [96,160,192,288,3] 13 :=
  permutation_upper _ _ _ [6,96,160,192,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1766

theorem m3411_5 : Upper (D 10) (R 10) [96,160,192,288,5] 13 :=
  permutation_upper _ _ _ [6,96,192,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1792

theorem m3411_6 : Upper (D 10) (R 10) [96,160,192,288,6] 13 :=
  permutation_upper _ _ _ [6,96,192,160,288] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1792

theorem m3411_9 : Upper (D 10) (R 10) [96,160,192,288,9] 13 :=
  permutation_upper _ _ _ [6,96,160,288,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1773

theorem m3411_10 : Upper (D 10) (R 10) [96,160,192,288,10] 13 :=
  permutation_upper _ _ _ [6,96,160,288,320] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1773

theorem m3411_12 : Upper (D 10) (R 10) [96,160,192,288,12] 13 :=
  permutation_upper _ _ _ [6,96,384,160,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1826

theorem m3411_257 : Upper (D 10) (R 10) [96,160,192,288,257] 13 :=
  permutation_upper _ _ _ [66,160,96,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2479

theorem m3411_258 : Upper (D 10) (R 10) [96,160,192,288,258] 13 :=
  permutation_upper _ _ _ [66,160,96,288,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2479

theorem m3411_260 : Upper (D 10) (R 10) [96,160,192,288,260] 13 :=
  permutation_upper _ _ _ [66,384,96,160,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2485

theorem m3411_264 : Upper (D 10) (R 10) [96,160,192,288,264] 13 :=
  permutation_upper _ _ _ [66,96,160,288,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2398

def r3411 : Route 9 := (fun mask => (mask,id))

def c3411 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3411 : Upper (D 10) (R 10) [96,160,192,288] 13 := by
  apply FastRouting.sound _ _ [96,160,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r3411 c3411
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3411_3
  · exact m3411_5
  · exact m3411_6
  · exact m3411_9
  · exact m3411_10
  · exact m3411_12
  · exact m3411_257
  · exact m3411_258
  · exact m3411_260
  · exact m3411_264

theorem m3412_3 : Upper (D 10) (R 10) [96,160,320,384,3] 13 :=
  permutation_upper _ _ _ [6,96,160,320,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1774

theorem m3412_5 : Upper (D 10) (R 10) [96,160,320,384,5] 13 :=
  permutation_upper _ _ _ [6,96,192,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1795

theorem m3412_6 : Upper (D 10) (R 10) [96,160,320,384,6] 13 :=
  permutation_upper _ _ _ [6,96,384,160,320] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1827

theorem m3412_9 : Upper (D 10) (R 10) [96,160,320,384,9] 13 :=
  permutation_upper _ _ _ [6,96,384,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1827

theorem m3412_10 : Upper (D 10) (R 10) [96,160,320,384,10] 13 :=
  permutation_upper _ _ _ [6,96,192,288,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1795

theorem m3412_12 : Upper (D 10) (R 10) [96,160,320,384,12] 13 :=
  permutation_upper _ _ _ [6,192,320,160,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1842

theorem m3412_33 : Upper (D 10) (R 10) [96,160,320,384,33] 13 :=
  permutation_upper _ _ _ [34,96,160,320,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2301

theorem m3412_34 : Upper (D 10) (R 10) [96,160,320,384,34] 13 :=
  permutation_upper _ _ _ [34,96,160,320,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2301

theorem m3412_36 : Upper (D 10) (R 10) [96,160,320,384,36] 13 :=
  permutation_upper _ _ _ [34,192,96,288,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2360

theorem m3412_40 : Upper (D 10) (R 10) [96,160,320,384,40] 13 :=
  permutation_upper _ _ _ [34,192,96,288,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2360

def r3412 : Route 9 := (fun mask => (mask,id))

def c3412 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3412 : Upper (D 10) (R 10) [96,160,320,384] 13 := by
  apply FastRouting.sound _ _ [96,160,320,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r3412 c3412
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3412_3
  · exact m3412_5
  · exact m3412_6
  · exact m3412_9
  · exact m3412_10
  · exact m3412_12
  · exact m3412_33
  · exact m3412_34
  · exact m3412_36
  · exact m3412_40

def r3413 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c3413 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u3413 : Upper (D 10) (R 10) [6,9,48] 13 := by
  apply FastRouting.sound _ _ [6,9,48] 13 (by decide) (choices 2) [96,192] r3413 c3413
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2486
  · exact u2487

def r3414 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3414 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u3414 : Upper (D 10) (R 10) [6,9,80] 13 := by
  apply FastRouting.sound _ _ [6,9,80] 13 (by decide) (choices 2) [96,160,192,384] r3414 c3414
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2488
  · exact u2489
  · exact u2490
  · exact u2491

theorem m3415_48 : Upper (D 10) (R 10) [6,9,96,48] 13 :=
  permutation_upper _ _ _ [6,9,48,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2486

theorem m3415_80 : Upper (D 10) (R 10) [6,9,96,80] 13 :=
  permutation_upper _ _ _ [6,9,80,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2488

theorem m3415_144 : Upper (D 10) (R 10) [6,9,96,144] 13 :=
  permutation_upper _ _ _ [6,9,80,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2489

def r3415 : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3415 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3415 : Upper (D 10) (R 10) [6,9,96] 13 := by
  apply FastRouting.sound _ _ [6,9,96] 13 (by decide) (choices 2) [48,80,96,144,160,192,384] r3415 c3415
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3415_48
  · exact m3415_80
  · exact u2492
  · exact m3415_144
  · exact u2493
  · exact u2494
  · exact u2495

theorem m3416_48 : Upper (D 10) (R 10) [6,9,192,48] 13 :=
  permutation_upper _ _ _ [6,9,48,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2487

theorem m3416_80 : Upper (D 10) (R 10) [6,9,192,80] 13 :=
  permutation_upper _ _ _ [6,9,80,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2490

theorem m3416_96 : Upper (D 10) (R 10) [6,9,192,96] 13 :=
  permutation_upper _ _ _ [6,9,96,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2494

theorem m3416_272 : Upper (D 10) (R 10) [6,9,192,272] 13 :=
  permutation_upper _ _ _ [6,9,80,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2491

theorem m3416_288 : Upper (D 10) (R 10) [6,9,192,288] 13 :=
  permutation_upper _ _ _ [6,9,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2495

def r3416 : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3416 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3416 : Upper (D 10) (R 10) [6,9,192] 13 := by
  apply FastRouting.sound _ _ [6,9,192] 13 (by decide) (choices 2) [48,80,96,192,272,288,320] r3416 c3416
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3416_48
  · exact m3416_80
  · exact m3416_96
  · exact u2496
  · exact m3416_272
  · exact m3416_288
  · exact u2497

def r3417 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c3417 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u3417 : Upper (D 10) (R 10) [6,24,33] 13 := by
  apply FastRouting.sound _ _ [6,24,33] 13 (by decide) (choices 2) [96,192] r3417 c3417
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2512
  · exact u2513

def r3418 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3418 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u3418 : Upper (D 10) (R 10) [6,24,65] 13 := by
  apply FastRouting.sound _ _ [6,24,65] 13 (by decide) (choices 2) [96,160,192,384] r3418 c3418
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2514
  · exact u2515
  · exact u2516
  · exact u2517

def r3419 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3419 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u3419 : Upper (D 10) (R 10) [6,24,96] 13 := by
  apply FastRouting.sound _ _ [6,24,96] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r3419 c3419
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u2518
  · exact u2519
  · exact u2520
  · exact u2521
  · exact u2522
  · exact u2523
  · exact u2524

#print axioms u3419
end Delivery.IrregularNine14.P10
