import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0298
import IrregularNine14P08C0299
import IrregularNine14P08C0300
import IrregularNine14P08C0301
import IrregularNine14P08C0302
import IrregularNine14P08C0303
import IrregularNine14P08C0304
import IrregularNine14P08C0305
import IrregularNine14P08C0306
import IrregularNine14P08C0308
import IrregularNine14P08C0309
import IrregularNine14P08C0310
import IrregularNine14P08C0311
import IrregularNine14P08C0312

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23700 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 104 147 179 211 147 403), lower := (rows 321 38 44 104 16 32 64 128 256), losses := [] }

theorem u23700 : Upper (D 8) (R 8) [320,36,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23701 : PairBound 9 := { available := 243, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 137 243 243 243 243 499), lower := (rows 321 38 44 137 16 32 64 128 256), losses := [] }

theorem u23701 : Upper (D 8) (R 8) [320,36,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23702 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 138 241 241 241 241 497), lower := (rows 321 38 44 138 16 32 64 128 256), losses := [] }

theorem u23702 : Upper (D 8) (R 8) [320,36,40,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23703 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 168 211 243 211 211 467), lower := (rows 321 38 44 168 16 32 64 128 256), losses := [] }

theorem u23703 : Upper (D 8) (R 8) [320,36,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23704 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 44 200 179 179 243 179 435), lower := (rows 321 38 44 200 16 32 64 128 256), losses := [] }

theorem u23704 : Upper (D 8) (R 8) [320,36,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23705 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 52 74 185 169 233 169 425), lower := (rows 321 38 52 74 16 32 64 128 256), losses := [] }

theorem u23705 : Upper (D 8) (R 8) [320,36,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23706 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 52 104 155 171 203 139 395), lower := (rows 321 38 52 104 16 32 64 128 256), losses := [] }

theorem u23706 : Upper (D 8) (R 8) [320,36,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23707 : PairBound 9 := { available := 235, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 52 137 251 235 235 235 491), lower := (rows 321 38 52 137 16 32 64 128 256), losses := [] }

theorem u23707 : Upper (D 8) (R 8) [320,36,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23708 : PairBound 9 := { available := 233, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 52 138 249 233 233 233 489), lower := (rows 321 38 52 138 16 32 64 128 256), losses := [] }

theorem u23708 : Upper (D 8) (R 8) [320,36,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23709 : PairBound 9 := { available := 203, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 52 168 219 235 203 203 459), lower := (rows 321 38 52 168 16 32 64 128 256), losses := [] }

theorem u23709 : Upper (D 8) (R 8) [320,36,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23710 : PairBound 9 := { available := 171, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 52 200 187 171 235 171 427), lower := (rows 321 38 52 200 16 32 64 128 256), losses := [] }

theorem u23710 : Upper (D 8) (R 8) [320,36,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23711 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 69 137 186 186 250 186 442), lower := (rows 321 38 69 137 16 32 64 128 256), losses := [] }

theorem u23711 : Upper (D 8) (R 8) [320,36,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23712 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 69 138 185 185 249 185 441), lower := (rows 321 38 69 138 16 32 64 128 256), losses := [] }

theorem u23712 : Upper (D 8) (R 8) [320,36,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23713 : PairBound 9 := { available := 187, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 69 168 187 187 251 187 443), lower := (rows 321 38 69 168 16 32 64 128 256), losses := [] }

theorem u23713 : Upper (D 8) (R 8) [320,36,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23714 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 38 70 137 185 185 249 185 441), lower := (rows 321 38 70 137 16 32 64 128 256), losses := [] }

theorem u23714 : Upper (D 8) (R 8) [320,36,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23715 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 38 70 168 185 185 249 185 441), lower := (rows 321 38 70 168 16 32 64 128 256), losses := [] }

theorem u23715 : Upper (D 8) (R 8) [320,36,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23716_3 : Upper (D 8) (R 8) [320,36,72,48,3] 13 :=
  permutation_upper _ _ _ [320,5,40,80,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17979

theorem m23716_33 : Upper (D 8) (R 8) [320,36,72,48,33] 13 :=
  permutation_upper _ _ _ [320,33,34,48,68] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18505

theorem m23716_34 : Upper (D 8) (R 8) [320,36,72,48,34] 13 :=
  permutation_upper _ _ _ [320,36,40,48,66] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18640

def r23716 : Route 9 := (fun mask => (mask,id))

def c23716 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23716 : Upper (D 8) (R 8) [320,36,72,48] 13 := by
  apply FastRouting.sound _ _ [320,36,72,48] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23716 c23716
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23716_3
  · exact m23716_33
  · exact m23716_34
  · exact u18678
  · exact u18679
  · exact u18680

theorem m23717_3 : Upper (D 8) (R 8) [320,36,72,129,3] 13 :=
  permutation_upper _ _ _ [320,5,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17980

theorem m23717_33 : Upper (D 8) (R 8) [320,36,72,129,33] 13 :=
  permutation_upper _ _ _ [320,33,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18544

theorem m23717_34 : Upper (D 8) (R 8) [320,36,72,129,34] 13 :=
  permutation_upper _ _ _ [320,36,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18646

def r23717 : Route 9 := (fun mask => (mask,id))

def c23717 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23717 : Upper (D 8) (R 8) [320,36,72,129] 13 := by
  apply FastRouting.sound _ _ [320,36,72,129] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23717 c23717
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23717_3
  · exact m23717_33
  · exact m23717_34
  · exact u18681
  · exact u18682
  · exact u18683

def b23718 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 38 76 138 177 177 241 177 433), lower := (rows 321 38 76 138 16 32 64 128 256), losses := [] }

theorem u23718 : Upper (D 8) (R 8) [320,36,72,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23719_3 : Upper (D 8) (R 8) [320,36,72,144,3] 13 :=
  permutation_upper _ _ _ [320,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17981

theorem m23719_33 : Upper (D 8) (R 8) [320,36,72,144,33] 13 :=
  permutation_upper _ _ _ [320,33,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18545

theorem m23719_34 : Upper (D 8) (R 8) [320,36,72,144,34] 13 :=
  permutation_upper _ _ _ [320,36,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18647

def r23719 : Route 9 := (fun mask => (mask,id))

def c23719 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23719 : Upper (D 8) (R 8) [320,36,72,144] 13 := by
  apply FastRouting.sound _ _ [320,36,72,144] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23719 c23719
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23719_3
  · exact m23719_33
  · exact m23719_34
  · exact u18686
  · exact u18687
  · exact u18688

theorem m23720_3 : Upper (D 8) (R 8) [320,36,72,160,3] 13 :=
  permutation_upper _ _ _ [320,5,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17982

theorem m23720_33 : Upper (D 8) (R 8) [320,36,72,160,33] 13 :=
  permutation_upper _ _ _ [320,33,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18547

theorem m23720_34 : Upper (D 8) (R 8) [320,36,72,160,34] 13 :=
  permutation_upper _ _ _ [320,36,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18648

def r23720 : Route 9 := (fun mask => (mask,id))

def c23720 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23720 : Upper (D 8) (R 8) [320,36,72,160] 13 := by
  apply FastRouting.sound _ _ [320,36,72,160] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23720 c23720
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23720_3
  · exact m23720_33
  · exact m23720_34
  · exact u18689
  · exact u18690
  · exact u18691

theorem m23721_3 : Upper (D 8) (R 8) [320,36,80,129,3] 13 :=
  permutation_upper _ _ _ [320,5,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17976

theorem m23721_9 : Upper (D 8) (R 8) [320,36,80,129,9] 13 :=
  permutation_upper _ _ _ [320,5,129,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18093

theorem m23721_10 : Upper (D 8) (R 8) [320,36,80,129,10] 13 :=
  permutation_upper _ _ _ [320,12,48,129,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18379

theorem m23721_33 : Upper (D 8) (R 8) [320,36,80,129,33] 13 :=
  permutation_upper _ _ _ [320,33,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18538

theorem m23721_34 : Upper (D 8) (R 8) [320,36,80,129,34] 13 :=
  permutation_upper _ _ _ [320,36,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18644

theorem m23721_40 : Upper (D 8) (R 8) [320,36,80,129,40] 13 :=
  permutation_upper _ _ _ [320,36,72,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18678

theorem m23721_129 : Upper (D 8) (R 8) [320,36,80,129,129] 13 :=
  permutation_upper _ _ _ [320,36,72,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18681

theorem m23721_130 : Upper (D 8) (R 8) [320,36,80,129,130] 13 :=
  permutation_upper _ _ _ [320,36,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18684

theorem m23721_136 : Upper (D 8) (R 8) [320,36,80,129,136] 13 :=
  permutation_upper _ _ _ [320,36,72,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18686

theorem m23721_160 : Upper (D 8) (R 8) [320,36,80,129,160] 13 :=
  permutation_upper _ _ _ [320,36,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18689

def r23721 : Route 9 := (fun mask => (mask,id))

def c23721 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23721 : Upper (D 8) (R 8) [320,36,80,129] 13 := by
  apply FastRouting.sound _ _ [320,36,80,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23721 c23721
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23721_3
  · exact m23721_9
  · exact m23721_10
  · exact m23721_33
  · exact m23721_34
  · exact m23721_40
  · exact m23721_129
  · exact m23721_130
  · exact m23721_136
  · exact m23721_160

theorem m23722_9 : Upper (D 8) (R 8) [320,36,80,130,9] 13 :=
  permutation_upper _ _ _ [320,5,136,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18148

theorem m23722_33 : Upper (D 8) (R 8) [320,36,80,130,33] 13 :=
  permutation_upper _ _ _ [320,33,40,66,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18539

theorem m23722_40 : Upper (D 8) (R 8) [320,36,80,130,40] 13 :=
  permutation_upper _ _ _ [320,36,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18679

theorem m23722_129 : Upper (D 8) (R 8) [320,36,80,130,129] 13 :=
  permutation_upper _ _ _ [320,36,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18682

theorem m23722_136 : Upper (D 8) (R 8) [320,36,80,130,136] 13 :=
  permutation_upper _ _ _ [320,36,72,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18687

theorem m23722_160 : Upper (D 8) (R 8) [320,36,80,130,160] 13 :=
  permutation_upper _ _ _ [320,36,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18690

def r23722 : Route 9 := (fun mask => (mask,id))

def c23722 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23722 : Upper (D 8) (R 8) [320,36,80,130] 13 := by
  apply FastRouting.sound _ _ [320,36,80,130] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23722 c23722
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23722_9
  · exact m23722_33
  · exact m23722_40
  · exact m23722_129
  · exact m23722_136
  · exact m23722_160

theorem m23723_3 : Upper (D 8) (R 8) [320,36,80,160,3] 13 :=
  permutation_upper _ _ _ [320,5,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17977

theorem m23723_9 : Upper (D 8) (R 8) [320,36,80,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18214

theorem m23723_10 : Upper (D 8) (R 8) [320,36,80,160,10] 13 :=
  permutation_upper _ _ _ [320,12,48,160,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18394

theorem m23723_33 : Upper (D 8) (R 8) [320,36,80,160,33] 13 :=
  permutation_upper _ _ _ [320,33,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18540

theorem m23723_34 : Upper (D 8) (R 8) [320,36,80,160,34] 13 :=
  permutation_upper _ _ _ [320,36,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18645

theorem m23723_40 : Upper (D 8) (R 8) [320,36,80,160,40] 13 :=
  permutation_upper _ _ _ [320,36,72,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18680

theorem m23723_129 : Upper (D 8) (R 8) [320,36,80,160,129] 13 :=
  permutation_upper _ _ _ [320,36,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18683

theorem m23723_130 : Upper (D 8) (R 8) [320,36,80,160,130] 13 :=
  permutation_upper _ _ _ [320,36,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18685

theorem m23723_136 : Upper (D 8) (R 8) [320,36,80,160,136] 13 :=
  permutation_upper _ _ _ [320,36,72,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18688

theorem m23723_160 : Upper (D 8) (R 8) [320,36,80,160,160] 13 :=
  permutation_upper _ _ _ [320,36,72,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18691

def r23723 : Route 9 := (fun mask => (mask,id))

def c23723 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23723 : Upper (D 8) (R 8) [320,36,80,160] 13 := by
  apply FastRouting.sound _ _ [320,36,80,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23723 c23723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23723_3
  · exact m23723_9
  · exact m23723_10
  · exact m23723_33
  · exact m23723_34
  · exact m23723_40
  · exact m23723_129
  · exact m23723_130
  · exact m23723_136
  · exact m23723_160

def b23724 : PairBound 9 := { available := 187, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 100 137 187 187 251 187 443), lower := (rows 321 38 100 137 16 32 64 128 256), losses := [] }

theorem u23724 : Upper (D 8) (R 8) [320,36,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23725 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 100 138 185 185 249 185 441), lower := (rows 321 38 100 138 16 32 64 128 256), losses := [] }

theorem u23725 : Upper (D 8) (R 8) [320,36,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23726 : PairBound 9 := { available := 155, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 100 168 155 187 219 155 411), lower := (rows 321 38 100 168 16 32 64 128 256), losses := [] }

theorem u23726 : Upper (D 8) (R 8) [320,36,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23727_3 : Upper (D 8) (R 8) [320,36,129,48,3] 13 :=
  permutation_upper _ _ _ [320,5,40,129,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17988

theorem m23727_9 : Upper (D 8) (R 8) [320,36,129,48,9] 13 :=
  permutation_upper _ _ _ [320,5,34,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17921

theorem m23727_10 : Upper (D 8) (R 8) [320,36,129,48,10] 13 :=
  permutation_upper _ _ _ [320,12,34,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18336

theorem m23727_33 : Upper (D 8) (R 8) [320,36,129,48,33] 13 :=
  permutation_upper _ _ _ [320,33,34,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18506

theorem m23727_34 : Upper (D 8) (R 8) [320,36,129,48,34] 13 :=
  permutation_upper _ _ _ [320,36,40,48,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18641

theorem m23727_40 : Upper (D 8) (R 8) [320,36,129,48,40] 13 :=
  permutation_upper _ _ _ [320,36,34,48,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18630

theorem m23727_65 : Upper (D 8) (R 8) [320,36,129,48,65] 13 :=
  permutation_upper _ _ _ [320,36,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18669

theorem m23727_66 : Upper (D 8) (R 8) [320,36,129,48,66] 13 :=
  permutation_upper _ _ _ [320,36,72,48,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18678

theorem m23727_72 : Upper (D 8) (R 8) [320,36,129,48,72] 13 :=
  permutation_upper _ _ _ [320,36,66,48,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18675

theorem m23727_96 : Upper (D 8) (R 8) [320,36,129,48,96] 13 :=
  permutation_upper _ _ _ [320,36,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18692

def r23727 : Route 9 := (fun mask => (mask,id))

def c23727 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23727 : Upper (D 8) (R 8) [320,36,129,48] 13 := by
  apply FastRouting.sound _ _ [320,36,129,48] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r23727 c23727
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23727_3
  · exact m23727_9
  · exact m23727_10
  · exact m23727_33
  · exact m23727_34
  · exact m23727_40
  · exact m23727_65
  · exact m23727_66
  · exact m23727_72
  · exact m23727_96
  · exact u18698
  · exact u18699
  · exact u18700
  · exact u18701
  · exact u18702

def b23728 : PairBound 9 := { available := 186, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 133 73 186 186 250 186 442), lower := (rows 321 38 133 73 16 32 64 128 256), losses := [] }

theorem u23728 : Upper (D 8) (R 8) [320,36,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23729_9 : Upper (D 8) (R 8) [320,36,129,66,9] 13 :=
  permutation_upper _ _ _ [320,5,72,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18048

theorem m23729_33 : Upper (D 8) (R 8) [320,36,129,66,33] 13 :=
  permutation_upper _ _ _ [320,33,40,129,68] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18552

theorem m23729_40 : Upper (D 8) (R 8) [320,36,129,66,40] 13 :=
  permutation_upper _ _ _ [320,36,72,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18678

def r23729 : Route 9 := (fun mask => (mask,id))

def c23729 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23729 : Upper (D 8) (R 8) [320,36,129,66] 13 := by
  apply FastRouting.sound _ _ [320,36,129,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23729 c23729
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23729_9
  · exact m23729_33
  · exact m23729_40
  · exact u18705
  · exact u18706
  · exact u18707

theorem m23730_3 : Upper (D 8) (R 8) [320,36,129,80,3] 13 :=
  permutation_upper _ _ _ [320,5,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17989

theorem m23730_9 : Upper (D 8) (R 8) [320,36,129,80,9] 13 :=
  permutation_upper _ _ _ [320,5,66,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18034

theorem m23730_10 : Upper (D 8) (R 8) [320,36,129,80,10] 13 :=
  permutation_upper _ _ _ [320,12,48,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18370

theorem m23730_33 : Upper (D 8) (R 8) [320,36,129,80,33] 13 :=
  permutation_upper _ _ _ [320,33,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18551

theorem m23730_34 : Upper (D 8) (R 8) [320,36,129,80,34] 13 :=
  permutation_upper _ _ _ [320,36,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18651

theorem m23730_40 : Upper (D 8) (R 8) [320,36,129,80,40] 13 :=
  permutation_upper _ _ _ [320,36,66,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18675

def r23730 : Route 9 := (fun mask => (mask,id))

def c23730 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23730 : Upper (D 8) (R 8) [320,36,129,80] 13 := by
  apply FastRouting.sound _ _ [320,36,129,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23730 c23730
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23730_3
  · exact m23730_9
  · exact m23730_10
  · exact m23730_33
  · exact m23730_34
  · exact m23730_40
  · exact u18708
  · exact u18709
  · exact u18710
  · exact u18711

theorem m23731_3 : Upper (D 8) (R 8) [320,36,129,96,3] 13 :=
  permutation_upper _ _ _ [320,5,40,129,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17990

theorem m23731_9 : Upper (D 8) (R 8) [320,36,129,96,9] 13 :=
  permutation_upper _ _ _ [320,5,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18077

theorem m23731_10 : Upper (D 8) (R 8) [320,36,129,96,10] 13 :=
  permutation_upper _ _ _ [320,12,48,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18373

theorem m23731_33 : Upper (D 8) (R 8) [320,36,129,96,33] 13 :=
  permutation_upper _ _ _ [320,33,40,129,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18553

theorem m23731_34 : Upper (D 8) (R 8) [320,36,129,96,34] 13 :=
  permutation_upper _ _ _ [320,36,40,129,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18652

theorem m23731_40 : Upper (D 8) (R 8) [320,36,129,96,40] 13 :=
  permutation_upper _ _ _ [320,36,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18692

def r23731 : Route 9 := (fun mask => (mask,id))

def c23731 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23731 : Upper (D 8) (R 8) [320,36,129,96] 13 := by
  apply FastRouting.sound _ _ [320,36,129,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23731 c23731
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23731_3
  · exact m23731_9
  · exact m23731_10
  · exact m23731_33
  · exact m23731_34
  · exact m23731_40
  · exact u18712
  · exact u18713
  · exact u18714
  · exact u18715

def b23732 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 321 38 133 137 122 122 122 250 378), lower := (rows 321 38 133 137 16 32 64 128 256), losses := [] }

theorem u23732 : Upper (D 8) (R 8) [320,36,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23733 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 133 138 121 121 121 249 377), lower := (rows 321 38 133 138 16 32 64 128 256), losses := [] }

theorem u23733 : Upper (D 8) (R 8) [320,36,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23734_3 : Upper (D 8) (R 8) [320,36,129,144,3] 13 :=
  permutation_upper _ _ _ [320,5,40,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17991

theorem m23734_9 : Upper (D 8) (R 8) [320,36,129,144,9] 13 :=
  permutation_upper _ _ _ [320,5,130,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18115

theorem m23734_10 : Upper (D 8) (R 8) [320,36,129,144,10] 13 :=
  permutation_upper _ _ _ [320,12,48,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18388

theorem m23734_33 : Upper (D 8) (R 8) [320,36,129,144,33] 13 :=
  permutation_upper _ _ _ [320,33,40,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18554

theorem m23734_34 : Upper (D 8) (R 8) [320,36,129,144,34] 13 :=
  permutation_upper _ _ _ [320,36,40,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18653

theorem m23734_40 : Upper (D 8) (R 8) [320,36,129,144,40] 13 :=
  permutation_upper _ _ _ [320,36,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18700

theorem m23734_65 : Upper (D 8) (R 8) [320,36,129,144,65] 13 :=
  permutation_upper _ _ _ [320,36,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18703

theorem m23734_66 : Upper (D 8) (R 8) [320,36,129,144,66] 13 :=
  permutation_upper _ _ _ [320,36,129,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18706

theorem m23734_72 : Upper (D 8) (R 8) [320,36,129,144,72] 13 :=
  permutation_upper _ _ _ [320,36,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18710

theorem m23734_96 : Upper (D 8) (R 8) [320,36,129,144,96] 13 :=
  permutation_upper _ _ _ [320,36,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18714

def r23734 : Route 9 := (fun mask => (mask,id))

def c23734 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23734 : Upper (D 8) (R 8) [320,36,129,144] 13 := by
  apply FastRouting.sound _ _ [320,36,129,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r23734 c23734
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23734_3
  · exact m23734_9
  · exact m23734_10
  · exact m23734_33
  · exact m23734_34
  · exact m23734_40
  · exact m23734_65
  · exact m23734_66
  · exact m23734_72
  · exact m23734_96

theorem m23735_3 : Upper (D 8) (R 8) [320,36,129,160,3] 13 :=
  permutation_upper _ _ _ [320,5,40,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17992

theorem m23735_9 : Upper (D 8) (R 8) [320,36,129,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18217

theorem m23735_10 : Upper (D 8) (R 8) [320,36,129,160,10] 13 :=
  permutation_upper _ _ _ [320,12,48,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18396

theorem m23735_33 : Upper (D 8) (R 8) [320,36,129,160,33] 13 :=
  permutation_upper _ _ _ [320,33,40,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18556

theorem m23735_34 : Upper (D 8) (R 8) [320,36,129,160,34] 13 :=
  permutation_upper _ _ _ [320,36,40,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18654

theorem m23735_40 : Upper (D 8) (R 8) [320,36,129,160,40] 13 :=
  permutation_upper _ _ _ [320,36,129,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18701

theorem m23735_65 : Upper (D 8) (R 8) [320,36,129,160,65] 13 :=
  permutation_upper _ _ _ [320,36,129,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18704

theorem m23735_66 : Upper (D 8) (R 8) [320,36,129,160,66] 13 :=
  permutation_upper _ _ _ [320,36,129,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18707

theorem m23735_72 : Upper (D 8) (R 8) [320,36,129,160,72] 13 :=
  permutation_upper _ _ _ [320,36,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18711

theorem m23735_96 : Upper (D 8) (R 8) [320,36,129,160,96] 13 :=
  permutation_upper _ _ _ [320,36,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18715

def r23735 : Route 9 := (fun mask => (mask,id))

def c23735 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23735 : Upper (D 8) (R 8) [320,36,129,160] 13 := by
  apply FastRouting.sound _ _ [320,36,129,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r23735 c23735
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23735_3
  · exact m23735_9
  · exact m23735_10
  · exact m23735_33
  · exact m23735_34
  · exact m23735_40
  · exact m23735_65
  · exact m23735_66
  · exact m23735_72
  · exact m23735_96

theorem m23736_3 : Upper (D 8) (R 8) [320,36,129,192,3] 13 :=
  permutation_upper _ _ _ [320,5,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17993

theorem m23736_9 : Upper (D 8) (R 8) [320,36,129,192,9] 13 :=
  permutation_upper _ _ _ [320,5,192,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18246

theorem m23736_10 : Upper (D 8) (R 8) [320,36,129,192,10] 13 :=
  permutation_upper _ _ _ [320,12,48,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18402

theorem m23736_33 : Upper (D 8) (R 8) [320,36,129,192,33] 13 :=
  permutation_upper _ _ _ [320,33,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18557

theorem m23736_34 : Upper (D 8) (R 8) [320,36,129,192,34] 13 :=
  permutation_upper _ _ _ [320,36,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18655

theorem m23736_40 : Upper (D 8) (R 8) [320,36,129,192,40] 13 :=
  permutation_upper _ _ _ [320,36,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18702

def r23736 : Route 9 := (fun mask => (mask,id))

def c23736 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23736 : Upper (D 8) (R 8) [320,36,129,192] 13 := by
  apply FastRouting.sound _ _ [320,36,129,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23736 c23736
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23736_3
  · exact m23736_9
  · exact m23736_10
  · exact m23736_33
  · exact m23736_34
  · exact m23736_40

theorem m23737_9 : Upper (D 8) (R 8) [320,36,130,48,9] 13 :=
  permutation_upper _ _ _ [320,5,34,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17922

theorem m23737_33 : Upper (D 8) (R 8) [320,36,130,48,33] 13 :=
  permutation_upper _ _ _ [320,33,34,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18508

theorem m23737_40 : Upper (D 8) (R 8) [320,36,130,48,40] 13 :=
  permutation_upper _ _ _ [320,36,34,48,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18631

theorem m23737_65 : Upper (D 8) (R 8) [320,36,130,48,65] 13 :=
  permutation_upper _ _ _ [320,36,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18671

theorem m23737_72 : Upper (D 8) (R 8) [320,36,130,48,72] 13 :=
  permutation_upper _ _ _ [320,36,66,48,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18676

theorem m23737_96 : Upper (D 8) (R 8) [320,36,130,48,96] 13 :=
  permutation_upper _ _ _ [320,36,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18694

theorem m23737_129 : Upper (D 8) (R 8) [320,36,130,48,129] 13 :=
  permutation_upper _ _ _ [320,36,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18700

def r23737 : Route 9 := (fun mask => (mask,id))

def c23737 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23737 : Upper (D 8) (R 8) [320,36,130,48] 13 := by
  apply FastRouting.sound _ _ [320,36,130,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23737 c23737
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23737_9
  · exact m23737_33
  · exact m23737_40
  · exact m23737_65
  · exact m23737_72
  · exact m23737_96
  · exact m23737_129
  · exact u18716
  · exact u18717
  · exact u18718

def b23738 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 134 73 185 185 249 185 441), lower := (rows 321 38 134 73 16 32 64 128 256), losses := [] }

theorem u23738 : Upper (D 8) (R 8) [320,36,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23739_9 : Upper (D 8) (R 8) [320,36,130,80,9] 13 :=
  permutation_upper _ _ _ [320,5,66,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18035

theorem m23739_33 : Upper (D 8) (R 8) [320,36,130,80,33] 13 :=
  permutation_upper _ _ _ [320,33,40,132,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18566

theorem m23739_40 : Upper (D 8) (R 8) [320,36,130,80,40] 13 :=
  permutation_upper _ _ _ [320,36,66,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18676

def r23739 : Route 9 := (fun mask => (mask,id))

def c23739 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23739 : Upper (D 8) (R 8) [320,36,130,80] 13 := by
  apply FastRouting.sound _ _ [320,36,130,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23739 c23739
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23739_9
  · exact m23739_33
  · exact m23739_40
  · exact u18719
  · exact u18720
  · exact u18721

theorem m23740_9 : Upper (D 8) (R 8) [320,36,130,96,9] 13 :=
  permutation_upper _ _ _ [320,5,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18079

theorem m23740_33 : Upper (D 8) (R 8) [320,36,130,96,33] 13 :=
  permutation_upper _ _ _ [320,33,40,132,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18567

theorem m23740_40 : Upper (D 8) (R 8) [320,36,130,96,40] 13 :=
  permutation_upper _ _ _ [320,36,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18694

def r23740 : Route 9 := (fun mask => (mask,id))

def c23740 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23740 : Upper (D 8) (R 8) [320,36,130,96] 13 := by
  apply FastRouting.sound _ _ [320,36,130,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23740 c23740
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23740_9
  · exact m23740_33
  · exact m23740_40
  · exact u18722
  · exact u18723
  · exact u18724

def b23741 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 134 137 121 121 121 249 377), lower := (rows 321 38 134 137 16 32 64 128 256), losses := [] }

theorem u23741 : Upper (D 8) (R 8) [320,36,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23742 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 134 152 121 105 105 233 361), lower := (rows 321 38 134 152 16 32 64 128 256), losses := [] }

theorem u23742 : Upper (D 8) (R 8) [320,36,130,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23743 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 134 168 121 121 121 249 377), lower := (rows 321 38 134 168 16 32 64 128 256), losses := [] }

theorem u23743 : Upper (D 8) (R 8) [320,36,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23744 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 134 200 57 57 121 185 313), lower := (rows 321 38 134 200 16 32 64 128 256), losses := [] }

theorem u23744 : Upper (D 8) (R 8) [320,36,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23745_3 : Upper (D 8) (R 8) [320,36,136,48,3] 13 :=
  permutation_upper _ _ _ [320,5,40,144,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18001

theorem m23745_33 : Upper (D 8) (R 8) [320,36,136,48,33] 13 :=
  permutation_upper _ _ _ [320,33,34,48,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18507

theorem m23745_34 : Upper (D 8) (R 8) [320,36,136,48,34] 13 :=
  permutation_upper _ _ _ [320,36,40,48,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18642

theorem m23745_65 : Upper (D 8) (R 8) [320,36,136,48,65] 13 :=
  permutation_upper _ _ _ [320,36,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18670

theorem m23745_66 : Upper (D 8) (R 8) [320,36,136,48,66] 13 :=
  permutation_upper _ _ _ [320,36,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18679

theorem m23745_96 : Upper (D 8) (R 8) [320,36,136,48,96] 13 :=
  permutation_upper _ _ _ [320,36,96,48,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18693

theorem m23745_129 : Upper (D 8) (R 8) [320,36,136,48,129] 13 :=
  permutation_upper _ _ _ [320,36,129,48,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18699

def r23745 : Route 9 := (fun mask => (mask,id))

def c23745 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23745 : Upper (D 8) (R 8) [320,36,136,48] 13 := by
  apply FastRouting.sound _ _ [320,36,136,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23745 c23745
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23745_3
  · exact m23745_33
  · exact m23745_34
  · exact m23745_65
  · exact m23745_66
  · exact m23745_96
  · exact m23745_129
  · exact u18725
  · exact u18726
  · exact u18727

def b23746 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 38 140 73 179 179 243 179 435), lower := (rows 321 38 140 73 16 32 64 128 256), losses := [] }

theorem u23746 : Upper (D 8) (R 8) [320,36,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23747 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 38 140 74 177 177 241 177 433), lower := (rows 321 38 140 74 16 32 64 128 256), losses := [] }

theorem u23747 : Upper (D 8) (R 8) [320,36,136,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23748_3 : Upper (D 8) (R 8) [320,36,136,80,3] 13 :=
  permutation_upper _ _ _ [320,5,40,144,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18003

theorem m23748_33 : Upper (D 8) (R 8) [320,36,136,80,33] 13 :=
  permutation_upper _ _ _ [320,33,40,144,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18573

theorem m23748_34 : Upper (D 8) (R 8) [320,36,136,80,34] 13 :=
  permutation_upper _ _ _ [320,36,40,144,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18660

def r23748 : Route 9 := (fun mask => (mask,id))

def c23748 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23748 : Upper (D 8) (R 8) [320,36,136,80] 13 := by
  apply FastRouting.sound _ _ [320,36,136,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23748 c23748
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23748_3
  · exact m23748_33
  · exact m23748_34
  · exact u18732
  · exact u18733
  · exact u18734

theorem m23749_3 : Upper (D 8) (R 8) [320,36,136,96,3] 13 :=
  permutation_upper _ _ _ [320,5,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18004

theorem m23749_33 : Upper (D 8) (R 8) [320,36,136,96,33] 13 :=
  permutation_upper _ _ _ [320,33,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18575

theorem m23749_34 : Upper (D 8) (R 8) [320,36,136,96,34] 13 :=
  permutation_upper _ _ _ [320,36,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18661

def r23749 : Route 9 := (fun mask => (mask,id))

def c23749 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23749 : Upper (D 8) (R 8) [320,36,136,96] 13 := by
  apply FastRouting.sound _ _ [320,36,136,96] 13 (by decide) (choices 2) [3,33,34,129,130,160] r23749 c23749
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23749_3
  · exact m23749_33
  · exact m23749_34
  · exact u18735
  · exact u18736
  · exact u18737

def b23750 : PairBound 9 := { available := 115, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 137 115 115 115 243 371), lower := (rows 321 38 140 137 16 32 64 128 256), losses := [] }

theorem u23750 : Upper (D 8) (R 8) [320,36,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23751 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 138 113 113 113 241 369), lower := (rows 321 38 140 138 16 32 64 128 256), losses := [] }

theorem u23751 : Upper (D 8) (R 8) [320,36,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23752 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 152 115 99 99 227 355), lower := (rows 321 38 140 152 16 32 64 128 256), losses := [] }

theorem u23752 : Upper (D 8) (R 8) [320,36,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23753 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 140 168 115 115 115 243 371), lower := (rows 321 38 140 168 16 32 64 128 256), losses := [] }

theorem u23753 : Upper (D 8) (R 8) [320,36,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23754 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 140 200 51 51 115 179 307), lower := (rows 321 38 140 200 16 32 64 128 256), losses := [] }

theorem u23754 : Upper (D 8) (R 8) [320,36,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23755_9 : Upper (D 8) (R 8) [320,36,144,66,9] 13 :=
  permutation_upper _ _ _ [320,5,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18049

theorem m23755_33 : Upper (D 8) (R 8) [320,36,144,66,33] 13 :=
  permutation_upper _ _ _ [320,33,40,130,68] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18559

theorem m23755_40 : Upper (D 8) (R 8) [320,36,144,66,40] 13 :=
  permutation_upper _ _ _ [320,36,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18679

theorem m23755_129 : Upper (D 8) (R 8) [320,36,144,66,129] 13 :=
  permutation_upper _ _ _ [320,36,136,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18738

theorem m23755_136 : Upper (D 8) (R 8) [320,36,144,66,136] 13 :=
  permutation_upper _ _ _ [320,36,136,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18741

theorem m23755_160 : Upper (D 8) (R 8) [320,36,144,66,160] 13 :=
  permutation_upper _ _ _ [320,36,136,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18743

def r23755 : Route 9 := (fun mask => (mask,id))

def c23755 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23755 : Upper (D 8) (R 8) [320,36,144,66] 13 := by
  apply FastRouting.sound _ _ [320,36,144,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23755 c23755
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23755_9
  · exact m23755_33
  · exact m23755_40
  · exact m23755_129
  · exact m23755_136
  · exact m23755_160

theorem m23756_3 : Upper (D 8) (R 8) [320,36,144,96,3] 13 :=
  permutation_upper _ _ _ [320,5,40,130,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17996

theorem m23756_9 : Upper (D 8) (R 8) [320,36,144,96,9] 13 :=
  permutation_upper _ _ _ [320,5,96,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18078

theorem m23756_10 : Upper (D 8) (R 8) [320,36,144,96,10] 13 :=
  permutation_upper _ _ _ [320,12,48,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18374

theorem m23756_33 : Upper (D 8) (R 8) [320,36,144,96,33] 13 :=
  permutation_upper _ _ _ [320,33,40,130,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18560

theorem m23756_34 : Upper (D 8) (R 8) [320,36,144,96,34] 13 :=
  permutation_upper _ _ _ [320,36,40,130,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18656

theorem m23756_40 : Upper (D 8) (R 8) [320,36,144,96,40] 13 :=
  permutation_upper _ _ _ [320,36,96,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18693

theorem m23756_129 : Upper (D 8) (R 8) [320,36,144,96,129] 13 :=
  permutation_upper _ _ _ [320,36,136,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18739

theorem m23756_130 : Upper (D 8) (R 8) [320,36,144,96,130] 13 :=
  permutation_upper _ _ _ [320,36,136,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18740

theorem m23756_136 : Upper (D 8) (R 8) [320,36,144,96,136] 13 :=
  permutation_upper _ _ _ [320,36,136,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18742

theorem m23756_160 : Upper (D 8) (R 8) [320,36,144,96,160] 13 :=
  permutation_upper _ _ _ [320,36,136,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18744

def r23756 : Route 9 := (fun mask => (mask,id))

def c23756 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23756 : Upper (D 8) (R 8) [320,36,144,96] 13 := by
  apply FastRouting.sound _ _ [320,36,144,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23756 c23756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23756_3
  · exact m23756_9
  · exact m23756_10
  · exact m23756_33
  · exact m23756_34
  · exact m23756_40
  · exact m23756_129
  · exact m23756_130
  · exact m23756_136
  · exact m23756_160

theorem m23757_3 : Upper (D 8) (R 8) [320,36,144,129,3] 13 :=
  permutation_upper _ _ _ [320,5,40,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17997

theorem m23757_9 : Upper (D 8) (R 8) [320,36,144,129,9] 13 :=
  permutation_upper _ _ _ [320,5,129,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18094

theorem m23757_10 : Upper (D 8) (R 8) [320,36,144,129,10] 13 :=
  permutation_upper _ _ _ [320,12,48,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18382

theorem m23757_33 : Upper (D 8) (R 8) [320,36,144,129,33] 13 :=
  permutation_upper _ _ _ [320,33,40,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18561

theorem m23757_34 : Upper (D 8) (R 8) [320,36,144,129,34] 13 :=
  permutation_upper _ _ _ [320,36,40,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18657

theorem m23757_40 : Upper (D 8) (R 8) [320,36,144,129,40] 13 :=
  permutation_upper _ _ _ [320,36,129,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18699

theorem m23757_65 : Upper (D 8) (R 8) [320,36,144,129,65] 13 :=
  permutation_upper _ _ _ [320,36,136,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18728

theorem m23757_66 : Upper (D 8) (R 8) [320,36,144,129,66] 13 :=
  permutation_upper _ _ _ [320,36,136,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18730

theorem m23757_72 : Upper (D 8) (R 8) [320,36,144,129,72] 13 :=
  permutation_upper _ _ _ [320,36,136,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18732

theorem m23757_96 : Upper (D 8) (R 8) [320,36,144,129,96] 13 :=
  permutation_upper _ _ _ [320,36,136,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18735

def r23757 : Route 9 := (fun mask => (mask,id))

def c23757 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23757 : Upper (D 8) (R 8) [320,36,144,129] 13 := by
  apply FastRouting.sound _ _ [320,36,144,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r23757 c23757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23757_3
  · exact m23757_9
  · exact m23757_10
  · exact m23757_33
  · exact m23757_34
  · exact m23757_40
  · exact m23757_65
  · exact m23757_66
  · exact m23757_72
  · exact m23757_96

def b23758 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 148 138 121 105 105 233 361), lower := (rows 321 38 148 138 16 32 64 128 256), losses := [] }

theorem u23758 : Upper (D 8) (R 8) [320,36,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23759_3 : Upper (D 8) (R 8) [320,36,144,160,3] 13 :=
  permutation_upper _ _ _ [320,5,40,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17998

theorem m23759_9 : Upper (D 8) (R 8) [320,36,144,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18218

theorem m23759_10 : Upper (D 8) (R 8) [320,36,144,160,10] 13 :=
  permutation_upper _ _ _ [320,12,48,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18397

theorem m23759_33 : Upper (D 8) (R 8) [320,36,144,160,33] 13 :=
  permutation_upper _ _ _ [320,33,40,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18563

theorem m23759_34 : Upper (D 8) (R 8) [320,36,144,160,34] 13 :=
  permutation_upper _ _ _ [320,36,40,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18658

theorem m23759_40 : Upper (D 8) (R 8) [320,36,144,160,40] 13 :=
  permutation_upper _ _ _ [320,36,136,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18726

theorem m23759_65 : Upper (D 8) (R 8) [320,36,144,160,65] 13 :=
  permutation_upper _ _ _ [320,36,136,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18729

theorem m23759_66 : Upper (D 8) (R 8) [320,36,144,160,66] 13 :=
  permutation_upper _ _ _ [320,36,136,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18731

theorem m23759_72 : Upper (D 8) (R 8) [320,36,144,160,72] 13 :=
  permutation_upper _ _ _ [320,36,136,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18734

theorem m23759_96 : Upper (D 8) (R 8) [320,36,144,160,96] 13 :=
  permutation_upper _ _ _ [320,36,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18737

def r23759 : Route 9 := (fun mask => (mask,id))

def c23759 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23759 : Upper (D 8) (R 8) [320,36,144,160] 13 := by
  apply FastRouting.sound _ _ [320,36,144,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r23759 c23759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23759_3
  · exact m23759_9
  · exact m23759_10
  · exact m23759_33
  · exact m23759_34
  · exact m23759_40
  · exact m23759_65
  · exact m23759_66
  · exact m23759_72
  · exact m23759_96

#print axioms u23759
end Delivery.IrregularNine14.P08
