import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0180
import IrregularNine14P08C0181
import IrregularNine14P08C0182
import IrregularNine14P08C0183
import IrregularNine14P08C0184

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20160 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 392 113 113 113 241 369), lower := (rows 67 38 140 392 16 32 64 128 256), losses := [] }

theorem u20160 : Upper (D 8) (R 8) [66,36,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20161 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 25 248 232 232 232 488), lower := (rows 67 38 261 25 16 32 64 128 256), losses := [] }

theorem u20161 : Upper (D 8) (R 8) [66,36,257,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20162 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 41 248 248 248 248 504), lower := (rows 67 38 261 41 16 32 64 128 256), losses := [] }

theorem u20162 : Upper (D 8) (R 8) [66,36,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20163_9 : Upper (D 8) (R 8) [66,36,257,48,9] 13 :=
  permutation_upper _ _ _ [66,36,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10849

theorem m20163_33 : Upper (D 8) (R 8) [66,36,257,48,33] 13 :=
  permutation_upper _ _ _ [66,36,257,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10855

def r20163 : Route 9 := (fun mask => (mask,id))

def c20163 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20163 : Upper (D 8) (R 8) [66,36,257,48] 13 := by
  apply FastRouting.sound _ _ [66,36,257,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20163 c20163
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20163_9
  · exact m20163_33
  · exact u10861
  · exact u10862
  · exact u10863
  · exact u10864
  · exact u10865
  · exact u10866
  · exact u10867
  · exact u10868

def b20164 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 261 73 184 184 248 184 440), lower := (rows 67 38 261 73 16 32 64 128 256), losses := [] }

theorem u20164 : Upper (D 8) (R 8) [66,36,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20165_9 : Upper (D 8) (R 8) [66,36,257,80,9] 13 :=
  permutation_upper _ _ _ [66,36,257,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10850

theorem m20165_33 : Upper (D 8) (R 8) [66,36,257,80,33] 13 :=
  permutation_upper _ _ _ [66,36,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10856

theorem m20165_40 : Upper (D 8) (R 8) [66,36,257,80,40] 13 :=
  permutation_upper _ _ _ [66,36,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10863

def r20165 : Route 9 := (fun mask => (mask,id))

def c20165 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20165 : Upper (D 8) (R 8) [66,36,257,80] 13 := by
  apply FastRouting.sound _ _ [66,36,257,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20165 c20165
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20165_9
  · exact m20165_33
  · exact m20165_40
  · exact u10871
  · exact u10872
  · exact u10873

theorem m20166_9 : Upper (D 8) (R 8) [66,36,257,96,9] 13 :=
  permutation_upper _ _ _ [66,36,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10851

theorem m20166_33 : Upper (D 8) (R 8) [66,36,257,96,33] 13 :=
  permutation_upper _ _ _ [66,36,257,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10857

theorem m20166_40 : Upper (D 8) (R 8) [66,36,257,96,40] 13 :=
  permutation_upper _ _ _ [66,36,257,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10864

def r20166 : Route 9 := (fun mask => (mask,id))

def c20166 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20166 : Upper (D 8) (R 8) [66,36,257,96] 13 := by
  apply FastRouting.sound _ _ [66,36,257,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20166 c20166
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20166_9
  · exact m20166_33
  · exact m20166_40
  · exact u10874
  · exact u10875
  · exact u10876

def b20167 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 137 248 248 248 248 504), lower := (rows 67 38 261 137 16 32 64 128 256), losses := [] }

theorem u20167 : Upper (D 8) (R 8) [66,36,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20168_9 : Upper (D 8) (R 8) [66,36,257,144,9] 13 :=
  permutation_upper _ _ _ [66,36,257,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10852

theorem m20168_33 : Upper (D 8) (R 8) [66,36,257,144,33] 13 :=
  permutation_upper _ _ _ [66,36,257,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10858

theorem m20168_40 : Upper (D 8) (R 8) [66,36,257,144,40] 13 :=
  permutation_upper _ _ _ [66,36,257,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10866

theorem m20168_65 : Upper (D 8) (R 8) [66,36,257,144,65] 13 :=
  permutation_upper _ _ _ [66,36,257,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10869

theorem m20168_72 : Upper (D 8) (R 8) [66,36,257,144,72] 13 :=
  permutation_upper _ _ _ [66,36,257,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10872

theorem m20168_96 : Upper (D 8) (R 8) [66,36,257,144,96] 13 :=
  permutation_upper _ _ _ [66,36,257,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10875

theorem m20168_129 : Upper (D 8) (R 8) [66,36,257,144,129] 13 :=
  permutation_upper _ _ _ [66,36,257,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10877

def r20168 : Route 9 := (fun mask => (mask,id))

def c20168 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20168 : Upper (D 8) (R 8) [66,36,257,144] 13 := by
  apply FastRouting.sound _ _ [66,36,257,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20168 c20168
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20168_9
  · exact m20168_33
  · exact m20168_40
  · exact m20168_65
  · exact m20168_72
  · exact m20168_96
  · exact m20168_129
  · exact u10880
  · exact u10881
  · exact u10882

theorem m20169_9 : Upper (D 8) (R 8) [66,36,257,160,9] 13 :=
  permutation_upper _ _ _ [66,36,257,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10853

theorem m20169_33 : Upper (D 8) (R 8) [66,36,257,160,33] 13 :=
  permutation_upper _ _ _ [66,36,257,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10859

theorem m20169_40 : Upper (D 8) (R 8) [66,36,257,160,40] 13 :=
  permutation_upper _ _ _ [66,36,257,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10867

theorem m20169_65 : Upper (D 8) (R 8) [66,36,257,160,65] 13 :=
  permutation_upper _ _ _ [66,36,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10870

theorem m20169_72 : Upper (D 8) (R 8) [66,36,257,160,72] 13 :=
  permutation_upper _ _ _ [66,36,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10873

theorem m20169_96 : Upper (D 8) (R 8) [66,36,257,160,96] 13 :=
  permutation_upper _ _ _ [66,36,257,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10876

theorem m20169_129 : Upper (D 8) (R 8) [66,36,257,160,129] 13 :=
  permutation_upper _ _ _ [66,36,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10878

theorem m20169_136 : Upper (D 8) (R 8) [66,36,257,160,136] 13 :=
  permutation_upper _ _ _ [66,36,257,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10881

def r20169 : Route 9 := (fun mask => (mask,id))

def c20169 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20169 : Upper (D 8) (R 8) [66,36,257,160] 13 := by
  apply FastRouting.sound _ _ [66,36,257,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20169 c20169
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20169_9
  · exact m20169_33
  · exact m20169_40
  · exact m20169_65
  · exact m20169_72
  · exact m20169_96
  · exact m20169_129
  · exact m20169_136
  · exact u10883
  · exact u10884

theorem m20170_9 : Upper (D 8) (R 8) [66,36,257,192,9] 13 :=
  permutation_upper _ _ _ [66,36,257,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10854

theorem m20170_33 : Upper (D 8) (R 8) [66,36,257,192,33] 13 :=
  permutation_upper _ _ _ [66,36,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10860

theorem m20170_40 : Upper (D 8) (R 8) [66,36,257,192,40] 13 :=
  permutation_upper _ _ _ [66,36,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10868

theorem m20170_129 : Upper (D 8) (R 8) [66,36,257,192,129] 13 :=
  permutation_upper _ _ _ [66,36,257,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10879

theorem m20170_136 : Upper (D 8) (R 8) [66,36,257,192,136] 13 :=
  permutation_upper _ _ _ [66,36,257,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10882

theorem m20170_160 : Upper (D 8) (R 8) [66,36,257,192,160] 13 :=
  permutation_upper _ _ _ [66,36,257,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10884

def r20170 : Route 9 := (fun mask => (mask,id))

def c20170 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20170 : Upper (D 8) (R 8) [66,36,257,192] 13 := by
  apply FastRouting.sound _ _ [66,36,257,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20170 c20170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20170_9
  · exact m20170_33
  · exact m20170_40
  · exact m20170_129
  · exact m20170_136
  · exact m20170_160

def r20171 : Route 9 := (fun mask => (mask,id))

def c20171 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20171 : Upper (D 8) (R 8) [66,36,264,17] 13 := by
  apply FastRouting.sound _ _ [66,36,264,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20171 c20171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10885
  · exact u10886
  · exact u10887
  · exact u10888
  · exact u10889
  · exact u10890

def r20172 : Route 9 := (fun mask => (mask,id))

def c20172 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20172 : Upper (D 8) (R 8) [66,36,264,33] 13 := by
  apply FastRouting.sound _ _ [66,36,264,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20172 c20172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10891
  · exact u10892
  · exact u10893
  · exact u10894
  · exact u10895
  · exact u10896

def r20173 : Route 9 := (fun mask => (mask,id))

def c20173 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20173 : Upper (D 8) (R 8) [66,36,264,48] 13 := by
  apply FastRouting.sound _ _ [66,36,264,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20173 c20173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10897
  · exact u10898
  · exact u10899
  · exact u10900
  · exact u10901
  · exact u10902

def b20174 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 73 177 177 241 177 433), lower := (rows 67 38 268 73 16 32 64 128 256), losses := [] }

theorem u20174 : Upper (D 8) (R 8) [66,36,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20175 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 268 88 177 161 225 161 417), lower := (rows 67 38 268 88 16 32 64 128 256), losses := [] }

theorem u20175 : Upper (D 8) (R 8) [66,36,264,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20176 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 268 104 177 177 241 177 433), lower := (rows 67 38 268 104 16 32 64 128 256), losses := [] }

theorem u20176 : Upper (D 8) (R 8) [66,36,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20177 : Route 9 := (fun mask => (mask,id))

def c20177 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20177 : Upper (D 8) (R 8) [66,36,264,129] 13 := by
  apply FastRouting.sound _ _ [66,36,264,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20177 c20177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10903
  · exact u10904
  · exact u10905
  · exact u10906
  · exact u10907
  · exact u10908

def r20178 : Route 9 := (fun mask => (mask,id))

def c20178 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20178 : Upper (D 8) (R 8) [66,36,264,144] 13 := by
  apply FastRouting.sound _ _ [66,36,264,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20178 c20178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10909
  · exact u10910
  · exact u10911
  · exact u10912
  · exact u10913
  · exact u10914

def r20179 : Route 9 := (fun mask => (mask,id))

def c20179 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20179 : Upper (D 8) (R 8) [66,36,264,160] 13 := by
  apply FastRouting.sound _ _ [66,36,264,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20179 c20179
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10915
  · exact u10916
  · exact u10917
  · exact u10918
  · exact u10919
  · exact u10920

def b20180 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 268 200 177 177 241 177 433), lower := (rows 67 38 268 200 16 32 64 128 256), losses := [] }

theorem u20180 : Upper (D 8) (R 8) [66,36,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20181 : Route 9 := (fun mask => (mask,id))

def c20181 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20181 : Upper (D 8) (R 8) [66,36,384,17] 13 := by
  apply FastRouting.sound _ _ [66,36,384,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20181 c20181
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10921
  · exact u10922
  · exact u10923
  · exact u10924
  · exact u10925
  · exact u10926
  · exact u10927
  · exact u10928
  · exact u10929
  · exact u10930

theorem m20182_9 : Upper (D 8) (R 8) [66,36,384,33,9] 13 :=
  permutation_upper _ _ _ [66,36,384,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10922

def r20182 : Route 9 := (fun mask => (mask,id))

def c20182 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20182 : Upper (D 8) (R 8) [66,36,384,33] 13 := by
  apply FastRouting.sound _ _ [66,36,384,33] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20182 c20182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20182_9
  · exact u10931
  · exact u10932
  · exact u10933
  · exact u10934
  · exact u10935
  · exact u10936
  · exact u10937
  · exact u10938
  · exact u10939

theorem m20183_9 : Upper (D 8) (R 8) [66,36,384,48,9] 13 :=
  permutation_upper _ _ _ [66,36,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10923

theorem m20183_33 : Upper (D 8) (R 8) [66,36,384,48,33] 13 :=
  permutation_upper _ _ _ [66,36,384,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10932

def r20183 : Route 9 := (fun mask => (mask,id))

def c20183 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20183 : Upper (D 8) (R 8) [66,36,384,48] 13 := by
  apply FastRouting.sound _ _ [66,36,384,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20183 c20183
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20183_9
  · exact m20183_33
  · exact u10940
  · exact u10941
  · exact u10942
  · exact u10943
  · exact u10944
  · exact u10945
  · exact u10946
  · exact u10947

def b20184 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 73 185 185 249 185 441), lower := (rows 67 38 388 73 16 32 64 128 256), losses := [] }

theorem u20184 : Upper (D 8) (R 8) [66,36,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20185_9 : Upper (D 8) (R 8) [66,36,384,80,9] 13 :=
  permutation_upper _ _ _ [66,36,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10925

theorem m20185_33 : Upper (D 8) (R 8) [66,36,384,80,33] 13 :=
  permutation_upper _ _ _ [66,36,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10934

theorem m20185_40 : Upper (D 8) (R 8) [66,36,384,80,40] 13 :=
  permutation_upper _ _ _ [66,36,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10942

def r20185 : Route 9 := (fun mask => (mask,id))

def c20185 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20185 : Upper (D 8) (R 8) [66,36,384,80] 13 := by
  apply FastRouting.sound _ _ [66,36,384,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20185 c20185
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20185_9
  · exact m20185_33
  · exact m20185_40
  · exact u10950
  · exact u10951
  · exact u10952

theorem m20186_9 : Upper (D 8) (R 8) [66,36,384,96,9] 13 :=
  permutation_upper _ _ _ [66,36,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10926

theorem m20186_33 : Upper (D 8) (R 8) [66,36,384,96,33] 13 :=
  permutation_upper _ _ _ [66,36,384,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10935

theorem m20186_40 : Upper (D 8) (R 8) [66,36,384,96,40] 13 :=
  permutation_upper _ _ _ [66,36,384,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10943

def r20186 : Route 9 := (fun mask => (mask,id))

def c20186 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20186 : Upper (D 8) (R 8) [66,36,384,96] 13 := by
  apply FastRouting.sound _ _ [66,36,384,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20186 c20186
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20186_9
  · exact m20186_33
  · exact m20186_40
  · exact u10953
  · exact u10954
  · exact u10955

def b20187 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 67 38 388 137 121 121 121 249 377), lower := (rows 67 38 388 137 16 32 64 128 256), losses := [] }

theorem u20187 : Upper (D 8) (R 8) [66,36,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20188_9 : Upper (D 8) (R 8) [66,36,384,144,9] 13 :=
  permutation_upper _ _ _ [66,36,384,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10928

theorem m20188_33 : Upper (D 8) (R 8) [66,36,384,144,33] 13 :=
  permutation_upper _ _ _ [66,36,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10937

theorem m20188_40 : Upper (D 8) (R 8) [66,36,384,144,40] 13 :=
  permutation_upper _ _ _ [66,36,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10945

theorem m20188_65 : Upper (D 8) (R 8) [66,36,384,144,65] 13 :=
  permutation_upper _ _ _ [66,36,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10948

theorem m20188_72 : Upper (D 8) (R 8) [66,36,384,144,72] 13 :=
  permutation_upper _ _ _ [66,36,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10951

theorem m20188_96 : Upper (D 8) (R 8) [66,36,384,144,96] 13 :=
  permutation_upper _ _ _ [66,36,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10954

def r20188 : Route 9 := (fun mask => (mask,id))

def c20188 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20188 : Upper (D 8) (R 8) [66,36,384,144] 13 := by
  apply FastRouting.sound _ _ [66,36,384,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20188 c20188
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20188_9
  · exact m20188_33
  · exact m20188_40
  · exact m20188_65
  · exact m20188_72
  · exact m20188_96

theorem m20189_9 : Upper (D 8) (R 8) [66,36,384,160,9] 13 :=
  permutation_upper _ _ _ [66,36,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10929

theorem m20189_33 : Upper (D 8) (R 8) [66,36,384,160,33] 13 :=
  permutation_upper _ _ _ [66,36,384,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10938

theorem m20189_40 : Upper (D 8) (R 8) [66,36,384,160,40] 13 :=
  permutation_upper _ _ _ [66,36,384,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10946

theorem m20189_65 : Upper (D 8) (R 8) [66,36,384,160,65] 13 :=
  permutation_upper _ _ _ [66,36,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10949

theorem m20189_72 : Upper (D 8) (R 8) [66,36,384,160,72] 13 :=
  permutation_upper _ _ _ [66,36,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10952

theorem m20189_96 : Upper (D 8) (R 8) [66,36,384,160,96] 13 :=
  permutation_upper _ _ _ [66,36,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10955

def r20189 : Route 9 := (fun mask => (mask,id))

def c20189 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u20189 : Upper (D 8) (R 8) [66,36,384,160] 13 := by
  apply FastRouting.sound _ _ [66,36,384,160] 13 (by decide) (choices 2) [9,33,40,65,72,96] r20189 c20189
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20189_9
  · exact m20189_33
  · exact m20189_40
  · exact m20189_65
  · exact m20189_72
  · exact m20189_96

theorem m20190_9 : Upper (D 8) (R 8) [66,36,384,192,9] 13 :=
  permutation_upper _ _ _ [66,36,384,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10930

theorem m20190_33 : Upper (D 8) (R 8) [66,36,384,192,33] 13 :=
  permutation_upper _ _ _ [66,36,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10939

theorem m20190_40 : Upper (D 8) (R 8) [66,36,384,192,40] 13 :=
  permutation_upper _ _ _ [66,36,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10947

def r20190 : Route 9 := (fun mask => (mask,id))

def c20190 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u20190 : Upper (D 8) (R 8) [66,36,384,192] 13 := by
  apply FastRouting.sound _ _ [66,36,384,192] 13 (by decide) (choices 2) [9,33,40] r20190 c20190
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m20190_9
  · exact m20190_33
  · exact m20190_40

def b20191 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 28 496 480 480 480 480), lower := (rows 67 131 13 28 16 32 64 128 256), losses := [] }

theorem u20191 : Upper (D 8) (R 8) [66,129,9,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20192 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 44 496 496 496 496 496), lower := (rows 67 131 13 44 16 32 64 128 256), losses := [] }

theorem u20192 : Upper (D 8) (R 8) [66,129,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20193 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 13 76 432 432 496 432 432), lower := (rows 67 131 13 76 16 32 64 128 256), losses := [] }

theorem u20193 : Upper (D 8) (R 8) [66,129,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20194 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 104 436 436 500 436 436), lower := (rows 67 131 13 104 16 32 64 128 256), losses := [] }

theorem u20194 : Upper (D 8) (R 8) [66,129,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20195 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 13 140 368 368 368 496 368), lower := (rows 67 131 13 140 16 32 64 128 256), losses := [] }

theorem u20195 : Upper (D 8) (R 8) [66,129,9,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20196 : PairBound 9 := { available := 372, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 168 372 372 372 500 372), lower := (rows 67 131 13 168 16 32 64 128 256), losses := [] }

theorem u20196 : Upper (D 8) (R 8) [66,129,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20197 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 268 240 240 240 240 496), lower := (rows 67 131 13 268 16 32 64 128 256), losses := [] }

theorem u20197 : Upper (D 8) (R 8) [66,129,9,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20198 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 296 244 244 244 244 500), lower := (rows 67 131 13 296 16 32 64 128 256), losses := [] }

theorem u20198 : Upper (D 8) (R 8) [66,129,9,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20199 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 328 180 180 244 180 436), lower := (rows 67 131 13 328 16 32 64 128 256), losses := [] }

theorem u20199 : Upper (D 8) (R 8) [66,129,9,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20200 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 392 116 116 116 244 372), lower := (rows 67 131 13 392 16 32 64 128 256), losses := [] }

theorem u20200 : Upper (D 8) (R 8) [66,129,9,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20201 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 21 44 504 488 488 488 488), lower := (rows 67 131 21 44 16 32 64 128 256), losses := [] }

theorem u20201 : Upper (D 8) (R 8) [66,129,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20202 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 21 76 440 424 488 424 424), lower := (rows 67 131 21 76 16 32 64 128 256), losses := [] }

theorem u20202 : Upper (D 8) (R 8) [66,129,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20203 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 21 104 444 428 492 428 428), lower := (rows 67 131 21 104 16 32 64 128 256), losses := [] }

theorem u20203 : Upper (D 8) (R 8) [66,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20204 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 21 140 376 360 360 488 360), lower := (rows 67 131 21 140 16 32 64 128 256), losses := [] }

theorem u20204 : Upper (D 8) (R 8) [66,129,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20205 : PairBound 9 := { available := 364, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 21 168 380 364 364 492 364), lower := (rows 67 131 21 168 16 32 64 128 256), losses := [] }

theorem u20205 : Upper (D 8) (R 8) [66,129,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20206 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 21 268 248 232 232 232 488), lower := (rows 67 131 21 268 16 32 64 128 256), losses := [] }

theorem u20206 : Upper (D 8) (R 8) [66,129,17,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20207 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 21 296 252 236 236 236 492), lower := (rows 67 131 21 296 16 32 64 128 256), losses := [] }

theorem u20207 : Upper (D 8) (R 8) [66,129,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20208 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 21 328 188 172 236 172 428), lower := (rows 67 131 21 328 16 32 64 128 256), losses := [] }

theorem u20208 : Upper (D 8) (R 8) [66,129,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20209 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 21 392 124 108 108 236 364), lower := (rows 67 131 21 392 16 32 64 128 256), losses := [] }

theorem u20209 : Upper (D 8) (R 8) [66,129,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20210 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 41 500 484 484 484 484), lower := (rows 67 131 28 41 16 32 64 128 256), losses := [] }

theorem u20210 : Upper (D 8) (R 8) [66,129,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20211_33 : Upper (D 8) (R 8) [66,129,24,36,33] 13 :=
  permutation_upper _ _ _ [66,129,24,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11019

def r20211 : Route 9 := (fun mask => (mask,id))

def c20211 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20211 : Upper (D 8) (R 8) [66,129,24,36] 13 := by
  apply FastRouting.sound _ _ [66,129,24,36] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20211 c20211
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20211_33
  · exact u11026
  · exact u11027
  · exact u11028
  · exact u11029
  · exact u11030
  · exact u11031
  · exact u11032
  · exact u11033
  · exact u11034

def b20212 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 73 436 420 484 420 420), lower := (rows 67 131 28 73 16 32 64 128 256), losses := [] }

theorem u20212 : Upper (D 8) (R 8) [66,129,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20213 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 131 28 76 433 417 481 417 417), lower := (rows 67 131 28 76 16 32 64 128 256), losses := [] }

theorem u20213 : Upper (D 8) (R 8) [66,129,24,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20214_5 : Upper (D 8) (R 8) [66,129,24,96,5] 13 :=
  permutation_upper _ _ _ [66,129,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10956

theorem m20214_33 : Upper (D 8) (R 8) [66,129,24,96,33] 13 :=
  permutation_upper _ _ _ [66,129,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11020

theorem m20214_36 : Upper (D 8) (R 8) [66,129,24,96,36] 13 :=
  permutation_upper _ _ _ [66,129,24,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11027

def r20214 : Route 9 := (fun mask => (mask,id))

def c20214 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20214 : Upper (D 8) (R 8) [66,129,24,96] 13 := by
  apply FastRouting.sound _ _ [66,129,24,96] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r20214 c20214
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20214_5
  · exact m20214_33
  · exact m20214_36
  · exact u11042
  · exact u11043
  · exact u11044
  · exact u11045
  · exact u11046
  · exact u11047
  · exact u11048

def b20215 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 131 28 137 372 356 356 484 356), lower := (rows 67 131 28 137 16 32 64 128 256), losses := [] }

theorem u20215 : Upper (D 8) (R 8) [66,129,24,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20216 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 131 28 140 369 353 353 481 353), lower := (rows 67 131 28 140 16 32 64 128 256), losses := [] }

theorem u20216 : Upper (D 8) (R 8) [66,129,24,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20217_5 : Upper (D 8) (R 8) [66,129,24,160,5] 13 :=
  permutation_upper _ _ _ [66,129,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10957

theorem m20217_33 : Upper (D 8) (R 8) [66,129,24,160,33] 13 :=
  permutation_upper _ _ _ [66,129,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11021

theorem m20217_36 : Upper (D 8) (R 8) [66,129,24,160,36] 13 :=
  permutation_upper _ _ _ [66,129,24,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11029

theorem m20217_65 : Upper (D 8) (R 8) [66,129,24,160,65] 13 :=
  permutation_upper _ _ _ [66,129,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11035

theorem m20217_68 : Upper (D 8) (R 8) [66,129,24,160,68] 13 :=
  permutation_upper _ _ _ [66,129,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11039

theorem m20217_96 : Upper (D 8) (R 8) [66,129,24,160,96] 13 :=
  permutation_upper _ _ _ [66,129,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11044

def r20217 : Route 9 := (fun mask => (mask,id))

def c20217 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u20217 : Upper (D 8) (R 8) [66,129,24,160] 13 := by
  apply FastRouting.sound _ _ [66,129,24,160] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r20217 c20217
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20217_5
  · exact m20217_33
  · exact m20217_36
  · exact m20217_65
  · exact m20217_68
  · exact m20217_96
  · exact u11054
  · exact u11055
  · exact u11056
  · exact u11057

def b20218 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 131 28 200 309 293 357 421 293), lower := (rows 67 131 28 200 16 32 64 128 256), losses := [] }

theorem u20218 : Upper (D 8) (R 8) [66,129,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20219 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 265 244 228 228 228 484), lower := (rows 67 131 28 265 16 32 64 128 256), losses := [] }

theorem u20219 : Upper (D 8) (R 8) [66,129,24,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u20219
end Delivery.IrregularNine14.P08
