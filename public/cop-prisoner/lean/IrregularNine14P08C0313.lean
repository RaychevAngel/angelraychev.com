import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0117
import IrregularNine14P08C0118
import IrregularNine14P08C0119
import IrregularNine14P08C0120

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r18780 : Route 9 := (fun mask => (mask,id))

def c18780 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18780 : Upper (D 8) (R 8) [6,9,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18780 c18780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7058
  · exact u7059
  · exact u7060
  · exact u7061
  · exact u7062
  · exact u7063
  · exact u7064
  · exact u7065
  · exact u7066
  · exact u7067

def b18781 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 100 200 433 433 497 433 433), lower := (rows 7 11 100 200 16 32 64 128 256), losses := [] }

theorem u18781 : Upper (D 8) (R 8) [6,9,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18782 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 265 240 240 240 240 496), lower := (rows 7 11 100 265 16 32 64 128 256), losses := [] }

theorem u18782 : Upper (D 8) (R 8) [6,9,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18783 : Route 9 := (fun mask => (mask,id))

def c18783 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18783 : Upper (D 8) (R 8) [6,9,96,272] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18783 c18783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7068
  · exact u7069
  · exact u7070
  · exact u7071
  · exact u7072
  · exact u7073

def r18784 : Route 9 := (fun mask => (mask,id))

def c18784 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18784 : Upper (D 8) (R 8) [6,9,96,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18784 c18784
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7074
  · exact u7075
  · exact u7076
  · exact u7077
  · exact u7078
  · exact u7079

def b18785 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 100 328 177 177 241 177 433), lower := (rows 7 11 100 328 16 32 64 128 256), losses := [] }

theorem u18785 : Upper (D 8) (R 8) [6,9,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18786 : Route 9 := (fun mask => (mask,id))

def c18786 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18786 : Upper (D 8) (R 8) [6,9,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18786 c18786
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7080
  · exact u7081
  · exact u7082
  · exact u7083
  · exact u7084
  · exact u7085

def b18787 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 196 25 496 480 480 480 480), lower := (rows 7 11 196 25 16 32 64 128 256), losses := [] }

theorem u18787 : Upper (D 8) (R 8) [6,9,192,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18788 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 196 41 496 496 496 496 496), lower := (rows 7 11 196 41 16 32 64 128 256), losses := [] }

theorem u18788 : Upper (D 8) (R 8) [6,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18789 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18789 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18789 : Upper (D 8) (R 8) [6,9,192,48] 13 := by
  apply FastRouting.sound _ _ [6,9,192,48] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r18789 c18789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7086
  · exact u7087
  · exact u7088
  · exact u7089
  · exact u7090
  · exact u7091
  · exact u7092

def b18790 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 11, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 196 73 432 432 496 432 432), lower := (rows 7 11 196 73 16 32 64 128 256), losses := [] }

theorem u18790 : Upper (D 8) (R 8) [6,9,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18791 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 196 88 433 417 481 417 417), lower := (rows 7 11 196 88 16 32 64 128 256), losses := [] }

theorem u18791 : Upper (D 8) (R 8) [6,9,192,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18792 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 196 104 433 433 497 433 433), lower := (rows 7 11 196 104 16 32 64 128 256), losses := [] }

theorem u18792 : Upper (D 8) (R 8) [6,9,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18793 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 11, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 196 200 305 305 369 433 305), lower := (rows 7 11 196 200 16 32 64 128 256), losses := [] }

theorem u18793 : Upper (D 8) (R 8) [6,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18794 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 196 265 240 240 240 240 496), lower := (rows 7 11 196 265 16 32 64 128 256), losses := [] }

theorem u18794 : Upper (D 8) (R 8) [6,9,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18795 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18795 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18795 : Upper (D 8) (R 8) [6,9,192,272] 13 := by
  apply FastRouting.sound _ _ [6,9,192,272] 13 (by decide) (choices 2) [33,65,96,192] r18795 c18795
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7093
  · exact u7094
  · exact u7095
  · exact u7096

def r18796 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18796 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18796 : Upper (D 8) (R 8) [6,9,192,288] 13 := by
  apply FastRouting.sound _ _ [6,9,192,288] 13 (by decide) (choices 2) [33,65,96,192] r18796 c18796
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7097
  · exact u7098
  · exact u7099
  · exact u7100

def b18797 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 196 328 177 177 241 177 433), lower := (rows 7 11 196 328 16 32 64 128 256), losses := [] }

theorem u18797 : Upper (D 8) (R 8) [6,9,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18798 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 276 41 240 224 224 224 480), lower := (rows 7 11 276 41 16 32 64 128 256), losses := [] }

theorem u18798 : Upper (D 8) (R 8) [6,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18799 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 276 73 240 224 224 224 480), lower := (rows 7 11 276 73 16 32 64 128 256), losses := [] }

theorem u18799 : Upper (D 8) (R 8) [6,9,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18800 : Route 9 := (fun mask => (mask,id))

def c18800 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18800 : Upper (D 8) (R 8) [6,9,272,96] 13 := by
  apply FastRouting.sound _ _ [6,9,272,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18800 c18800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7101
  · exact u7102
  · exact u7103
  · exact u7104
  · exact u7105
  · exact u7106

def r18801 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18801 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18801 : Upper (D 8) (R 8) [6,9,272,192] 13 := by
  apply FastRouting.sound _ _ [6,9,272,192] 13 (by decide) (choices 2) [33,65,96,192] r18801 c18801
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7107
  · exact u7108
  · exact u7109
  · exact u7110

def b18802 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 25 240 224 224 224 480), lower := (rows 7 11 292 25 16 32 64 128 256), losses := [] }

theorem u18802 : Upper (D 8) (R 8) [6,9,288,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18803 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 292 41 240 240 240 240 496), lower := (rows 7 11 292 41 16 32 64 128 256), losses := [] }

theorem u18803 : Upper (D 8) (R 8) [6,9,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18804 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18804 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18804 : Upper (D 8) (R 8) [6,9,288,48] 13 := by
  apply FastRouting.sound _ _ [6,9,288,48] 13 (by decide) (choices 2) [33,65,96,192] r18804 c18804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7111
  · exact u7112
  · exact u7113
  · exact u7114

def b18805 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 73 240 240 240 240 496), lower := (rows 7 11 292 73 16 32 64 128 256), losses := [] }

theorem u18805 : Upper (D 8) (R 8) [6,9,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18806 : Route 9 := (fun mask => (mask,id))

def c18806 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18806 : Upper (D 8) (R 8) [6,9,288,80] 13 := by
  apply FastRouting.sound _ _ [6,9,288,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18806 c18806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7115
  · exact u7116
  · exact u7117
  · exact u7118
  · exact u7119
  · exact u7120

def r18807 : Route 9 := (fun mask => (mask,id))

def c18807 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18807 : Upper (D 8) (R 8) [6,9,288,96] 13 := by
  apply FastRouting.sound _ _ [6,9,288,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18807 c18807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7121
  · exact u7122
  · exact u7123
  · exact u7124
  · exact u7125
  · exact u7126

def r18808 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18808 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18808 : Upper (D 8) (R 8) [6,9,288,192] 13 := by
  apply FastRouting.sound _ _ [6,9,288,192] 13 (by decide) (choices 2) [33,65,96,192] r18808 c18808
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7127
  · exact u7128
  · exact u7129
  · exact u7130

def b18809 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 324 25 240 224 224 224 480), lower := (rows 7 11 324 25 16 32 64 128 256), losses := [] }

theorem u18809 : Upper (D 8) (R 8) [6,9,320,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18810 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 324 41 240 240 240 240 496), lower := (rows 7 11 324 41 16 32 64 128 256), losses := [] }

theorem u18810 : Upper (D 8) (R 8) [6,9,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18811 : Route 9 := (fun mask => (mask,id))

def c18811 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18811 : Upper (D 8) (R 8) [6,9,320,48] 13 := by
  apply FastRouting.sound _ _ [6,9,320,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18811 c18811
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7131
  · exact u7132
  · exact u7133
  · exact u7134
  · exact u7135
  · exact u7136

def b18812 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 11, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 324 73 176 176 240 176 432), lower := (rows 7 11 324 73 16 32 64 128 256), losses := [] }

theorem u18812 : Upper (D 8) (R 8) [6,9,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18813 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 324 88 177 161 225 161 417), lower := (rows 7 11 324 88 16 32 64 128 256), losses := [] }

theorem u18813 : Upper (D 8) (R 8) [6,9,320,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18814 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 324 104 177 177 241 177 433), lower := (rows 7 11 324 104 16 32 64 128 256), losses := [] }

theorem u18814 : Upper (D 8) (R 8) [6,9,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18815 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 324 137 240 240 240 240 496), lower := (rows 7 11 324 137 16 32 64 128 256), losses := [] }

theorem u18815 : Upper (D 8) (R 8) [6,9,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18816 : Route 9 := (fun mask => (mask,id))

def c18816 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18816 : Upper (D 8) (R 8) [6,9,320,144] 13 := by
  apply FastRouting.sound _ _ [6,9,320,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18816 c18816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7137
  · exact u7138
  · exact u7139
  · exact u7140
  · exact u7141
  · exact u7142

def r18817 : Route 9 := (fun mask => (mask,id))

def c18817 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18817 : Upper (D 8) (R 8) [6,9,320,160] 13 := by
  apply FastRouting.sound _ _ [6,9,320,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18817 c18817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7143
  · exact u7144
  · exact u7145
  · exact u7146
  · exact u7147
  · exact u7148

def b18818 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 324 200 177 177 241 177 433), lower := (rows 7 11 324 200 16 32 64 128 256), losses := [] }

theorem u18818 : Upper (D 8) (R 8) [6,9,320,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18819 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 37 41 496 480 480 480 480), lower := (rows 7 26 37 41 16 32 64 128 256), losses := [] }

theorem u18819 : Upper (D 8) (R 8) [6,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18820 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 73 496 480 480 480 480), lower := (rows 7 26 37 73 16 32 64 128 256), losses := [] }

theorem u18820 : Upper (D 8) (R 8) [6,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18821_33 : Upper (D 8) (R 8) [6,24,33,96,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7149

theorem m18821_65 : Upper (D 8) (R 8) [6,24,33,96,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7153

theorem m18821_129 : Upper (D 8) (R 8) [6,24,33,96,129] 13 :=
  permutation_upper _ _ _ [6,24,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7154

def r18821 : Route 9 := (fun mask => (mask,id))

def c18821 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18821 : Upper (D 8) (R 8) [6,24,33,96] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18821 c18821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18821_33
  · exact m18821_65
  · exact u7159
  · exact m18821_129
  · exact u7160
  · exact u7161
  · exact u7162
  · exact u7163
  · exact u7164
  · exact u7165

theorem m18822_33 : Upper (D 8) (R 8) [6,24,33,192,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7150

theorem m18822_65 : Upper (D 8) (R 8) [6,24,33,192,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7155

theorem m18822_96 : Upper (D 8) (R 8) [6,24,33,192,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7161

def r18822 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18822 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18822 : Upper (D 8) (R 8) [6,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r18822 c18822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18822_33
  · exact m18822_65
  · exact m18822_96
  · exact u7166
  · exact u7167
  · exact u7168
  · exact u7169

def b18823 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 265 240 224 224 224 480), lower := (rows 7 26 37 265 16 32 64 128 256), losses := [] }

theorem u18823 : Upper (D 8) (R 8) [6,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18824_33 : Upper (D 8) (R 8) [6,24,33,288,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7151

theorem m18824_65 : Upper (D 8) (R 8) [6,24,33,288,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7156

theorem m18824_96 : Upper (D 8) (R 8) [6,24,33,288,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7163

theorem m18824_192 : Upper (D 8) (R 8) [6,24,33,288,192] 13 :=
  permutation_upper _ _ _ [6,24,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7168

def r18824 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18824 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18824 : Upper (D 8) (R 8) [6,24,33,288] 13 := by
  apply FastRouting.sound _ _ [6,24,33,288] 13 (by decide) (choices 2) [33,65,96,192] r18824 c18824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m18824_33
  · exact m18824_65
  · exact m18824_96
  · exact m18824_192

theorem m18825_33 : Upper (D 8) (R 8) [6,24,33,320,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7152

theorem m18825_65 : Upper (D 8) (R 8) [6,24,33,320,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7157

theorem m18825_96 : Upper (D 8) (R 8) [6,24,33,320,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7164

theorem m18825_129 : Upper (D 8) (R 8) [6,24,33,320,129] 13 :=
  permutation_upper _ _ _ [6,24,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7158

theorem m18825_160 : Upper (D 8) (R 8) [6,24,33,320,160] 13 :=
  permutation_upper _ _ _ [6,24,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7165

theorem m18825_192 : Upper (D 8) (R 8) [6,24,33,320,192] 13 :=
  permutation_upper _ _ _ [6,24,33,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7169

def r18825 : Route 9 := (fun mask => (mask,id))

def c18825 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18825 : Upper (D 8) (R 8) [6,24,33,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18825 c18825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18825_33
  · exact m18825_65
  · exact m18825_96
  · exact m18825_129
  · exact m18825_160
  · exact m18825_192

def b18826 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 41 496 480 480 480 480), lower := (rows 7 26 69 41 16 32 64 128 256), losses := [] }

theorem u18826 : Upper (D 8) (R 8) [6,24,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18827 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 69 73 432 416 480 416 416), lower := (rows 7 26 69 73 16 32 64 128 256), losses := [] }

theorem u18827 : Upper (D 8) (R 8) [6,24,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18828 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 69 104 433 417 481 417 417), lower := (rows 7 26 69 104 16 32 64 128 256), losses := [] }

theorem u18828 : Upper (D 8) (R 8) [6,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18829 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 137 496 480 480 480 480), lower := (rows 7 26 69 137 16 32 64 128 256), losses := [] }

theorem u18829 : Upper (D 8) (R 8) [6,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18830_33 : Upper (D 8) (R 8) [6,24,65,160,33] 13 :=
  permutation_upper _ _ _ [6,24,65,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7170

theorem m18830_65 : Upper (D 8) (R 8) [6,24,65,160,65] 13 :=
  permutation_upper _ _ _ [6,24,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7173

theorem m18830_96 : Upper (D 8) (R 8) [6,24,65,160,96] 13 :=
  permutation_upper _ _ _ [6,24,65,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7176

theorem m18830_129 : Upper (D 8) (R 8) [6,24,65,160,129] 13 :=
  permutation_upper _ _ _ [6,24,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7179

def r18830 : Route 9 := (fun mask => (mask,id))

def c18830 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18830 : Upper (D 8) (R 8) [6,24,65,160] 13 := by
  apply FastRouting.sound _ _ [6,24,65,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18830 c18830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18830_33
  · exact m18830_65
  · exact m18830_96
  · exact m18830_129
  · exact u7182
  · exact u7183
  · exact u7184
  · exact u7185
  · exact u7186
  · exact u7187

def b18831 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 69 200 433 417 481 417 417), lower := (rows 7 26 69 200 16 32 64 128 256), losses := [] }

theorem u18831 : Upper (D 8) (R 8) [6,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18832 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 265 240 224 224 224 480), lower := (rows 7 26 69 265 16 32 64 128 256), losses := [] }

theorem u18832 : Upper (D 8) (R 8) [6,24,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18833_33 : Upper (D 8) (R 8) [6,24,65,288,33] 13 :=
  permutation_upper _ _ _ [6,24,65,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7171

theorem m18833_65 : Upper (D 8) (R 8) [6,24,65,288,65] 13 :=
  permutation_upper _ _ _ [6,24,65,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7174

theorem m18833_96 : Upper (D 8) (R 8) [6,24,65,288,96] 13 :=
  permutation_upper _ _ _ [6,24,65,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7177

theorem m18833_129 : Upper (D 8) (R 8) [6,24,65,288,129] 13 :=
  permutation_upper _ _ _ [6,24,65,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7180

theorem m18833_160 : Upper (D 8) (R 8) [6,24,65,288,160] 13 :=
  permutation_upper _ _ _ [6,24,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7185

theorem m18833_192 : Upper (D 8) (R 8) [6,24,65,288,192] 13 :=
  permutation_upper _ _ _ [6,24,65,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7188

def r18833 : Route 9 := (fun mask => (mask,id))

def c18833 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18833 : Upper (D 8) (R 8) [6,24,65,288] 13 := by
  apply FastRouting.sound _ _ [6,24,65,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18833 c18833
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18833_33
  · exact m18833_65
  · exact m18833_96
  · exact m18833_129
  · exact m18833_160
  · exact m18833_192

def b18834 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 69 328 177 161 225 161 417), lower := (rows 7 26 69 328 16 32 64 128 256), losses := [] }

theorem u18834 : Upper (D 8) (R 8) [6,24,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18835_33 : Upper (D 8) (R 8) [6,24,65,384,33] 13 :=
  permutation_upper _ _ _ [6,24,65,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7172

theorem m18835_65 : Upper (D 8) (R 8) [6,24,65,384,65] 13 :=
  permutation_upper _ _ _ [6,24,65,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7175

theorem m18835_96 : Upper (D 8) (R 8) [6,24,65,384,96] 13 :=
  permutation_upper _ _ _ [6,24,65,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7178

theorem m18835_129 : Upper (D 8) (R 8) [6,24,65,384,129] 13 :=
  permutation_upper _ _ _ [6,24,65,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7181

theorem m18835_160 : Upper (D 8) (R 8) [6,24,65,384,160] 13 :=
  permutation_upper _ _ _ [6,24,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7187

theorem m18835_192 : Upper (D 8) (R 8) [6,24,65,384,192] 13 :=
  permutation_upper _ _ _ [6,24,65,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7189

def r18835 : Route 9 := (fun mask => (mask,id))

def c18835 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18835 : Upper (D 8) (R 8) [6,24,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,65,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18835 c18835
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18835_33
  · exact m18835_65
  · exact m18835_96
  · exact m18835_129
  · exact m18835_160
  · exact m18835_192

def r18836 : Route 9 := (fun mask => (mask,id))

def c18836 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18836 : Upper (D 8) (R 8) [6,24,96,33] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18836 c18836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7190
  · exact u7191
  · exact u7192
  · exact u7193
  · exact u7194
  · exact u7195
  · exact u7196
  · exact u7197
  · exact u7198
  · exact u7199

def b18837 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 100 73 433 417 481 417 417), lower := (rows 7 26 100 73 16 32 64 128 256), losses := [] }

theorem u18837 : Upper (D 8) (R 8) [6,24,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18838 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 433 417 481 417 417), lower := (rows 7 26 100 104 16 32 64 128 256), losses := [] }

theorem u18838 : Upper (D 8) (R 8) [6,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18839_33 : Upper (D 8) (R 8) [6,24,96,129,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7193

theorem m18839_65 : Upper (D 8) (R 8) [6,24,96,129,65] 13 :=
  permutation_upper _ _ _ [6,24,96,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7200

theorem m18839_96 : Upper (D 8) (R 8) [6,24,96,129,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7205

def r18839 : Route 9 := (fun mask => (mask,id))

def c18839 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18839 : Upper (D 8) (R 8) [6,24,96,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18839 c18839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18839_33
  · exact m18839_65
  · exact m18839_96
  · exact u7210
  · exact u7211
  · exact u7212
  · exact u7213
  · exact u7214
  · exact u7215
  · exact u7216

#print axioms u18839
end Delivery.IrregularNine14.P08
