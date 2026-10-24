import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0110
import IrregularNine14P05C0111
import IrregularNine14P05C0112
import IrregularNine14P05C0113

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9120 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 312, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 70 134 41 313 313 377 441 313), lower := (rows 7 70 134 41 16 32 64 128 256), losses := [] }

theorem u9120 : Upper (D 5) (R 5) [6,68,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9120
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9121 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 312, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 70 134 56 313 297 361 425 297), lower := (rows 7 70 134 56 16 32 64 128 256), losses := [] }

theorem u9121 : Upper (D 5) (R 5) [6,68,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9122 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 312, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 70 134 265 57 57 121 185 313), lower := (rows 7 70 134 265 16 32 64 128 256), losses := [] }

theorem u9122 : Upper (D 5) (R 5) [6,68,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9123 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 312, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 70 134 280 57 41 105 169 297), lower := (rows 7 70 134 280 16 32 64 128 256), losses := [] }

theorem u9123 : Upper (D 5) (R 5) [6,68,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9123
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9124 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 312, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 70 134 296 57 57 121 185 313), lower := (rows 7 70 134 296 16 32 64 128 256), losses := [] }

theorem u9124 : Upper (D 5) (R 5) [6,68,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9124
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9125 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 25 315 299 363 427 299), lower := (rows 7 70 140 25 16 32 64 128 256), losses := [] }

theorem u9125 : Upper (D 5) (R 5) [6,68,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9125
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9126 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 26 313 297 361 425 297), lower := (rows 7 70 140 26 16 32 64 128 256), losses := [] }

theorem u9126 : Upper (D 5) (R 5) [6,68,136,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9126
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9127 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 41 315 315 379 443 315), lower := (rows 7 70 140 41 16 32 64 128 256), losses := [] }

theorem u9127 : Upper (D 5) (R 5) [6,68,136,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9127
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9128 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 42 313 313 377 441 313), lower := (rows 7 70 140 42 16 32 64 128 256), losses := [] }

theorem u9128 : Upper (D 5) (R 5) [6,68,136,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9129 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 56 315 299 363 427 299), lower := (rows 7 70 140 56 16 32 64 128 256), losses := [] }

theorem u9129 : Upper (D 5) (R 5) [6,68,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9130 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 265 59 59 123 187 315), lower := (rows 7 70 140 265 16 32 64 128 256), losses := [] }

theorem u9130 : Upper (D 5) (R 5) [6,68,136,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9130
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9131 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 266 57 57 121 185 313), lower := (rows 7 70 140 266 16 32 64 128 256), losses := [] }

theorem u9131 : Upper (D 5) (R 5) [6,68,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9131
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9132 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 280 59 43 107 171 299), lower := (rows 7 70 140 280 16 32 64 128 256), losses := [] }

theorem u9132 : Upper (D 5) (R 5) [6,68,136,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9132
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9133 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 140 296 59 59 123 187 315), lower := (rows 7 70 140 296 16 32 64 128 256), losses := [] }

theorem u9133 : Upper (D 5) (R 5) [6,68,136,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9133
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9134 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 148 41 315 299 363 427 299), lower := (rows 7 70 148 41 16 32 64 128 256), losses := [] }

theorem u9134 : Upper (D 5) (R 5) [6,68,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9134
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9135 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 148 42 313 297 361 425 297), lower := (rows 7 70 148 42 16 32 64 128 256), losses := [] }

theorem u9135 : Upper (D 5) (R 5) [6,68,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9135
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9136 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 148 265 59 43 107 171 299), lower := (rows 7 70 148 265 16 32 64 128 256), losses := [] }

theorem u9136 : Upper (D 5) (R 5) [6,68,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9136
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9137 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 148 266 57 41 105 169 297), lower := (rows 7 70 148 266 16 32 64 128 256), losses := [] }

theorem u9137 : Upper (D 5) (R 5) [6,68,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9137
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9138 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 148 296 59 43 107 171 299), lower := (rows 7 70 148 296 16 32 64 128 256), losses := [] }

theorem u9138 : Upper (D 5) (R 5) [6,68,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9138
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9139 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 25 315 299 363 427 299), lower := (rows 7 70 164 25 16 32 64 128 256), losses := [] }

theorem u9139 : Upper (D 5) (R 5) [6,68,160,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9139
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9140 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 26 313 297 361 425 297), lower := (rows 7 70 164 26 16 32 64 128 256), losses := [] }

theorem u9140 : Upper (D 5) (R 5) [6,68,160,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9140
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9141 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 41 283 315 347 411 283), lower := (rows 7 70 164 41 16 32 64 128 256), losses := [] }

theorem u9141 : Upper (D 5) (R 5) [6,68,160,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9141
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9142 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 42 281 313 345 409 281), lower := (rows 7 70 164 42 16 32 64 128 256), losses := [] }

theorem u9142 : Upper (D 5) (R 5) [6,68,160,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9142
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9143 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 56 283 299 331 395 267), lower := (rows 7 70 164 56 16 32 64 128 256), losses := [] }

theorem u9143 : Upper (D 5) (R 5) [6,68,160,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9143
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9144 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 265 59 59 123 187 315), lower := (rows 7 70 164 265 16 32 64 128 256), losses := [] }

theorem u9144 : Upper (D 5) (R 5) [6,68,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9144
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9145 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 266 57 57 121 185 313), lower := (rows 7 70 164 266 16 32 64 128 256), losses := [] }

theorem u9145 : Upper (D 5) (R 5) [6,68,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9145
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9146 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 280 59 43 107 171 299), lower := (rows 7 70 164 280 16 32 64 128 256), losses := [] }

theorem u9146 : Upper (D 5) (R 5) [6,68,160,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9146
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9147 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 164 296 27 59 91 155 283), lower := (rows 7 70 164 296 16 32 64 128 256), losses := [] }

theorem u9147 : Upper (D 5) (R 5) [6,68,160,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9147
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9148 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 388 25 59 43 107 171 299), lower := (rows 7 70 388 25 16 32 64 128 256), losses := [] }

theorem u9148 : Upper (D 5) (R 5) [6,68,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9148
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9149 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 388 26 57 41 105 169 297), lower := (rows 7 70 388 26 16 32 64 128 256), losses := [] }

theorem u9149 : Upper (D 5) (R 5) [6,68,384,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9149
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9150 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 388 41 59 59 123 187 315), lower := (rows 7 70 388 41 16 32 64 128 256), losses := [] }

theorem u9150 : Upper (D 5) (R 5) [6,68,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9150
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9151 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 388 42 57 57 121 185 313), lower := (rows 7 70 388 42 16 32 64 128 256), losses := [] }

theorem u9151 : Upper (D 5) (R 5) [6,68,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9152 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 70 388 56 59 43 107 171 299), lower := (rows 7 70 388 56 16 32 64 128 256), losses := [] }

theorem u9152 : Upper (D 5) (R 5) [6,68,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9152
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9153_5 : Upper (D 5) (R 5) [6,72,136,17,5] 13 :=
  permutation_upper _ _ _ [6,72,136,17,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6614

theorem m9153_36 : Upper (D 5) (R 5) [6,72,136,17,36] 13 :=
  permutation_upper _ _ _ [6,72,136,17,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6617

theorem m9153_260 : Upper (D 5) (R 5) [6,72,136,17,260] 13 :=
  permutation_upper _ _ _ [6,72,136,17,258] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6619

def r9153 : Route 9 := (fun mask => (mask,id))

def c9153 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9153 : Upper (D 5) (R 5) [6,72,136,17] 13 := by
  apply FastRouting.sound _ _ [6,72,136,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9153 c9153
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6614
  · exact m9153_5
  · exact u6615
  · exact u6616
  · exact u6617
  · exact m9153_36
  · exact u6618
  · exact u6619
  · exact m9153_260
  · exact u6620

def b9154 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 140 26 309 293 357 421 293), lower := (rows 7 74 140 26 16 32 64 128 256), losses := [] }

theorem u9154 : Upper (D 5) (R 5) [6,72,136,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9154
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9155_5 : Upper (D 5) (R 5) [6,72,136,33,5] 13 :=
  permutation_upper _ _ _ [6,72,136,33,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6621

theorem m9155_36 : Upper (D 5) (R 5) [6,72,136,33,36] 13 :=
  permutation_upper _ _ _ [6,72,136,33,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6624

theorem m9155_260 : Upper (D 5) (R 5) [6,72,136,33,260] 13 :=
  permutation_upper _ _ _ [6,72,136,33,258] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6626

def r9155 : Route 9 := (fun mask => (mask,id))

def c9155 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9155 : Upper (D 5) (R 5) [6,72,136,33] 13 := by
  apply FastRouting.sound _ _ [6,72,136,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9155 c9155
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6621
  · exact m9155_5
  · exact u6622
  · exact u6623
  · exact u6624
  · exact m9155_36
  · exact u6625
  · exact u6626
  · exact m9155_260
  · exact u6627

def b9156 : PairBound 9 := { available := 309, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 140 42 309 309 373 437 309), lower := (rows 7 74 140 42 16 32 64 128 256), losses := [] }

theorem u9156 : Upper (D 5) (R 5) [6,72,136,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9156
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9157_5 : Upper (D 5) (R 5) [6,72,136,48,5] 13 :=
  permutation_upper _ _ _ [6,72,136,48,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6628

theorem m9157_36 : Upper (D 5) (R 5) [6,72,136,48,36] 13 :=
  permutation_upper _ _ _ [6,72,136,48,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6631

theorem m9157_260 : Upper (D 5) (R 5) [6,72,136,48,260] 13 :=
  permutation_upper _ _ _ [6,72,136,48,258] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6633

def r9157 : Route 9 := (fun mask => (mask,id))

def c9157 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9157 : Upper (D 5) (R 5) [6,72,136,48] 13 := by
  apply FastRouting.sound _ _ [6,72,136,48] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9157 c9157
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6628
  · exact m9157_5
  · exact u6629
  · exact u6630
  · exact u6631
  · exact m9157_36
  · exact u6632
  · exact u6633
  · exact m9157_260
  · exact u6634

theorem m9158_5 : Upper (D 5) (R 5) [6,72,136,257,5] 13 :=
  permutation_upper _ _ _ [6,72,136,257,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6635

theorem m9158_36 : Upper (D 5) (R 5) [6,72,136,257,36] 13 :=
  permutation_upper _ _ _ [6,72,136,257,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6638

def r9158 : Route 9 := (fun mask => (mask,id))

def c9158 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9158 : Upper (D 5) (R 5) [6,72,136,257] 13 := by
  apply FastRouting.sound _ _ [6,72,136,257] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9158 c9158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6635
  · exact m9158_5
  · exact u6636
  · exact u6637
  · exact u6638
  · exact m9158_36

def b9159 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 140 266 53 53 117 181 309), lower := (rows 7 74 140 266 16 32 64 128 256), losses := [] }

theorem u9159 : Upper (D 5) (R 5) [6,72,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9159
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9160_5 : Upper (D 5) (R 5) [6,72,136,272,5] 13 :=
  permutation_upper _ _ _ [6,72,136,272,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6639

theorem m9160_36 : Upper (D 5) (R 5) [6,72,136,272,36] 13 :=
  permutation_upper _ _ _ [6,72,136,272,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6642

def r9160 : Route 9 := (fun mask => (mask,id))

def c9160 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9160 : Upper (D 5) (R 5) [6,72,136,272] 13 := by
  apply FastRouting.sound _ _ [6,72,136,272] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9160 c9160
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6639
  · exact m9160_5
  · exact u6640
  · exact u6641
  · exact u6642
  · exact m9160_36

theorem m9161_5 : Upper (D 5) (R 5) [6,72,136,288,5] 13 :=
  permutation_upper _ _ _ [6,72,136,288,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6643

theorem m9161_36 : Upper (D 5) (R 5) [6,72,136,288,36] 13 :=
  permutation_upper _ _ _ [6,72,136,288,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6646

def r9161 : Route 9 := (fun mask => (mask,id))

def c9161 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9161 : Upper (D 5) (R 5) [6,72,136,288] 13 := by
  apply FastRouting.sound _ _ [6,72,136,288] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9161 c9161
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6643
  · exact m9161_5
  · exact u6644
  · exact u6645
  · exact u6646
  · exact m9161_36

def r9162 : Route 9 := (fun mask => (mask,id))

def c9162 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9162 : Upper (D 5) (R 5) [6,72,144,33] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9162 c9162
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6647
  · exact u6648
  · exact u6649
  · exact u6650
  · exact u6651
  · exact u6652
  · exact u6653
  · exact u6654
  · exact u6655
  · exact u6656
  · exact u6657
  · exact u6658
  · exact u6659
  · exact u6660
  · exact u6661

def r9163 : Route 9 := (fun mask => (mask,id))

def c9163 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9163 : Upper (D 5) (R 5) [6,72,144,34] 13 := by
  apply FastRouting.sound _ _ [6,72,144,34] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9163 c9163
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6662
  · exact u6663
  · exact u6664
  · exact u6665
  · exact u6666
  · exact u6667
  · exact u6668
  · exact u6669
  · exact u6670
  · exact u6671

def r9164 : Route 9 := (fun mask => (mask,id))

def c9164 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9164 : Upper (D 5) (R 5) [6,72,144,36] 13 := by
  apply FastRouting.sound _ _ [6,72,144,36] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9164 c9164
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6672
  · exact u6673
  · exact u6674
  · exact u6675
  · exact u6676
  · exact u6677
  · exact u6678
  · exact u6679
  · exact u6680
  · exact u6681

def r9165 : Route 9 := (fun mask => (mask,id))

def c9165 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9165 : Upper (D 5) (R 5) [6,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,72,144,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9165 c9165
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6682
  · exact u6683
  · exact u6684
  · exact u6685
  · exact u6686
  · exact u6687
  · exact u6688
  · exact u6689
  · exact u6690
  · exact u6691

def r9166 : Route 9 := (fun mask => (mask,id))

def c9166 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9166 : Upper (D 5) (R 5) [6,72,144,258] 13 := by
  apply FastRouting.sound _ _ [6,72,144,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9166 c9166
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6692
  · exact u6693
  · exact u6694
  · exact u6695
  · exact u6696
  · exact u6697

def r9167 : Route 9 := (fun mask => (mask,id))

def c9167 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9167 : Upper (D 5) (R 5) [6,72,144,260] 13 := by
  apply FastRouting.sound _ _ [6,72,144,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9167 c9167
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6698
  · exact u6699
  · exact u6700
  · exact u6701
  · exact u6702
  · exact u6703

def r9168 : Route 9 := (fun mask => (mask,id))

def c9168 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9168 : Upper (D 5) (R 5) [6,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9168 c9168
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6704
  · exact u6705
  · exact u6706
  · exact u6707
  · exact u6708
  · exact u6709
  · exact u6710
  · exact u6711
  · exact u6712
  · exact u6713

def r9169 : Route 9 := (fun mask => (mask,id))

def c9169 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9169 : Upper (D 5) (R 5) [6,72,160,17] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9169 c9169
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6714
  · exact u6715
  · exact u6716
  · exact u6717
  · exact u6718
  · exact u6719
  · exact u6720
  · exact u6721
  · exact u6722
  · exact u6723
  · exact u6724
  · exact u6725
  · exact u6726
  · exact u6727
  · exact u6728

def r9170 : Route 9 := (fun mask => (mask,id))

def c9170 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9170 : Upper (D 5) (R 5) [6,72,160,18] 13 := by
  apply FastRouting.sound _ _ [6,72,160,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9170 c9170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6729
  · exact u6730
  · exact u6731
  · exact u6732
  · exact u6733
  · exact u6734
  · exact u6735
  · exact u6736
  · exact u6737
  · exact u6738

def r9171 : Route 9 := (fun mask => (mask,id))

def c9171 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9171 : Upper (D 5) (R 5) [6,72,160,20] 13 := by
  apply FastRouting.sound _ _ [6,72,160,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9171 c9171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6739
  · exact u6740
  · exact u6741
  · exact u6742
  · exact u6743
  · exact u6744
  · exact u6745
  · exact u6746
  · exact u6747
  · exact u6748

def r9172 : Route 9 := (fun mask => (mask,id))

def c9172 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9172 : Upper (D 5) (R 5) [6,72,160,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9172 c9172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6749
  · exact u6750
  · exact u6751
  · exact u6752
  · exact u6753
  · exact u6754
  · exact u6755
  · exact u6756
  · exact u6757
  · exact u6758

def r9173 : Route 9 := (fun mask => (mask,id))

def c9173 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9173 : Upper (D 5) (R 5) [6,72,160,34] 13 := by
  apply FastRouting.sound _ _ [6,72,160,34] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9173 c9173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6759
  · exact u6760
  · exact u6761
  · exact u6762
  · exact u6763
  · exact u6764

def b9174 : PairBound 9 := { available := 283, camps := [{ cop := 3, region := 339, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 164 44 283 315 347 411 283), lower := (rows 7 74 164 44 16 32 64 128 256), losses := [] }

theorem u9174 : Upper (D 5) (R 5) [6,72,160,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9174
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9175 : Route 9 := (fun mask => (mask,id))

def c9175 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9175 : Upper (D 5) (R 5) [6,72,160,48] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9175 c9175
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6765
  · exact u6766
  · exact u6767
  · exact u6768
  · exact u6769
  · exact u6770
  · exact u6771
  · exact u6772
  · exact u6773
  · exact u6774

def r9176 : Route 9 := (fun mask => (mask,id))

def c9176 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9176 : Upper (D 5) (R 5) [6,72,160,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9176 c9176
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6775
  · exact u6776
  · exact u6777
  · exact u6778
  · exact u6779
  · exact u6780
  · exact u6781
  · exact u6782
  · exact u6783
  · exact u6784

def r9177 : Route 9 := (fun mask => (mask,id))

def c9177 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9177 : Upper (D 5) (R 5) [6,72,160,258] 13 := by
  apply FastRouting.sound _ _ [6,72,160,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9177 c9177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6785
  · exact u6786
  · exact u6787
  · exact u6788
  · exact u6789
  · exact u6790

def r9178 : Route 9 := (fun mask => (mask,id))

def c9178 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9178 : Upper (D 5) (R 5) [6,72,160,260] 13 := by
  apply FastRouting.sound _ _ [6,72,160,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9178 c9178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6791
  · exact u6792
  · exact u6793
  · exact u6794
  · exact u6795
  · exact u6796

def r9179 : Route 9 := (fun mask => (mask,id))

def c9179 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9179 : Upper (D 5) (R 5) [6,72,160,272] 13 := by
  apply FastRouting.sound _ _ [6,72,160,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9179 c9179
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6797
  · exact u6798
  · exact u6799
  · exact u6800
  · exact u6801
  · exact u6802
  · exact u6803
  · exact u6804
  · exact u6805
  · exact u6806

#print axioms u9179
end Delivery.IrregularNine14.P05
