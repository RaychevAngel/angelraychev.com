import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0208
import IrregularNine14P08C0212
import IrregularNine14P08C0216
import IrregularNine14P08C0219
import IrregularNine14P08C0220

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20940 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 26 433 417 481 417 417), lower := (rows 97 7 76 26 16 32 64 128 256), losses := [] }

theorem u20940 : Upper (D 8) (R 8) [96,5,72,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20941 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 76 42 433 433 497 433 433), lower := (rows 97 7 76 42 16 32 64 128 256), losses := [] }

theorem u20941 : Upper (D 8) (R 8) [96,5,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20942 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 137 434 434 498 434 434), lower := (rows 97 7 76 137 16 32 64 128 256), losses := [] }

theorem u20942 : Upper (D 8) (R 8) [96,5,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20943 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 138 433 433 497 433 433), lower := (rows 97 7 76 138 16 32 64 128 256), losses := [] }

theorem u20943 : Upper (D 8) (R 8) [96,5,72,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20944 : PairBound 9 := { available := 435, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 168 435 435 499 435 435), lower := (rows 97 7 76 168 16 32 64 128 256), losses := [] }

theorem u20944 : Upper (D 8) (R 8) [96,5,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20945 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 265 178 178 242 178 434), lower := (rows 97 7 76 265 16 32 64 128 256), losses := [] }

theorem u20945 : Upper (D 8) (R 8) [96,5,72,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20946 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 266 177 177 241 177 433), lower := (rows 97 7 76 266 16 32 64 128 256), losses := [] }

theorem u20946 : Upper (D 8) (R 8) [96,5,72,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20947 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 296 179 179 243 179 435), lower := (rows 97 7 76 296 16 32 64 128 256), losses := [] }

theorem u20947 : Upper (D 8) (R 8) [96,5,72,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20948 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 392 179 179 243 179 435), lower := (rows 97 7 76 392 16 32 64 128 256), losses := [] }

theorem u20948 : Upper (D 8) (R 8) [96,5,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20949 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 84 42 441 425 489 425 425), lower := (rows 97 7 84 42 16 32 64 128 256), losses := [] }

theorem u20949 : Upper (D 8) (R 8) [96,5,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20950 : PairBound 9 := { available := 426, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 84 137 442 426 490 426 426), lower := (rows 97 7 84 137 16 32 64 128 256), losses := [] }

theorem u20950 : Upper (D 8) (R 8) [96,5,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20951 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 84 138 441 425 489 425 425), lower := (rows 97 7 84 138 16 32 64 128 256), losses := [] }

theorem u20951 : Upper (D 8) (R 8) [96,5,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20952 : PairBound 9 := { available := 427, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 84 168 443 427 491 427 427), lower := (rows 97 7 84 168 16 32 64 128 256), losses := [] }

theorem u20952 : Upper (D 8) (R 8) [96,5,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20953 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 84 265 186 170 234 170 426), lower := (rows 97 7 84 265 16 32 64 128 256), losses := [] }

theorem u20953 : Upper (D 8) (R 8) [96,5,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20954 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 84 266 185 169 233 169 425), lower := (rows 97 7 84 266 16 32 64 128 256), losses := [] }

theorem u20954 : Upper (D 8) (R 8) [96,5,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20955 : PairBound 9 := { available := 171, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 84 296 187 171 235 171 427), lower := (rows 97 7 84 296 16 32 64 128 256), losses := [] }

theorem u20955 : Upper (D 8) (R 8) [96,5,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20956 : PairBound 9 := { available := 171, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 84 392 187 171 235 171 427), lower := (rows 97 7 84 392 16 32 64 128 256), losses := [] }

theorem u20956 : Upper (D 8) (R 8) [96,5,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20957 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 441 425 489 425 425), lower := (rows 97 7 100 26 16 32 64 128 256), losses := [] }

theorem u20957 : Upper (D 8) (R 8) [96,5,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20958 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 42 409 441 473 409 409), lower := (rows 97 7 100 42 16 32 64 128 256), losses := [] }

theorem u20958 : Upper (D 8) (R 8) [96,5,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20959 : PairBound 9 := { available := 442, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 442 442 506 442 442), lower := (rows 97 7 100 137 16 32 64 128 256), losses := [] }

theorem u20959 : Upper (D 8) (R 8) [96,5,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20960 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 441 441 505 441 441), lower := (rows 97 7 100 138 16 32 64 128 256), losses := [] }

theorem u20960 : Upper (D 8) (R 8) [96,5,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20961 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 168 411 443 475 411 411), lower := (rows 97 7 100 168 16 32 64 128 256), losses := [] }

theorem u20961 : Upper (D 8) (R 8) [96,5,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20962 : PairBound 9 := { available := 186, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 265 186 186 250 186 442), lower := (rows 97 7 100 265 16 32 64 128 256), losses := [] }

theorem u20962 : Upper (D 8) (R 8) [96,5,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20963 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 266 185 185 249 185 441), lower := (rows 97 7 100 266 16 32 64 128 256), losses := [] }

theorem u20963 : Upper (D 8) (R 8) [96,5,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20964 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 296 155 187 219 155 411), lower := (rows 97 7 100 296 16 32 64 128 256), losses := [] }

theorem u20964 : Upper (D 8) (R 8) [96,5,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20965 : PairBound 9 := { available := 187, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 392 187 187 251 187 443), lower := (rows 97 7 100 392 16 32 64 128 256), losses := [] }

theorem u20965 : Upper (D 8) (R 8) [96,5,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20966 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 504 488 488 488 488), lower := (rows 97 7 133 26 16 32 64 128 256), losses := [] }

theorem u20966 : Upper (D 8) (R 8) [96,5,129,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20967 : PairBound 9 := { available := 504, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 504 504 504 504 504), lower := (rows 97 7 133 42 16 32 64 128 256), losses := [] }

theorem u20967 : Upper (D 8) (R 8) [96,5,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20968 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 74 440 440 504 440 440), lower := (rows 97 7 133 74 16 32 64 128 256), losses := [] }

theorem u20968 : Upper (D 8) (R 8) [96,5,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20969 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 138 376 376 376 504 376), lower := (rows 97 7 133 138 16 32 64 128 256), losses := [] }

theorem u20969 : Upper (D 8) (R 8) [96,5,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20970 : PairBound 9 := { available := 378, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 378 378 378 506 378), lower := (rows 97 7 133 168 16 32 64 128 256), losses := [] }

theorem u20970 : Upper (D 8) (R 8) [96,5,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20971 : PairBound 9 := { available := 314, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 200 314 314 378 442 314), lower := (rows 97 7 133 200 16 32 64 128 256), losses := [] }

theorem u20971 : Upper (D 8) (R 8) [96,5,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20972 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 266 248 248 248 248 504), lower := (rows 97 7 133 266 16 32 64 128 256), losses := [] }

theorem u20972 : Upper (D 8) (R 8) [96,5,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20973 : PairBound 9 := { available := 250, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 296 250 250 250 250 506), lower := (rows 97 7 133 296 16 32 64 128 256), losses := [] }

theorem u20973 : Upper (D 8) (R 8) [96,5,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20974 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 328 186 186 250 186 442), lower := (rows 97 7 133 328 16 32 64 128 256), losses := [] }

theorem u20974 : Upper (D 8) (R 8) [96,5,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20975 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 392 122 122 122 250 378), lower := (rows 97 7 133 392 16 32 64 128 256), losses := [] }

theorem u20975 : Upper (D 8) (R 8) [96,5,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20976 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 134 25 504 488 488 488 488), lower := (rows 97 7 134 25 16 32 64 128 256), losses := [] }

theorem u20976 : Upper (D 8) (R 8) [96,5,130,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20977 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 134 41 504 504 504 504 504), lower := (rows 97 7 134 41 16 32 64 128 256), losses := [] }

theorem u20977 : Upper (D 8) (R 8) [96,5,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20978_9 : Upper (D 8) (R 8) [96,5,130,48,9] 13 :=
  permutation_upper _ _ _ [96,5,34,17,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12764

theorem m20978_33 : Upper (D 8) (R 8) [96,5,130,48,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13148

def r20978 : Route 9 := (fun mask => (mask,id))

def c20978 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u20978 : Upper (D 8) (R 8) [96,5,130,48] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r20978 c20978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20978_9
  · exact m20978_33
  · exact u13153
  · exact u13154
  · exact u13155
  · exact u13156
  · exact u13157
  · exact u13158
  · exact u13159
  · exact u13160
  · exact u13161
  · exact u13162
  · exact u13163
  · exact u13164
  · exact u13165

def b20979 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 73 440 440 504 440 440), lower := (rows 97 7 134 73 16 32 64 128 256), losses := [] }

theorem u20979 : Upper (D 8) (R 8) [96,5,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20980_9 : Upper (D 8) (R 8) [96,5,130,80,9] 13 :=
  permutation_upper _ _ _ [96,5,66,17,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12975

theorem m20980_33 : Upper (D 8) (R 8) [96,5,130,80,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13149

theorem m20980_40 : Upper (D 8) (R 8) [96,5,130,80,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13155

def r20980 : Route 9 := (fun mask => (mask,id))

def c20980 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20980 : Upper (D 8) (R 8) [96,5,130,80] 13 := by
  apply FastRouting.sound _ _ [96,5,130,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r20980 c20980
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20980_9
  · exact m20980_33
  · exact m20980_40
  · exact u13168
  · exact u13169
  · exact u13170
  · exact u13171
  · exact u13172
  · exact u13173
  · exact u13174

def b20981 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 104 441 441 505 441 441), lower := (rows 97 7 134 104 16 32 64 128 256), losses := [] }

theorem u20981 : Upper (D 8) (R 8) [96,5,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20982 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 137 376 376 376 504 376), lower := (rows 97 7 134 137 16 32 64 128 256), losses := [] }

theorem u20982 : Upper (D 8) (R 8) [96,5,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20983 : PairBound 9 := { available := 361, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 152 377 361 361 489 361), lower := (rows 97 7 134 152 16 32 64 128 256), losses := [] }

theorem u20983 : Upper (D 8) (R 8) [96,5,130,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20984 : PairBound 9 := { available := 377, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 168 377 377 377 505 377), lower := (rows 97 7 134 168 16 32 64 128 256), losses := [] }

theorem u20984 : Upper (D 8) (R 8) [96,5,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20985 : PairBound 9 := { available := 313, camps := [{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 200 313 313 377 441 313), lower := (rows 97 7 134 200 16 32 64 128 256), losses := [] }

theorem u20985 : Upper (D 8) (R 8) [96,5,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20986 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 134 265 248 248 248 248 504), lower := (rows 97 7 134 265 16 32 64 128 256), losses := [] }

theorem u20986 : Upper (D 8) (R 8) [96,5,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20987_9 : Upper (D 8) (R 8) [96,5,130,272,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13144

theorem m20987_33 : Upper (D 8) (R 8) [96,5,130,272,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13150

theorem m20987_40 : Upper (D 8) (R 8) [96,5,130,272,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13162

theorem m20987_65 : Upper (D 8) (R 8) [96,5,130,272,65] 13 :=
  permutation_upper _ _ _ [96,5,130,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13166

theorem m20987_72 : Upper (D 8) (R 8) [96,5,130,272,72] 13 :=
  permutation_upper _ _ _ [96,5,130,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13172

theorem m20987_96 : Upper (D 8) (R 8) [96,5,130,272,96] 13 :=
  permutation_upper _ _ _ [96,5,130,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13175

theorem m20987_129 : Upper (D 8) (R 8) [96,5,130,272,129] 13 :=
  permutation_upper _ _ _ [96,5,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13177

theorem m20987_136 : Upper (D 8) (R 8) [96,5,130,272,136] 13 :=
  permutation_upper _ _ _ [96,5,130,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13181

theorem m20987_160 : Upper (D 8) (R 8) [96,5,130,272,160] 13 :=
  permutation_upper _ _ _ [96,5,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13185

theorem m20987_192 : Upper (D 8) (R 8) [96,5,130,272,192] 13 :=
  permutation_upper _ _ _ [96,5,130,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13189

def r20987 : Route 9 := (fun mask => (mask,id))

def c20987 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20987 : Upper (D 8) (R 8) [96,5,130,272] 13 := by
  apply FastRouting.sound _ _ [96,5,130,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20987 c20987
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20987_9
  · exact m20987_33
  · exact m20987_40
  · exact m20987_65
  · exact m20987_72
  · exact m20987_96
  · exact m20987_129
  · exact m20987_136
  · exact m20987_160
  · exact m20987_192

theorem m20988_9 : Upper (D 8) (R 8) [96,5,130,288,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13145

theorem m20988_33 : Upper (D 8) (R 8) [96,5,130,288,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13151

theorem m20988_40 : Upper (D 8) (R 8) [96,5,130,288,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13163

theorem m20988_65 : Upper (D 8) (R 8) [96,5,130,288,65] 13 :=
  permutation_upper _ _ _ [96,5,130,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13167

theorem m20988_72 : Upper (D 8) (R 8) [96,5,130,288,72] 13 :=
  permutation_upper _ _ _ [96,5,130,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13173

theorem m20988_96 : Upper (D 8) (R 8) [96,5,130,288,96] 13 :=
  permutation_upper _ _ _ [96,5,130,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13176

theorem m20988_129 : Upper (D 8) (R 8) [96,5,130,288,129] 13 :=
  permutation_upper _ _ _ [96,5,130,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13178

theorem m20988_136 : Upper (D 8) (R 8) [96,5,130,288,136] 13 :=
  permutation_upper _ _ _ [96,5,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13182

theorem m20988_160 : Upper (D 8) (R 8) [96,5,130,288,160] 13 :=
  permutation_upper _ _ _ [96,5,130,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13186

theorem m20988_192 : Upper (D 8) (R 8) [96,5,130,288,192] 13 :=
  permutation_upper _ _ _ [96,5,130,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13190

def r20988 : Route 9 := (fun mask => (mask,id))

def c20988 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20988 : Upper (D 8) (R 8) [96,5,130,288] 13 := by
  apply FastRouting.sound _ _ [96,5,130,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20988 c20988
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20988_9
  · exact m20988_33
  · exact m20988_40
  · exact m20988_65
  · exact m20988_72
  · exact m20988_96
  · exact m20988_129
  · exact m20988_136
  · exact m20988_160
  · exact m20988_192

theorem m20989_9 : Upper (D 8) (R 8) [96,5,130,320,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13146

theorem m20989_33 : Upper (D 8) (R 8) [96,5,130,320,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13152

theorem m20989_40 : Upper (D 8) (R 8) [96,5,130,320,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13164

theorem m20989_129 : Upper (D 8) (R 8) [96,5,130,320,129] 13 :=
  permutation_upper _ _ _ [96,5,130,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13179

theorem m20989_136 : Upper (D 8) (R 8) [96,5,130,320,136] 13 :=
  permutation_upper _ _ _ [96,5,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13183

theorem m20989_160 : Upper (D 8) (R 8) [96,5,130,320,160] 13 :=
  permutation_upper _ _ _ [96,5,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13187

def r20989 : Route 9 := (fun mask => (mask,id))

def c20989 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20989 : Upper (D 8) (R 8) [96,5,130,320] 13 := by
  apply FastRouting.sound _ _ [96,5,130,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20989 c20989
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20989_9
  · exact m20989_33
  · exact m20989_40
  · exact m20989_129
  · exact m20989_136
  · exact m20989_160

def b20990 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 392 121 121 121 249 377), lower := (rows 97 7 134 392 16 32 64 128 256), losses := [] }

theorem u20990 : Upper (D 8) (R 8) [96,5,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20991 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 25 498 482 482 482 482), lower := (rows 97 7 140 25 16 32 64 128 256), losses := [] }

theorem u20991 : Upper (D 8) (R 8) [96,5,136,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20992 : Route 9 := (fun mask => (mask,id))

def c20992 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20992 : Upper (D 8) (R 8) [96,5,136,18] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20992 c20992
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13197
  · exact u13198
  · exact u13199
  · exact u13200
  · exact u13201
  · exact u13202
  · exact u13203
  · exact u13204
  · exact u13205
  · exact u13206

def b20993 : PairBound 9 := { available := 498, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 41 498 498 498 498 498), lower := (rows 97 7 140 41 16 32 64 128 256), losses := [] }

theorem u20993 : Upper (D 8) (R 8) [96,5,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20994 : Route 9 := (fun mask => (mask,id))

def c20994 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20994 : Upper (D 8) (R 8) [96,5,136,34] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20994 c20994
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13215
  · exact u13216
  · exact u13217
  · exact u13218
  · exact u13219
  · exact u13220
  · exact u13221
  · exact u13222
  · exact u13223
  · exact u13224

theorem m20995_3 : Upper (D 8) (R 8) [96,5,136,48,3] 13 :=
  permutation_upper _ _ _ [96,5,9,144,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12537

def r20995 : Route 9 := (fun mask => (mask,id))

def c20995 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20995 : Upper (D 8) (R 8) [96,5,136,48] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r20995 c20995
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20995_3
  · exact u13225
  · exact u13226
  · exact u13227
  · exact u13228
  · exact u13229
  · exact u13230
  · exact u13231
  · exact u13232
  · exact u13233
  · exact u13234
  · exact u13235
  · exact u13236
  · exact u13237
  · exact u13238

def b20996 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 73 434 434 498 434 434), lower := (rows 97 7 140 73 16 32 64 128 256), losses := [] }

theorem u20996 : Upper (D 8) (R 8) [96,5,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20997 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 74 433 433 497 433 433), lower := (rows 97 7 140 74 16 32 64 128 256), losses := [] }

theorem u20997 : Upper (D 8) (R 8) [96,5,136,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20998 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 88 435 419 483 419 419), lower := (rows 97 7 140 88 16 32 64 128 256), losses := [] }

theorem u20998 : Upper (D 8) (R 8) [96,5,136,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20999 : PairBound 9 := { available := 435, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 435 435 499 435 435), lower := (rows 97 7 140 104 16 32 64 128 256), losses := [] }

theorem u20999 : Upper (D 8) (R 8) [96,5,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u20999
end Delivery.IrregularNine14.P08
