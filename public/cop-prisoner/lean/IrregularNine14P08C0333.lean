import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0171
import IrregularNine14P08C0172
import IrregularNine14P08C0173
import IrregularNine14P08C0174
import IrregularNine14P08C0175

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19980 : PairBound 9 := { available := 496, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 13 44 496 496 496 496 496), lower := (rows 67 35 13 44 16 32 64 128 256), losses := [] }

theorem u19980 : Upper (D 8) (R 8) [66,33,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19981 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 35 13 76 432 432 496 432 432), lower := (rows 67 35 13 76 16 32 64 128 256), losses := [] }

theorem u19981 : Upper (D 8) (R 8) [66,33,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19982 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 140 496 496 496 496 496), lower := (rows 67 35 13 140 16 32 64 128 256), losses := [] }

theorem u19982 : Upper (D 8) (R 8) [66,33,9,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19983 : PairBound 9 := { available := 500, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 168 500 500 500 500 500), lower := (rows 67 35 13 168 16 32 64 128 256), losses := [] }

theorem u19983 : Upper (D 8) (R 8) [66,33,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19984 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 200 436 436 500 436 436), lower := (rows 67 35 13 200 16 32 64 128 256), losses := [] }

theorem u19984 : Upper (D 8) (R 8) [66,33,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19985 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 268 240 240 240 240 496), lower := (rows 67 35 13 268 16 32 64 128 256), losses := [] }

theorem u19985 : Upper (D 8) (R 8) [66,33,9,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19986 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 296 244 244 244 244 500), lower := (rows 67 35 13 296 16 32 64 128 256), losses := [] }

theorem u19986 : Upper (D 8) (R 8) [66,33,9,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19987 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 328 180 180 244 180 436), lower := (rows 67 35 13 328 16 32 64 128 256), losses := [] }

theorem u19987 : Upper (D 8) (R 8) [66,33,9,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19988 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 392 244 244 244 244 500), lower := (rows 67 35 13 392 16 32 64 128 256), losses := [] }

theorem u19988 : Upper (D 8) (R 8) [66,33,9,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19989 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 21 44 504 488 488 488 488), lower := (rows 67 35 21 44 16 32 64 128 256), losses := [] }

theorem u19989 : Upper (D 8) (R 8) [66,33,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19990 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 21 76 440 424 488 424 424), lower := (rows 67 35 21 76 16 32 64 128 256), losses := [] }

theorem u19990 : Upper (D 8) (R 8) [66,33,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19991 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 21 140 504 488 488 488 488), lower := (rows 67 35 21 140 16 32 64 128 256), losses := [] }

theorem u19991 : Upper (D 8) (R 8) [66,33,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19992 : PairBound 9 := { available := 492, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 21 168 508 492 492 492 492), lower := (rows 67 35 21 168 16 32 64 128 256), losses := [] }

theorem u19992 : Upper (D 8) (R 8) [66,33,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19993 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 21 200 444 428 492 428 428), lower := (rows 67 35 21 200 16 32 64 128 256), losses := [] }

theorem u19993 : Upper (D 8) (R 8) [66,33,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19994 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 21 268 248 232 232 232 488), lower := (rows 67 35 21 268 16 32 64 128 256), losses := [] }

theorem u19994 : Upper (D 8) (R 8) [66,33,17,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19995 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 21 296 252 236 236 236 492), lower := (rows 67 35 21 296 16 32 64 128 256), losses := [] }

theorem u19995 : Upper (D 8) (R 8) [66,33,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19996 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 21 328 188 172 236 172 428), lower := (rows 67 35 21 328 16 32 64 128 256), losses := [] }

theorem u19996 : Upper (D 8) (R 8) [66,33,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19997 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 21 392 252 236 236 236 492), lower := (rows 67 35 21 392 16 32 64 128 256), losses := [] }

theorem u19997 : Upper (D 8) (R 8) [66,33,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19998 : PairBound 9 := { available := 484, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 35 28 41 500 484 484 484 484), lower := (rows 67 35 28 41 16 32 64 128 256), losses := [] }

theorem u19998 : Upper (D 8) (R 8) [66,33,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19999_33 : Upper (D 8) (R 8) [66,33,24,36,33] 13 :=
  permutation_upper _ _ _ [66,33,24,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10362

def r19999 : Route 9 := (fun mask => (mask,id))

def c19999 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19999 : Upper (D 8) (R 8) [66,33,24,36] 13 := by
  apply FastRouting.sound _ _ [66,33,24,36] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19999 c19999
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19999_33
  · exact u10370
  · exact u10371
  · exact u10372
  · exact u10373
  · exact u10374
  · exact u10375
  · exact u10376
  · exact u10377
  · exact u10378

def b20000 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 73 436 420 484 420 420), lower := (rows 67 35 28 73 16 32 64 128 256), losses := [] }

theorem u20000 : Upper (D 8) (R 8) [66,33,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20001 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 76 433 417 481 417 417), lower := (rows 67 35 28 76 16 32 64 128 256), losses := [] }

theorem u20001 : Upper (D 8) (R 8) [66,33,24,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20002 : PairBound 9 := { available := 421, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 104 437 421 485 421 421), lower := (rows 67 35 28 104 16 32 64 128 256), losses := [] }

theorem u20002 : Upper (D 8) (R 8) [66,33,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20003 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 137 500 484 484 484 484), lower := (rows 67 35 28 137 16 32 64 128 256), losses := [] }

theorem u20003 : Upper (D 8) (R 8) [66,33,24,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20004_33 : Upper (D 8) (R 8) [66,33,24,132,33] 13 :=
  permutation_upper _ _ _ [66,33,24,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10363

theorem m20004_65 : Upper (D 8) (R 8) [66,33,24,132,65] 13 :=
  permutation_upper _ _ _ [66,33,24,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10379

theorem m20004_96 : Upper (D 8) (R 8) [66,33,24,132,96] 13 :=
  permutation_upper _ _ _ [66,33,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10387

theorem m20004_129 : Upper (D 8) (R 8) [66,33,24,132,129] 13 :=
  permutation_upper _ _ _ [66,33,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10392

def r20004 : Route 9 := (fun mask => (mask,id))

def c20004 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20004 : Upper (D 8) (R 8) [66,33,24,132] 13 := by
  apply FastRouting.sound _ _ [66,33,24,132] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20004 c20004
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20004_33
  · exact m20004_65
  · exact m20004_96
  · exact m20004_129
  · exact u10399
  · exact u10400
  · exact u10401
  · exact u10402
  · exact u10403
  · exact u10404

theorem m20005_5 : Upper (D 8) (R 8) [66,33,24,160,5] 13 :=
  permutation_upper _ _ _ [66,33,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10293

theorem m20005_33 : Upper (D 8) (R 8) [66,33,24,160,33] 13 :=
  permutation_upper _ _ _ [66,33,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10364

theorem m20005_36 : Upper (D 8) (R 8) [66,33,24,160,36] 13 :=
  permutation_upper _ _ _ [66,33,24,36,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10373

theorem m20005_65 : Upper (D 8) (R 8) [66,33,24,160,65] 13 :=
  permutation_upper _ _ _ [66,33,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10380

theorem m20005_68 : Upper (D 8) (R 8) [66,33,24,160,68] 13 :=
  permutation_upper _ _ _ [66,33,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10384

theorem m20005_96 : Upper (D 8) (R 8) [66,33,24,160,96] 13 :=
  permutation_upper _ _ _ [66,33,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10388

theorem m20005_129 : Upper (D 8) (R 8) [66,33,24,160,129] 13 :=
  permutation_upper _ _ _ [66,33,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10393

theorem m20005_132 : Upper (D 8) (R 8) [66,33,24,160,132] 13 :=
  permutation_upper _ _ _ [66,33,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10399

def r20005 : Route 9 := (fun mask => (mask,id))

def c20005 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20005 : Upper (D 8) (R 8) [66,33,24,160] 13 := by
  apply FastRouting.sound _ _ [66,33,24,160] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r20005 c20005
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20005_5
  · exact m20005_33
  · exact m20005_36
  · exact m20005_65
  · exact m20005_68
  · exact m20005_96
  · exact m20005_129
  · exact m20005_132
  · exact u10405
  · exact u10406
  · exact u10407
  · exact u10408
  · exact u10409
  · exact u10410
  · exact u10411

theorem m20006_5 : Upper (D 8) (R 8) [66,33,24,192,5] 13 :=
  permutation_upper _ _ _ [66,33,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10294

theorem m20006_33 : Upper (D 8) (R 8) [66,33,24,192,33] 13 :=
  permutation_upper _ _ _ [66,33,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10365

theorem m20006_36 : Upper (D 8) (R 8) [66,33,24,192,36] 13 :=
  permutation_upper _ _ _ [66,33,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10374

theorem m20006_129 : Upper (D 8) (R 8) [66,33,24,192,129] 13 :=
  permutation_upper _ _ _ [66,33,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10394

theorem m20006_132 : Upper (D 8) (R 8) [66,33,24,192,132] 13 :=
  permutation_upper _ _ _ [66,33,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10400

theorem m20006_160 : Upper (D 8) (R 8) [66,33,24,192,160] 13 :=
  permutation_upper _ _ _ [66,33,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10406

def r20006 : Route 9 := (fun mask => (mask,id))

def c20006 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20006 : Upper (D 8) (R 8) [66,33,24,192] 13 := by
  apply FastRouting.sound _ _ [66,33,24,192] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r20006 c20006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20006_5
  · exact m20006_33
  · exact m20006_36
  · exact m20006_129
  · exact m20006_132
  · exact m20006_160
  · exact u10412
  · exact u10413
  · exact u10414
  · exact u10415

def b20007 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 265 244 228 228 228 484), lower := (rows 67 35 28 265 16 32 64 128 256), losses := [] }

theorem u20007 : Upper (D 8) (R 8) [66,33,24,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20008_33 : Upper (D 8) (R 8) [66,33,24,260,33] 13 :=
  permutation_upper _ _ _ [66,33,24,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10366

theorem m20008_65 : Upper (D 8) (R 8) [66,33,24,260,65] 13 :=
  permutation_upper _ _ _ [66,33,24,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10381

theorem m20008_96 : Upper (D 8) (R 8) [66,33,24,260,96] 13 :=
  permutation_upper _ _ _ [66,33,24,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10389

theorem m20008_129 : Upper (D 8) (R 8) [66,33,24,260,129] 13 :=
  permutation_upper _ _ _ [66,33,24,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10395

theorem m20008_160 : Upper (D 8) (R 8) [66,33,24,260,160] 13 :=
  permutation_upper _ _ _ [66,33,24,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10408

theorem m20008_192 : Upper (D 8) (R 8) [66,33,24,260,192] 13 :=
  permutation_upper _ _ _ [66,33,24,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10413

def r20008 : Route 9 := (fun mask => (mask,id))

def c20008 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20008 : Upper (D 8) (R 8) [66,33,24,260] 13 := by
  apply FastRouting.sound _ _ [66,33,24,260] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20008 c20008
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20008_33
  · exact m20008_65
  · exact m20008_96
  · exact m20008_129
  · exact m20008_160
  · exact m20008_192

theorem m20009_5 : Upper (D 8) (R 8) [66,33,24,288,5] 13 :=
  permutation_upper _ _ _ [66,33,9,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10295

theorem m20009_33 : Upper (D 8) (R 8) [66,33,24,288,33] 13 :=
  permutation_upper _ _ _ [66,33,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10367

theorem m20009_36 : Upper (D 8) (R 8) [66,33,24,288,36] 13 :=
  permutation_upper _ _ _ [66,33,24,36,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10376

theorem m20009_65 : Upper (D 8) (R 8) [66,33,24,288,65] 13 :=
  permutation_upper _ _ _ [66,33,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10382

theorem m20009_68 : Upper (D 8) (R 8) [66,33,24,288,68] 13 :=
  permutation_upper _ _ _ [66,33,24,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10385

theorem m20009_96 : Upper (D 8) (R 8) [66,33,24,288,96] 13 :=
  permutation_upper _ _ _ [66,33,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10390

theorem m20009_129 : Upper (D 8) (R 8) [66,33,24,288,129] 13 :=
  permutation_upper _ _ _ [66,33,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10396

theorem m20009_132 : Upper (D 8) (R 8) [66,33,24,288,132] 13 :=
  permutation_upper _ _ _ [66,33,24,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10402

theorem m20009_160 : Upper (D 8) (R 8) [66,33,24,288,160] 13 :=
  permutation_upper _ _ _ [66,33,24,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10409

theorem m20009_192 : Upper (D 8) (R 8) [66,33,24,288,192] 13 :=
  permutation_upper _ _ _ [66,33,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10414

def r20009 : Route 9 := (fun mask => (mask,id))

def c20009 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20009 : Upper (D 8) (R 8) [66,33,24,288] 13 := by
  apply FastRouting.sound _ _ [66,33,24,288] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r20009 c20009
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20009_5
  · exact m20009_33
  · exact m20009_36
  · exact m20009_65
  · exact m20009_68
  · exact m20009_96
  · exact m20009_129
  · exact m20009_132
  · exact m20009_160
  · exact m20009_192

theorem m20010_5 : Upper (D 8) (R 8) [66,33,24,320,5] 13 :=
  permutation_upper _ _ _ [66,33,9,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10296

theorem m20010_33 : Upper (D 8) (R 8) [66,33,24,320,33] 13 :=
  permutation_upper _ _ _ [66,33,24,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10368

theorem m20010_36 : Upper (D 8) (R 8) [66,33,24,320,36] 13 :=
  permutation_upper _ _ _ [66,33,24,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10377

theorem m20010_129 : Upper (D 8) (R 8) [66,33,24,320,129] 13 :=
  permutation_upper _ _ _ [66,33,24,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10397

theorem m20010_132 : Upper (D 8) (R 8) [66,33,24,320,132] 13 :=
  permutation_upper _ _ _ [66,33,24,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10403

theorem m20010_160 : Upper (D 8) (R 8) [66,33,24,320,160] 13 :=
  permutation_upper _ _ _ [66,33,24,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10410

def r20010 : Route 9 := (fun mask => (mask,id))

def c20010 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20010 : Upper (D 8) (R 8) [66,33,24,320] 13 := by
  apply FastRouting.sound _ _ [66,33,24,320] 13 (by decide) (choices 2) [5,33,36,129,132,160] r20010 c20010
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20010_5
  · exact m20010_33
  · exact m20010_36
  · exact m20010_129
  · exact m20010_132
  · exact m20010_160

theorem m20011_5 : Upper (D 8) (R 8) [66,33,24,384,5] 13 :=
  permutation_upper _ _ _ [66,33,9,20,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10297

theorem m20011_33 : Upper (D 8) (R 8) [66,33,24,384,33] 13 :=
  permutation_upper _ _ _ [66,33,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10369

theorem m20011_36 : Upper (D 8) (R 8) [66,33,24,384,36] 13 :=
  permutation_upper _ _ _ [66,33,24,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10378

theorem m20011_65 : Upper (D 8) (R 8) [66,33,24,384,65] 13 :=
  permutation_upper _ _ _ [66,33,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10383

theorem m20011_68 : Upper (D 8) (R 8) [66,33,24,384,68] 13 :=
  permutation_upper _ _ _ [66,33,24,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10386

theorem m20011_96 : Upper (D 8) (R 8) [66,33,24,384,96] 13 :=
  permutation_upper _ _ _ [66,33,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10391

theorem m20011_129 : Upper (D 8) (R 8) [66,33,24,384,129] 13 :=
  permutation_upper _ _ _ [66,33,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10398

theorem m20011_132 : Upper (D 8) (R 8) [66,33,24,384,132] 13 :=
  permutation_upper _ _ _ [66,33,24,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10404

theorem m20011_160 : Upper (D 8) (R 8) [66,33,24,384,160] 13 :=
  permutation_upper _ _ _ [66,33,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10411

theorem m20011_192 : Upper (D 8) (R 8) [66,33,24,384,192] 13 :=
  permutation_upper _ _ _ [66,33,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10415

def r20011 : Route 9 := (fun mask => (mask,id))

def c20011 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20011 : Upper (D 8) (R 8) [66,33,24,384] 13 := by
  apply FastRouting.sound _ _ [66,33,24,384] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r20011 c20011
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20011_5
  · exact m20011_33
  · exact m20011_36
  · exact m20011_65
  · exact m20011_68
  · exact m20011_96
  · exact m20011_129
  · exact m20011_132
  · exact m20011_160
  · exact m20011_192

def b20012 : PairBound 9 := { available := 472, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 44 472 504 472 472 472), lower := (rows 67 35 37 44 16 32 64 128 256), losses := [] }

theorem u20012 : Upper (D 8) (R 8) [66,33,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20013 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 76 440 440 504 440 440), lower := (rows 67 35 37 76 16 32 64 128 256), losses := [] }

theorem u20013 : Upper (D 8) (R 8) [66,33,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20014 : PairBound 9 := { available := 504, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 140 504 504 504 504 504), lower := (rows 67 35 37 140 16 32 64 128 256), losses := [] }

theorem u20014 : Upper (D 8) (R 8) [66,33,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20015 : PairBound 9 := { available := 476, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 168 476 508 476 476 476), lower := (rows 67 35 37 168 16 32 64 128 256), losses := [] }

theorem u20015 : Upper (D 8) (R 8) [66,33,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20016 : PairBound 9 := { available := 444, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 200 444 444 508 444 444), lower := (rows 67 35 37 200 16 32 64 128 256), losses := [] }

theorem u20016 : Upper (D 8) (R 8) [66,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20017 : PairBound 9 := { available := 248, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 268 248 248 248 248 504), lower := (rows 67 35 37 268 16 32 64 128 256), losses := [] }

theorem u20017 : Upper (D 8) (R 8) [66,33,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20018 : PairBound 9 := { available := 220, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 296 220 252 220 220 476), lower := (rows 67 35 37 296 16 32 64 128 256), losses := [] }

theorem u20018 : Upper (D 8) (R 8) [66,33,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20019 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 328 188 188 252 188 444), lower := (rows 67 35 37 328 16 32 64 128 256), losses := [] }

theorem u20019 : Upper (D 8) (R 8) [66,33,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20020 : PairBound 9 := { available := 252, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 37 392 252 252 252 252 508), lower := (rows 67 35 37 392 16 32 64 128 256), losses := [] }

theorem u20020 : Upper (D 8) (R 8) [66,33,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20021 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 44 465 497 465 465 465), lower := (rows 67 35 44 44 16 32 64 128 256), losses := [] }

theorem u20021 : Upper (D 8) (R 8) [66,33,40,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20022 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 56 469 485 453 453 453), lower := (rows 67 35 44 56 16 32 64 128 256), losses := [] }

theorem u20022 : Upper (D 8) (R 8) [66,33,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20023 : PairBound 9 := { available := 436, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 73 436 436 500 436 436), lower := (rows 67 35 44 73 16 32 64 128 256), losses := [] }

theorem u20023 : Upper (D 8) (R 8) [66,33,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20024 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 44 76 433 433 497 433 433), lower := (rows 67 35 44 76 16 32 64 128 256), losses := [] }

theorem u20024 : Upper (D 8) (R 8) [66,33,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20025_5 : Upper (D 8) (R 8) [66,33,40,80,5] 13 :=
  permutation_upper _ _ _ [66,33,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10303

theorem m20025_33 : Upper (D 8) (R 8) [66,33,40,80,33] 13 :=
  permutation_upper _ _ _ [66,33,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10422

theorem m20025_36 : Upper (D 8) (R 8) [66,33,40,80,36] 13 :=
  permutation_upper _ _ _ [66,33,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10462

def r20025 : Route 9 := (fun mask => (mask,id))

def c20025 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20025 : Upper (D 8) (R 8) [66,33,40,80] 13 := by
  apply FastRouting.sound _ _ [66,33,40,80] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r20025 c20025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20025_5
  · exact m20025_33
  · exact m20025_36
  · exact u10476
  · exact u10477
  · exact u10478
  · exact u10479
  · exact u10480
  · exact u10481
  · exact u10482

def b20026 : PairBound 9 := { available := 405, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 104 405 437 469 405 405), lower := (rows 67 35 44 104 16 32 64 128 256), losses := [] }

theorem u20026 : Upper (D 8) (R 8) [66,33,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20027 : PairBound 9 := { available := 500, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 137 500 500 500 500 500), lower := (rows 67 35 44 137 16 32 64 128 256), losses := [] }

theorem u20027 : Upper (D 8) (R 8) [66,33,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20028_33 : Upper (D 8) (R 8) [66,33,40,132,33] 13 :=
  permutation_upper _ _ _ [66,33,33,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10424

def r20028 : Route 9 := (fun mask => (mask,id))

def c20028 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20028 : Upper (D 8) (R 8) [66,33,40,132] 13 := by
  apply FastRouting.sound _ _ [66,33,40,132] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20028 c20028
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20028_33
  · exact u10494
  · exact u10495
  · exact u10496
  · exact u10497
  · exact u10498
  · exact u10499
  · exact u10500
  · exact u10501
  · exact u10502

theorem m20029_5 : Upper (D 8) (R 8) [66,33,40,144,5] 13 :=
  permutation_upper _ _ _ [66,33,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10304

theorem m20029_33 : Upper (D 8) (R 8) [66,33,40,144,33] 13 :=
  permutation_upper _ _ _ [66,33,33,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10423

theorem m20029_36 : Upper (D 8) (R 8) [66,33,40,144,36] 13 :=
  permutation_upper _ _ _ [66,33,40,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10463

def r20029 : Route 9 := (fun mask => (mask,id))

def c20029 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20029 : Upper (D 8) (R 8) [66,33,40,144] 13 := by
  apply FastRouting.sound _ _ [66,33,40,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r20029 c20029
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20029_5
  · exact m20029_33
  · exact m20029_36
  · exact u10503
  · exact u10504
  · exact u10505
  · exact u10506
  · exact u10507
  · exact u10508
  · exact u10509
  · exact u10510
  · exact u10511
  · exact u10512
  · exact u10513
  · exact u10514

def b20030 : PairBound 9 := { available := 469, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 168 469 501 469 469 469), lower := (rows 67 35 44 168 16 32 64 128 256), losses := [] }

theorem u20030 : Upper (D 8) (R 8) [66,33,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20031_5 : Upper (D 8) (R 8) [66,33,40,192,5] 13 :=
  permutation_upper _ _ _ [66,33,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10305

theorem m20031_33 : Upper (D 8) (R 8) [66,33,40,192,33] 13 :=
  permutation_upper _ _ _ [66,33,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10425

theorem m20031_36 : Upper (D 8) (R 8) [66,33,40,192,36] 13 :=
  permutation_upper _ _ _ [66,33,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10464

def r20031 : Route 9 := (fun mask => (mask,id))

def c20031 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20031 : Upper (D 8) (R 8) [66,33,40,192] 13 := by
  apply FastRouting.sound _ _ [66,33,40,192] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r20031 c20031
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20031_5
  · exact m20031_33
  · exact m20031_36
  · exact u10521
  · exact u10522
  · exact u10523
  · exact u10524
  · exact u10525
  · exact u10526
  · exact u10527

def b20032 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 265 244 244 244 244 500), lower := (rows 67 35 44 265 16 32 64 128 256), losses := [] }

theorem u20032 : Upper (D 8) (R 8) [66,33,40,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20033_33 : Upper (D 8) (R 8) [66,33,40,260,33] 13 :=
  permutation_upper _ _ _ [66,33,33,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10427

def r20033 : Route 9 := (fun mask => (mask,id))

def c20033 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20033 : Upper (D 8) (R 8) [66,33,40,260] 13 := by
  apply FastRouting.sound _ _ [66,33,40,260] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20033 c20033
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20033_33
  · exact u10532
  · exact u10533
  · exact u10534
  · exact u10535
  · exact u10536

theorem m20034_5 : Upper (D 8) (R 8) [66,33,40,272,5] 13 :=
  permutation_upper _ _ _ [66,33,9,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10306

theorem m20034_33 : Upper (D 8) (R 8) [66,33,40,272,33] 13 :=
  permutation_upper _ _ _ [66,33,33,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10426

theorem m20034_36 : Upper (D 8) (R 8) [66,33,40,272,36] 13 :=
  permutation_upper _ _ _ [66,33,40,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10465

def r20034 : Route 9 := (fun mask => (mask,id))

def c20034 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20034 : Upper (D 8) (R 8) [66,33,40,272] 13 := by
  apply FastRouting.sound _ _ [66,33,40,272] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r20034 c20034
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20034_5
  · exact m20034_33
  · exact m20034_36
  · exact u10537
  · exact u10538
  · exact u10539
  · exact u10540
  · exact u10541
  · exact u10542
  · exact u10543

def b20035 : PairBound 9 := { available := 213, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 296 213 245 213 213 469), lower := (rows 67 35 44 296 16 32 64 128 256), losses := [] }

theorem u20035 : Upper (D 8) (R 8) [66,33,40,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20036_5 : Upper (D 8) (R 8) [66,33,40,320,5] 13 :=
  permutation_upper _ _ _ [66,33,9,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10307

theorem m20036_33 : Upper (D 8) (R 8) [66,33,40,320,33] 13 :=
  permutation_upper _ _ _ [66,33,33,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10428

theorem m20036_36 : Upper (D 8) (R 8) [66,33,40,320,36] 13 :=
  permutation_upper _ _ _ [66,33,40,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10466

def r20036 : Route 9 := (fun mask => (mask,id))

def c20036 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20036 : Upper (D 8) (R 8) [66,33,40,320] 13 := by
  apply FastRouting.sound _ _ [66,33,40,320] 13 (by decide) (choices 2) [5,33,36,129,132,160] r20036 c20036
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20036_5
  · exact m20036_33
  · exact m20036_36
  · exact u10547
  · exact u10548
  · exact u10549

theorem m20037_5 : Upper (D 8) (R 8) [66,33,40,384,5] 13 :=
  permutation_upper _ _ _ [66,33,9,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10308

theorem m20037_33 : Upper (D 8) (R 8) [66,33,40,384,33] 13 :=
  permutation_upper _ _ _ [66,33,33,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10429

theorem m20037_36 : Upper (D 8) (R 8) [66,33,40,384,36] 13 :=
  permutation_upper _ _ _ [66,33,40,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10467

def r20037 : Route 9 := (fun mask => (mask,id))

def c20037 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20037 : Upper (D 8) (R 8) [66,33,40,384] 13 := by
  apply FastRouting.sound _ _ [66,33,40,384] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r20037 c20037
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20037_5
  · exact m20037_33
  · exact m20037_36
  · exact u10550
  · exact u10551
  · exact u10552
  · exact u10553
  · exact u10554
  · exact u10555
  · exact u10556

theorem m20038_9 : Upper (D 8) (R 8) [66,33,48,68,9] 13 :=
  permutation_upper _ _ _ [66,33,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10312

theorem m20038_33 : Upper (D 8) (R 8) [66,33,48,68,33] 13 :=
  permutation_upper _ _ _ [66,33,33,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10416

theorem m20038_40 : Upper (D 8) (R 8) [66,33,48,68,40] 13 :=
  permutation_upper _ _ _ [66,33,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10462

theorem m20038_129 : Upper (D 8) (R 8) [66,33,48,68,129] 13 :=
  permutation_upper _ _ _ [66,33,40,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10486

theorem m20038_136 : Upper (D 8) (R 8) [66,33,48,68,136] 13 :=
  permutation_upper _ _ _ [66,33,40,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10504

theorem m20038_160 : Upper (D 8) (R 8) [66,33,48,68,160] 13 :=
  permutation_upper _ _ _ [66,33,40,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10515

theorem m20038_257 : Upper (D 8) (R 8) [66,33,48,68,257] 13 :=
  permutation_upper _ _ _ [66,33,40,257,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10528

theorem m20038_264 : Upper (D 8) (R 8) [66,33,48,68,264] 13 :=
  permutation_upper _ _ _ [66,33,40,272,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10538

theorem m20038_288 : Upper (D 8) (R 8) [66,33,48,68,288] 13 :=
  permutation_upper _ _ _ [66,33,40,288,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10544

theorem m20038_384 : Upper (D 8) (R 8) [66,33,48,68,384] 13 :=
  permutation_upper _ _ _ [66,33,40,384,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10551

def r20038 : Route 9 := (fun mask => (mask,id))

def c20038 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20038 : Upper (D 8) (R 8) [66,33,48,68] 13 := by
  apply FastRouting.sound _ _ [66,33,48,68] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r20038 c20038
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20038_9
  · exact m20038_33
  · exact m20038_40
  · exact m20038_129
  · exact m20038_136
  · exact m20038_160
  · exact m20038_257
  · exact m20038_264
  · exact m20038_288
  · exact m20038_384

theorem m20039_9 : Upper (D 8) (R 8) [66,33,48,132,9] 13 :=
  permutation_upper _ _ _ [66,33,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10323

theorem m20039_33 : Upper (D 8) (R 8) [66,33,48,132,33] 13 :=
  permutation_upper _ _ _ [66,33,33,36,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10417

theorem m20039_40 : Upper (D 8) (R 8) [66,33,48,132,40] 13 :=
  permutation_upper _ _ _ [66,33,40,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10463

theorem m20039_65 : Upper (D 8) (R 8) [66,33,48,132,65] 13 :=
  permutation_upper _ _ _ [66,33,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10468

theorem m20039_72 : Upper (D 8) (R 8) [66,33,48,132,72] 13 :=
  permutation_upper _ _ _ [66,33,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10477

theorem m20039_96 : Upper (D 8) (R 8) [66,33,48,132,96] 13 :=
  permutation_upper _ _ _ [66,33,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10483

theorem m20039_129 : Upper (D 8) (R 8) [66,33,48,132,129] 13 :=
  permutation_upper _ _ _ [66,33,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10487

theorem m20039_136 : Upper (D 8) (R 8) [66,33,48,132,136] 13 :=
  permutation_upper _ _ _ [66,33,40,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10507

theorem m20039_160 : Upper (D 8) (R 8) [66,33,48,132,160] 13 :=
  permutation_upper _ _ _ [66,33,40,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10516

theorem m20039_192 : Upper (D 8) (R 8) [66,33,48,132,192] 13 :=
  permutation_upper _ _ _ [66,33,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10522

theorem m20039_257 : Upper (D 8) (R 8) [66,33,48,132,257] 13 :=
  permutation_upper _ _ _ [66,33,40,257,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10529

theorem m20039_264 : Upper (D 8) (R 8) [66,33,48,132,264] 13 :=
  permutation_upper _ _ _ [66,33,40,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10541

theorem m20039_288 : Upper (D 8) (R 8) [66,33,48,132,288] 13 :=
  permutation_upper _ _ _ [66,33,40,288,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10545

theorem m20039_320 : Upper (D 8) (R 8) [66,33,48,132,320] 13 :=
  permutation_upper _ _ _ [66,33,40,320,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10548

theorem m20039_384 : Upper (D 8) (R 8) [66,33,48,132,384] 13 :=
  permutation_upper _ _ _ [66,33,40,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10554

def r20039 : Route 9 := (fun mask => (mask,id))

def c20039 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u20039 : Upper (D 8) (R 8) [66,33,48,132] 13 := by
  apply FastRouting.sound _ _ [66,33,48,132] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r20039 c20039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20039_9
  · exact m20039_33
  · exact m20039_40
  · exact m20039_65
  · exact m20039_72
  · exact m20039_96
  · exact m20039_129
  · exact m20039_136
  · exact m20039_160
  · exact m20039_192
  · exact m20039_257
  · exact m20039_264
  · exact m20039_288
  · exact m20039_320
  · exact m20039_384

#print axioms u20039
end Delivery.IrregularNine14.P08
