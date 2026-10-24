import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0708
import IrregularNine14P06C0709
import IrregularNine14P06C0710
import IrregularNine14P06C0711
import IrregularNine14P06C0712
import IrregularNine14P06C0713
import IrregularNine14P06C0714
import IrregularNine14P06C0715

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b43860 : PairBound 9 := { available := 350, camps := [{ cop := 5, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 35 133 350 350 382 350 478 350), lower := (rows 35 35 133 8 16 32 64 128 256), losses := [] }

theorem u43860 : Upper (D 6) (R 6) [34,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43861 : PairBound 9 := { available := 343, camps := [{ cop := 5, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 35 140 351 343 375 343 471 343), lower := (rows 35 35 140 8 16 32 64 128 256), losses := [] }

theorem u43861 : Upper (D 6) (R 6) [34,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43862 : PairBound 9 := { available := 351, camps := [{ cop := 5, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 35 196 351 351 383 351 479 351), lower := (rows 35 35 196 8 16 32 64 128 256), losses := [] }

theorem u43862 : Upper (D 6) (R 6) [34,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43863 : PairBound 9 := { available := 95, camps := [{ cop := 5, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 35 388 95 95 127 95 223 351), lower := (rows 35 35 388 8 16 32 64 128 256), losses := [] }

theorem u43863 : Upper (D 6) (R 6) [34,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43864 : PairBound 9 := { available := 479, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 38 69 479 479 511 479 479 479), lower := (rows 35 38 69 8 16 32 64 128 256), losses := [] }

theorem u43864 : Upper (D 6) (R 6) [34,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43865 : PairBound 9 := { available := 477, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 38 70 477 477 509 477 477 477), lower := (rows 35 38 70 8 16 32 64 128 256), losses := [] }

theorem u43865 : Upper (D 6) (R 6) [34,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43866 : PairBound 9 := { available := 471, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 38 76 479 471 503 471 471 471), lower := (rows 35 38 76 8 16 32 64 128 256), losses := [] }

theorem u43866 : Upper (D 6) (R 6) [34,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43867 : PairBound 9 := { available := 351, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 38 133 351 351 383 351 479 351), lower := (rows 35 38 133 8 16 32 64 128 256), losses := [] }

theorem u43867 : Upper (D 6) (R 6) [34,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43868 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 38 134 349 349 381 349 477 349), lower := (rows 35 38 134 8 16 32 64 128 256), losses := [] }

theorem u43868 : Upper (D 6) (R 6) [34,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43869 : PairBound 9 := { available := 343, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 38 140 351 343 375 343 471 343), lower := (rows 35 38 140 8 16 32 64 128 256), losses := [] }

theorem u43869 : Upper (D 6) (R 6) [34,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43870 : PairBound 9 := { available := 351, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 38 196 351 351 383 351 479 351), lower := (rows 35 38 196 8 16 32 64 128 256), losses := [] }

theorem u43870 : Upper (D 6) (R 6) [34,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43871 : PairBound 9 := { available := 95, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 38 388 95 95 127 95 223 351), lower := (rows 35 38 388 8 16 32 64 128 256), losses := [] }

theorem u43871 : Upper (D 6) (R 6) [34,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43872 : PairBound 9 := { available := 471, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 42 69 479 471 503 471 471 471), lower := (rows 35 42 69 8 16 32 64 128 256), losses := [] }

theorem u43872 : Upper (D 6) (R 6) [34,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43873 : PairBound 9 := { available := 469, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 42 70 477 469 501 469 469 469), lower := (rows 35 42 70 8 16 32 64 128 256), losses := [] }

theorem u43873 : Upper (D 6) (R 6) [34,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43874 : PairBound 9 := { available := 455, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 42 84 463 471 487 455 455 455), lower := (rows 35 42 84 8 16 32 64 128 256), losses := [] }

theorem u43874 : Upper (D 6) (R 6) [34,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43875 : PairBound 9 := { available := 343, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 42 133 351 343 375 343 471 343), lower := (rows 35 42 133 8 16 32 64 128 256), losses := [] }

theorem u43875 : Upper (D 6) (R 6) [34,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43876 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 42 134 349 341 373 341 469 341), lower := (rows 35 42 134 8 16 32 64 128 256), losses := [] }

theorem u43876 : Upper (D 6) (R 6) [34,40,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43877 : PairBound 9 := { available := 327, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 42 148 335 343 359 327 455 327), lower := (rows 35 42 148 8 16 32 64 128 256), losses := [] }

theorem u43877 : Upper (D 6) (R 6) [34,40,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43878 : PairBound 9 := { available := 343, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 42 196 351 343 375 343 471 343), lower := (rows 35 42 196 8 16 32 64 128 256), losses := [] }

theorem u43878 : Upper (D 6) (R 6) [34,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43879 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 42 388 95 87 119 87 215 343), lower := (rows 35 42 388 8 16 32 64 128 256), losses := [] }

theorem u43879 : Upper (D 6) (R 6) [34,40,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43880 : PairBound 9 := { available := 477, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 64 },{ cop := 2, region := 1, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 35 67 38 477 477 509 477 477 477), lower := (rows 35 67 38 8 16 32 64 128 256), losses := [] }

theorem u43880 : Upper (D 6) (R 6) [34,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43881 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43881 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43881 : Upper (D 6) (R 6) [34,65,40] 13 := by
  apply FastRouting.sound _ _ [34,65,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192,384] r43881 c43881
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42491
  · exact u42492
  · exact u42493
  · exact u42494
  · exact u42495
  · exact u42496
  · exact u42497
  · exact u42498
  · exact u42499
  · exact u42500
  · exact u42501
  · exact u42502
  · exact u42503
  · exact u42504
  · exact u42505
  · exact u42506

theorem m43882_6 : Upper (D 6) (R 6) [34,65,96,6] 13 :=
  permutation_upper _ _ _ [34,65,96,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42508

theorem m43882_18 : Upper (D 6) (R 6) [34,65,96,18] 13 :=
  permutation_upper _ _ _ [34,65,96,17] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42509

theorem m43882_130 : Upper (D 6) (R 6) [34,65,96,130] 13 :=
  permutation_upper _ _ _ [34,65,96,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42511

def r43882 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43882 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43882 : Upper (D 6) (R 6) [34,65,96] 13 := by
  apply FastRouting.sound _ _ [34,65,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r43882 c43882
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42507
  · exact u42508
  · exact m43882_6
  · exact u42509
  · exact m43882_18
  · exact u42510
  · exact u42511
  · exact m43882_130
  · exact u42512
  · exact u42513
  · exact u42514

def r43883 : Route 9 := (fun mask => (mask,id))

def c43883 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43883 : Upper (D 6) (R 6) [34,65,129] 13 := by
  apply FastRouting.sound _ _ [34,65,129] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,258,260,272,288,320] r43883 c43883
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42515
  · exact u42516
  · exact u42517
  · exact u42518
  · exact u42519
  · exact u42520
  · exact u42521
  · exact u42522
  · exact u42523
  · exact u42524
  · exact u42525
  · exact u42526
  · exact u42527
  · exact u42528
  · exact u42529

theorem m43884_6 : Upper (D 6) (R 6) [34,65,136,6] 13 :=
  permutation_upper _ _ _ [34,65,136,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42531

theorem m43884_18 : Upper (D 6) (R 6) [34,65,136,18] 13 :=
  permutation_upper _ _ _ [34,65,136,17] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42532

theorem m43884_65 : Upper (D 6) (R 6) [34,65,136,65] 13 :=
  permutation_upper _ _ _ [34,65,136,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42535

theorem m43884_66 : Upper (D 6) (R 6) [34,65,136,66] 13 :=
  permutation_upper _ _ _ [34,65,136,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42534

theorem m43884_68 : Upper (D 6) (R 6) [34,65,136,68] 13 :=
  permutation_upper _ _ _ [34,65,136,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42536

theorem m43884_80 : Upper (D 6) (R 6) [34,65,136,80] 13 :=
  permutation_upper _ _ _ [34,65,136,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42537

theorem m43884_258 : Upper (D 6) (R 6) [34,65,136,258] 13 :=
  permutation_upper _ _ _ [34,65,136,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42539

theorem m43884_320 : Upper (D 6) (R 6) [34,65,136,320] 13 :=
  permutation_upper _ _ _ [34,65,136,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42542

def r43884 : Route 9 := (fun mask => (mask,id))

def c43884 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43884 : Upper (D 6) (R 6) [34,65,136] 13 := by
  apply FastRouting.sound _ _ [34,65,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43884 c43884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42530
  · exact u42531
  · exact m43884_6
  · exact u42532
  · exact m43884_18
  · exact u42533
  · exact u42534
  · exact u42535
  · exact u42536
  · exact u42537
  · exact m43884_65
  · exact m43884_66
  · exact m43884_68
  · exact m43884_80
  · exact u42538
  · exact u42539
  · exact m43884_258
  · exact u42540
  · exact u42541
  · exact u42542
  · exact m43884_320

def r43885 : Route 9 := (fun mask => (mask,id))

def c43885 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43885 : Upper (D 6) (R 6) [34,65,160] 13 := by
  apply FastRouting.sound _ _ [34,65,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43885 c43885
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42543
  · exact u42544
  · exact u42545
  · exact u42546
  · exact u42547
  · exact u42548
  · exact u42549
  · exact u42550
  · exact u42551
  · exact u42552
  · exact u42553
  · exact u42554
  · exact u42555
  · exact u42556
  · exact u42557

theorem m43886_6 : Upper (D 6) (R 6) [34,65,384,6] 13 :=
  permutation_upper _ _ _ [34,65,384,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42559

theorem m43886_18 : Upper (D 6) (R 6) [34,65,384,18] 13 :=
  permutation_upper _ _ _ [34,65,384,17] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42560

theorem m43886_65 : Upper (D 6) (R 6) [34,65,384,65] 13 :=
  permutation_upper _ _ _ [34,65,384,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42563

theorem m43886_66 : Upper (D 6) (R 6) [34,65,384,66] 13 :=
  permutation_upper _ _ _ [34,65,384,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42562

theorem m43886_68 : Upper (D 6) (R 6) [34,65,384,68] 13 :=
  permutation_upper _ _ _ [34,65,384,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42564

theorem m43886_80 : Upper (D 6) (R 6) [34,65,384,80] 13 :=
  permutation_upper _ _ _ [34,65,384,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42565

def r43886 : Route 9 := (fun mask => (mask,id))

def c43886 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43886 : Upper (D 6) (R 6) [34,65,384] 13 := by
  apply FastRouting.sound _ _ [34,65,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43886 c43886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42558
  · exact u42559
  · exact m43886_6
  · exact u42560
  · exact m43886_18
  · exact u42561
  · exact u42562
  · exact u42563
  · exact u42564
  · exact u42565
  · exact m43886_65
  · exact m43886_66
  · exact m43886_68
  · exact m43886_80
  · exact u42566

def r43887 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43887 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43887 : Upper (D 6) (R 6) [34,68,40] 13 := by
  apply FastRouting.sound _ _ [34,68,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192,384] r43887 c43887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42567
  · exact u42568
  · exact u42569
  · exact u42570
  · exact u42571
  · exact u42572
  · exact u42573
  · exact u42574
  · exact u42575
  · exact u42576
  · exact u42577
  · exact u42578
  · exact u42579
  · exact u42580
  · exact u42581
  · exact u42582

def b43888 : PairBound 9 := { available := 415, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 100 415 415 447 479 415 415), lower := (rows 35 70 100 8 16 32 64 128 256), losses := [] }

theorem u43888 : Upper (D 6) (R 6) [34,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43889 : Route 9 := (fun mask => (mask,id))

def c43889 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43889 : Upper (D 6) (R 6) [34,68,129] 13 := by
  apply FastRouting.sound _ _ [34,68,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43889 c43889
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42583
  · exact u42584
  · exact u42585
  · exact u42586
  · exact u42587
  · exact u42588
  · exact u42589
  · exact u42590
  · exact u42591
  · exact u42592
  · exact u42593
  · exact u42594
  · exact u42595
  · exact u42596
  · exact u42597
  · exact u42598
  · exact u42599
  · exact u42600
  · exact u42601
  · exact u42602
  · exact u42603

def r43890 : Route 9 := (fun mask => (mask,id))

def c43890 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43890 : Upper (D 6) (R 6) [34,68,130] 13 := by
  apply FastRouting.sound _ _ [34,68,130] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r43890 c43890
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42604
  · exact u42605
  · exact u42606
  · exact u42607
  · exact u42608
  · exact u42609
  · exact u42610
  · exact u42611
  · exact u42612
  · exact u42613
  · exact u42614
  · exact u42615
  · exact u42616
  · exact u42617
  · exact u42618

def r43891 : Route 9 := (fun mask => (mask,id))

def c43891 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43891 : Upper (D 6) (R 6) [34,68,136] 13 := by
  apply FastRouting.sound _ _ [34,68,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43891 c43891
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42619
  · exact u42620
  · exact u42621
  · exact u42622
  · exact u42623
  · exact u42624
  · exact u42625
  · exact u42626
  · exact u42627
  · exact u42628
  · exact u42629
  · exact u42630
  · exact u42631
  · exact u42632
  · exact u42633
  · exact u42634
  · exact u42635
  · exact u42636
  · exact u42637
  · exact u42638
  · exact u42639

def r43892 : Route 9 := (fun mask => (mask,id))

def c43892 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43892 : Upper (D 6) (R 6) [34,68,160] 13 := by
  apply FastRouting.sound _ _ [34,68,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43892 c43892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42640
  · exact u42641
  · exact u42642
  · exact u42643
  · exact u42644
  · exact u42645
  · exact u42646
  · exact u42647
  · exact u42648
  · exact u42649
  · exact u42650
  · exact u42651
  · exact u42652
  · exact u42653
  · exact u42654

def b43893 : PairBound 9 := { available := 319, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 196 319 319 319 383 447 319), lower := (rows 35 70 196 8 16 32 64 128 256), losses := [] }

theorem u43893 : Upper (D 6) (R 6) [34,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43894 : Route 9 := (fun mask => (mask,id))

def c43894 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43894 : Upper (D 6) (R 6) [34,68,384] 13 := by
  apply FastRouting.sound _ _ [34,68,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43894 c43894
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42655
  · exact u42656
  · exact u42657
  · exact u42658
  · exact u42659
  · exact u42660
  · exact u42661
  · exact u42662
  · exact u42663
  · exact u42664
  · exact u42665
  · exact u42666
  · exact u42667
  · exact u42668
  · exact u42669

def b43895 : PairBound 9 := { available := 469, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 64 },{ cop := 2, region := 1, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 35 74 38 477 469 501 469 469 469), lower := (rows 35 74 38 8 16 32 64 128 256), losses := [] }

theorem u43895 : Upper (D 6) (R 6) [34,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43896 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43896 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43896 : Upper (D 6) (R 6) [34,72,48] 13 := by
  apply FastRouting.sound _ _ [34,72,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r43896 c43896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42670
  · exact u42671
  · exact u42672
  · exact u42673
  · exact u42674
  · exact u42675
  · exact u42676
  · exact u42677
  · exact u42678
  · exact u42679
  · exact u42680

def r43897 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43897 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43897 : Upper (D 6) (R 6) [34,72,80] 13 := by
  apply FastRouting.sound _ _ [34,72,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r43897 c43897
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42681
  · exact u42682
  · exact u42683
  · exact u42684
  · exact u42685
  · exact u42686
  · exact u42687
  · exact u42688
  · exact u42689
  · exact u42690
  · exact u42691

def r43898 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43898 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43898 : Upper (D 6) (R 6) [34,72,96] 13 := by
  apply FastRouting.sound _ _ [34,72,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r43898 c43898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42692
  · exact u42693
  · exact u42694
  · exact u42695
  · exact u42696
  · exact u42697
  · exact u42698
  · exact u42699
  · exact u42700
  · exact u42701
  · exact u42702

def r43899 : Route 9 := (fun mask => (mask,id))

def c43899 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43899 : Upper (D 6) (R 6) [34,72,129] 13 := by
  apply FastRouting.sound _ _ [34,72,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43899 c43899
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42703
  · exact u42704
  · exact u42705
  · exact u42706
  · exact u42707
  · exact u42708
  · exact u42709
  · exact u42710
  · exact u42711
  · exact u42712
  · exact u42713
  · exact u42714
  · exact u42715
  · exact u42716
  · exact u42717
  · exact u42718
  · exact u42719
  · exact u42720
  · exact u42721
  · exact u42722
  · exact u42723

def r43900 : Route 9 := (fun mask => (mask,id))

def c43900 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43900 : Upper (D 6) (R 6) [34,72,130] 13 := by
  apply FastRouting.sound _ _ [34,72,130] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r43900 c43900
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42724
  · exact u42725
  · exact u42726
  · exact u42727
  · exact u42728
  · exact u42729
  · exact u42730
  · exact u42731
  · exact u42732
  · exact u42733
  · exact u42734
  · exact u42735
  · exact u42736
  · exact u42737
  · exact u42738

def r43901 : Route 9 := (fun mask => (mask,id))

def c43901 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43901 : Upper (D 6) (R 6) [34,72,144] 13 := by
  apply FastRouting.sound _ _ [34,72,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43901 c43901
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42739
  · exact u42740
  · exact u42741
  · exact u42742
  · exact u42743
  · exact u42744
  · exact u42745
  · exact u42746
  · exact u42747
  · exact u42748
  · exact u42749
  · exact u42750
  · exact u42751
  · exact u42752
  · exact u42753

def r43902 : Route 9 := (fun mask => (mask,id))

def c43902 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43902 : Upper (D 6) (R 6) [34,72,160] 13 := by
  apply FastRouting.sound _ _ [34,72,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43902 c43902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42754
  · exact u42755
  · exact u42756
  · exact u42757
  · exact u42758
  · exact u42759
  · exact u42760
  · exact u42761
  · exact u42762
  · exact u42763
  · exact u42764
  · exact u42765
  · exact u42766
  · exact u42767
  · exact u42768

def r43903 : Route 9 := (fun mask => (mask,id))

def c43903 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43903 : Upper (D 6) (R 6) [34,72,192] 13 := by
  apply FastRouting.sound _ _ [34,72,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r43903 c43903
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42769
  · exact u42770
  · exact u42771
  · exact u42772
  · exact u42773
  · exact u42774
  · exact u42775
  · exact u42776
  · exact u42777
  · exact u42778
  · exact u42779
  · exact u42780
  · exact u42781
  · exact u42782
  · exact u42783

def r43904 : Route 9 := (fun mask => (mask,id))

def c43904 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43904 : Upper (D 6) (R 6) [34,72,384] 13 := by
  apply FastRouting.sound _ _ [34,72,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43904 c43904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42784
  · exact u42785
  · exact u42786
  · exact u42787
  · exact u42788
  · exact u42789
  · exact u42790
  · exact u42791
  · exact u42792
  · exact u42793
  · exact u42794
  · exact u42795
  · exact u42796
  · exact u42797
  · exact u42798

def b43905 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 98 76 415 407 439 471 407 407), lower := (rows 35 98 76 8 16 32 64 128 256), losses := [] }

theorem u43905 : Upper (D 6) (R 6) [34,96,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43906 : PairBound 9 := { available := 351, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 98 133 351 351 383 351 479 351), lower := (rows 35 98 133 8 16 32 64 128 256), losses := [] }

theorem u43906 : Upper (D 6) (R 6) [34,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43907 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 98 134 349 349 381 349 477 349), lower := (rows 35 98 134 8 16 32 64 128 256), losses := [] }

theorem u43907 : Upper (D 6) (R 6) [34,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43908 : PairBound 9 := { available := 343, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 98 140 351 343 375 343 471 343), lower := (rows 35 98 140 8 16 32 64 128 256), losses := [] }

theorem u43908 : Upper (D 6) (R 6) [34,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43909 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 98 196 287 287 319 351 415 287), lower := (rows 35 98 196 8 16 32 64 128 256), losses := [] }

theorem u43909 : Upper (D 6) (R 6) [34,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43910 : PairBound 9 := { available := 95, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 98 388 95 95 127 95 223 351), lower := (rows 35 98 388 8 16 32 64 128 256), losses := [] }

theorem u43910 : Upper (D 6) (R 6) [34,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43911 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 64 },{ cop := 2, region := 1, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 35 131 38 349 349 381 349 477 349), lower := (rows 35 131 38 8 16 32 64 128 256), losses := [] }

theorem u43911 : Upper (D 6) (R 6) [34,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43912 : Route 9 := (fun mask => (mask,id))

def c43912 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43912 : Upper (D 6) (R 6) [34,129,40] 13 := by
  apply FastRouting.sound _ _ [34,129,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43912 c43912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42799
  · exact u42800
  · exact u42801
  · exact u42802
  · exact u42803
  · exact u42804
  · exact u42805
  · exact u42806
  · exact u42807
  · exact u42808
  · exact u42809
  · exact u42810
  · exact u42811
  · exact u42812
  · exact u42813

def r43913 : Route 9 := (fun mask => (mask,id))

def c43913 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43913 : Upper (D 6) (R 6) [34,129,66] 13 := by
  apply FastRouting.sound _ _ [34,129,66] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r43913 c43913
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42814
  · exact u42815
  · exact u42816
  · exact u42817
  · exact u42818
  · exact u42819
  · exact u42820
  · exact u42821
  · exact u42822
  · exact u42823
  · exact u42824
  · exact u42825
  · exact u42826
  · exact u42827
  · exact u42828

def r43914 : Route 9 := (fun mask => (mask,id))

def c43914 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43914 : Upper (D 6) (R 6) [34,129,72] 13 := by
  apply FastRouting.sound _ _ [34,129,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43914 c43914
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42829
  · exact u42830
  · exact u42831
  · exact u42832
  · exact u42833
  · exact u42834
  · exact u42835
  · exact u42836
  · exact u42837
  · exact u42838
  · exact u42839
  · exact u42840
  · exact u42841
  · exact u42842
  · exact u42843
  · exact u42844
  · exact u42845
  · exact u42846
  · exact u42847
  · exact u42848
  · exact u42849

def r43915 : Route 9 := (fun mask => (mask,id))

def c43915 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43915 : Upper (D 6) (R 6) [34,129,96] 13 := by
  apply FastRouting.sound _ _ [34,129,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43915 c43915
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42850
  · exact u42851
  · exact u42852
  · exact u42853
  · exact u42854
  · exact u42855
  · exact u42856
  · exact u42857
  · exact u42858
  · exact u42859
  · exact u42860
  · exact u42861
  · exact u42862
  · exact u42863
  · exact u42864

def r43916 : Route 9 := (fun mask => (mask,id))

def c43916 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43916 : Upper (D 6) (R 6) [34,129,257] 13 := by
  apply FastRouting.sound _ _ [34,129,257] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96] r43916 c43916
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42865
  · exact u42866
  · exact u42867
  · exact u42868
  · exact u42869
  · exact u42870
  · exact u42871
  · exact u42872
  · exact u42873
  · exact u42874

def r43917 : Route 9 := (fun mask => (mask,id))

def c43917 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43917 : Upper (D 6) (R 6) [34,129,258] 13 := by
  apply FastRouting.sound _ _ [34,129,258] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] r43917 c43917
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42875
  · exact u42876
  · exact u42877
  · exact u42878
  · exact u42879
  · exact u42880
  · exact u42881
  · exact u42882
  · exact u42883
  · exact u42884

def r43918 : Route 9 := (fun mask => (mask,id))

def c43918 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43918 : Upper (D 6) (R 6) [34,129,264] 13 := by
  apply FastRouting.sound _ _ [34,129,264] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43918 c43918
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42885
  · exact u42886
  · exact u42887
  · exact u42888
  · exact u42889
  · exact u42890
  · exact u42891
  · exact u42892
  · exact u42893
  · exact u42894
  · exact u42895
  · exact u42896
  · exact u42897
  · exact u42898
  · exact u42899

def r43919 : Route 9 := (fun mask => (mask,id))

def c43919 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43919 : Upper (D 6) (R 6) [34,129,288] 13 := by
  apply FastRouting.sound _ _ [34,129,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43919 c43919
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42900
  · exact u42901
  · exact u42902
  · exact u42903
  · exact u42904
  · exact u42905
  · exact u42906
  · exact u42907
  · exact u42908
  · exact u42909

#print axioms u43919
end Delivery.IrregularNine14.P06
