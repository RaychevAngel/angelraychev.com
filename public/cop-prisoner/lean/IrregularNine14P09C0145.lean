import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0108
import IrregularNine14P09C0109
import IrregularNine14P09C0110

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8700 : Route 9 := (fun mask => (mask,id))

def c8700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8700 : Upper (D 9) (R 9) [96,36,136,258,384] 13 := by
  apply FastRouting.sound _ _ [96,36,136,258,384] 13 (by decide) (choices 1) [1,16,64] r8700 c8700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6525
  · exact u6526
  · exact u6527

def r8701 : Route 9 := (fun mask => (mask,id))

def c8701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8701 : Upper (D 9) (R 9) [96,36,136,272,129] 13 := by
  apply FastRouting.sound _ _ [96,36,136,272,129] 13 (by decide) (choices 1) [1,2,64,256] r8701 c8701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6528
  · exact u6529
  · exact u6530
  · exact u6531

def r8702 : Route 9 := (fun mask => (mask,id))

def c8702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8702 : Upper (D 9) (R 9) [96,36,136,272,130] 13 := by
  apply FastRouting.sound _ _ [96,36,136,272,130] 13 (by decide) (choices 1) [1,64,256] r8702 c8702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6532
  · exact u6533
  · exact u6534

def r8703 : Route 9 := (fun mask => (mask,id))

def c8703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8703 : Upper (D 9) (R 9) [96,36,136,272,192] 13 := by
  apply FastRouting.sound _ _ [96,36,136,272,192] 13 (by decide) (choices 1) [1,2,256] r8703 c8703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6535
  · exact u6536
  · exact u6537

def b8704 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 38 140 280 273 227 195 195 451), lower := (rows 97 38 140 280 273 32 64 128 256), losses := [] }

theorem u8704 : Upper (D 9) (R 9) [96,36,136,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8704 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8705 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 225, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 38 140 280 274 225 193 193 449), lower := (rows 97 38 140 280 274 32 64 128 256), losses := [] }

theorem u8705 : Upper (D 9) (R 9) [96,36,136,272,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8705 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8706 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 38 140 280 336 163 195 131 387), lower := (rows 97 38 140 280 336 32 64 128 256), losses := [] }

theorem u8706 : Upper (D 9) (R 9) [96,36,136,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8706 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8707 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0),(3,5)], upper := (rows 97 38 140 280 400 99 67 195 323), lower := (rows 97 38 140 280 400 32 64 128 256), losses := [] }

theorem u8707 : Upper (D 9) (R 9) [96,36,136,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8707 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8708 : Route 9 := (fun mask => (mask,id))

def c8708 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8708 : Upper (D 9) (R 9) [96,36,136,320,129] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,129] 13 (by decide) (choices 1) [1,2,16,256] r8708 c8708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6538
  · exact u6539
  · exact u6540
  · exact u6541

def r8709 : Route 9 := (fun mask => (mask,id))

def c8709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8709 : Upper (D 9) (R 9) [96,36,136,320,130] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,130] 13 (by decide) (choices 1) [1,16,256] r8709 c8709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6542
  · exact u6543
  · exact u6544

def r8710 : Route 9 := (fun mask => (mask,id))

def c8710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8710 : Upper (D 9) (R 9) [96,36,136,320,257] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,257] 13 (by decide) (choices 1) [1,2,16,128] r8710 c8710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6545
  · exact u6546
  · exact u6547
  · exact u6548

def r8711 : Route 9 := (fun mask => (mask,id))

def c8711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8711 : Upper (D 9) (R 9) [96,36,136,320,258] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,258] 13 (by decide) (choices 1) [1,16,128] r8711 c8711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6549
  · exact u6550
  · exact u6551

def r8712 : Route 9 := (fun mask => (mask,id))

def c8712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8712 : Upper (D 9) (R 9) [96,36,136,320,384] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,384] 13 (by decide) (choices 1) [1,2,16] r8712 c8712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6552
  · exact u6553
  · exact u6554

def b8713 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 392 273 115 83 211 339), lower := (rows 97 38 140 392 273 32 64 128 256), losses := [] }

theorem u8713 : Upper (D 9) (R 9) [96,36,136,384,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8713 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8714 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 392 274 113 81 209 337), lower := (rows 97 38 140 392 274 32 64 128 256), losses := [] }

theorem u8714 : Upper (D 9) (R 9) [96,36,136,384,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8714 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8715 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 38 140 392 336 51 83 147 275), lower := (rows 97 38 140 392 336 32 64 128 256), losses := [] }

theorem u8715 : Upper (D 9) (R 9) [96,36,136,384,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8715 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8716 : Route 9 := (fun mask => (mask,id))

def c8716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8716 : Upper (D 9) (R 9) [96,36,192,129,257] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,257] 13 (by decide) (choices 1) [2,8,16,256] r8716 c8716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6555
  · exact u6556
  · exact u6557
  · exact u6558

def r8717 : Route 9 := (fun mask => (mask,id))

def c8717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8717 : Upper (D 9) (R 9) [96,36,192,129,258] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,258] 13 (by decide) (choices 1) [1,8,16,256] r8717 c8717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6559
  · exact u6560
  · exact u6561
  · exact u6562

def r8718 : Route 9 := (fun mask => (mask,id))

def c8718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8718 : Upper (D 9) (R 9) [96,36,192,129,264] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,264] 13 (by decide) (choices 1) [1,2,16,256] r8718 c8718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6563
  · exact u6564
  · exact u6565
  · exact u6566

def r8719 : Route 9 := (fun mask => (mask,id))

def c8719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8719 : Upper (D 9) (R 9) [96,36,192,130,257] 13 := by
  apply FastRouting.sound _ _ [96,36,192,130,257] 13 (by decide) (choices 1) [1,8,16,256] r8719 c8719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6567
  · exact u6568
  · exact u6569
  · exact u6570

def r8720 : Route 9 := (fun mask => (mask,id))

def c8720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8720 : Upper (D 9) (R 9) [96,36,192,130,264] 13 := by
  apply FastRouting.sound _ _ [96,36,192,130,264] 13 (by decide) (choices 1) [1,16,256] r8720 c8720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6571
  · exact u6572
  · exact u6573

def r8721 : Route 9 := (fun mask => (mask,id))

def c8721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8721 : Upper (D 9) (R 9) [96,36,192,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,257] 13 (by decide) (choices 1) [1,2,8,256] r8721 c8721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6574
  · exact u6575
  · exact u6576
  · exact u6577

def r8722 : Route 9 := (fun mask => (mask,id))

def c8722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8722 : Upper (D 9) (R 9) [96,36,192,144,258] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,258] 13 (by decide) (choices 1) [1,8,256] r8722 c8722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6578
  · exact u6579
  · exact u6580

def r8723 : Route 9 := (fun mask => (mask,id))

def c8723 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8723 : Upper (D 9) (R 9) [96,36,192,144,264] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,264] 13 (by decide) (choices 1) [1,2,256] r8723 c8723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6581
  · exact u6582
  · exact u6583

def b8724 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 97 38 196 265 273 186 218 154 410), lower := (rows 97 38 196 265 273 32 64 128 256), losses := [] }

theorem u8724 : Upper (D 9) (R 9) [96,36,192,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8724 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8725 : Route 9 := (fun mask => (mask,id))

def c8725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8725 : Upper (D 9) (R 9) [96,36,192,257,258] 13 := by
  apply FastRouting.sound _ _ [96,36,192,257,258] 13 (by decide) (choices 1) [1,8,16,128] r8725 c8725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6584
  · exact u6585
  · exact u6586
  · exact u6587

def b8726 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 97 38 196 265 280 179 211 147 403), lower := (rows 97 38 196 265 280 32 64 128 256), losses := [] }

theorem u8726 : Upper (D 9) (R 9) [96,36,192,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8726 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8727 : Route 9 := (fun mask => (mask,id))

def c8727 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8727 : Upper (D 9) (R 9) [96,36,192,257,384] 13 := by
  apply FastRouting.sound _ _ [96,36,192,257,384] 13 (by decide) (choices 1) [1,2,8,16] r8727 c8727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6588
  · exact u6589
  · exact u6590
  · exact u6591

def b8728 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 97 38 196 266 280 177 209 145 401), lower := (rows 97 38 196 266 280 32 64 128 256), losses := [] }

theorem u8728 : Upper (D 9) (R 9) [96,36,192,258,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8728 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8729 : Route 9 := (fun mask => (mask,id))

def c8729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8729 : Upper (D 9) (R 9) [96,36,192,258,384] 13 := by
  apply FastRouting.sound _ _ [96,36,192,258,384] 13 (by decide) (choices 1) [1,8,16] r8729 c8729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6592
  · exact u6593
  · exact u6594

def b8730 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 97 38 196 280 280 163 195 131 387), lower := (rows 97 38 196 280 280 32 64 128 256), losses := [] }

theorem u8730 : Upper (D 9) (R 9) [96,36,192,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8730 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8731 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 38 196 280 400 43 75 139 267), lower := (rows 97 38 196 280 400 32 64 128 256), losses := [] }

theorem u8731 : Upper (D 9) (R 9) [96,36,192,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8731 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8732 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 97 38 388 88 400 43 75 139 267), lower := (rows 97 38 388 88 400 32 64 128 256), losses := [] }

theorem u8732 : Upper (D 9) (R 9) [96,36,384,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8732 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8733_16 : Upper (D 9) (R 9) [96,36,384,129,257,16] 13 :=
  permutation_upper _ _ _ [96,36,384,129,257,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6596

def r8733 : Route 9 := (fun mask => (mask,id))

def c8733 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8733 : Upper (D 9) (R 9) [96,36,384,129,257] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,257] 13 (by decide) (choices 1) [2,8,16,64] r8733 c8733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6595
  · exact u6596
  · exact m8733_16
  · exact u6597

def r8734 : Route 9 := (fun mask => (mask,id))

def c8734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8734 : Upper (D 9) (R 9) [96,36,384,129,258] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,258] 13 (by decide) (choices 1) [1,8,16,64] r8734 c8734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6598
  · exact u6599
  · exact u6600
  · exact u6601

def r8735 : Route 9 := (fun mask => (mask,id))

def c8735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8735 : Upper (D 9) (R 9) [96,36,384,129,264] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,264] 13 (by decide) (choices 1) [1,2,16,64] r8735 c8735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6602
  · exact u6603
  · exact u6604
  · exact u6605

def r8736 : Route 9 := (fun mask => (mask,id))

def c8736 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8736 : Upper (D 9) (R 9) [96,36,384,129,320] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,320] 13 (by decide) (choices 1) [1,2,8,16] r8736 c8736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6606
  · exact u6607
  · exact u6608
  · exact u6609

def r8737 : Route 9 := (fun mask => (mask,id))

def c8737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8737 : Upper (D 9) (R 9) [96,36,384,130,264] 13 := by
  apply FastRouting.sound _ _ [96,36,384,130,264] 13 (by decide) (choices 1) [1,16,64] r8737 c8737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6610
  · exact u6611
  · exact u6612

def r8738 : Route 9 := (fun mask => (mask,id))

def c8738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8738 : Upper (D 9) (R 9) [96,36,384,130,320] 13 := by
  apply FastRouting.sound _ _ [96,36,384,130,320] 13 (by decide) (choices 1) [1,8,16] r8738 c8738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6613
  · exact u6614
  · exact u6615

def b8739 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0),(4,5)], upper := (rows 97 38 388 152 280 99 67 195 323), lower := (rows 97 38 388 152 280 32 64 128 256), losses := [] }

theorem u8739 : Upper (D 9) (R 9) [96,36,384,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8739 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8740 : Route 9 := (fun mask => (mask,id))

def c8740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8740 : Upper (D 9) (R 9) [96,36,384,144,320] 13 := by
  apply FastRouting.sound _ _ [96,36,384,144,320] 13 (by decide) (choices 1) [1,2,8] r8740 c8740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6616
  · exact u6617
  · exact u6618

def b8741 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 138 273 316 348 412 284), lower := (rows 97 98 133 138 273 32 64 128 256), losses := [] }

theorem u8741 : Upper (D 9) (R 9) [96,96,129,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8741 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8742 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 138 276 313 345 409 281), lower := (rows 97 98 133 138 276 32 64 128 256), losses := [] }

theorem u8742 : Upper (D 9) (R 9) [96,96,129,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8742 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8743 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 138 280 309 341 405 277), lower := (rows 97 98 133 138 280 32 64 128 256), losses := [] }

theorem u8743 : Upper (D 9) (R 9) [96,96,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8743 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8744 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 152 273 302 334 398 270), lower := (rows 97 98 133 152 273 32 64 128 256), losses := [] }

theorem u8744 : Upper (D 9) (R 9) [96,96,129,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8744 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8745 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 152 274 301 333 397 269), lower := (rows 97 98 133 152 274 32 64 128 256), losses := [] }

theorem u8745 : Upper (D 9) (R 9) [96,96,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8745 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8746 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 152 276 299 331 395 267), lower := (rows 97 98 133 152 276 32 64 128 256), losses := [] }

theorem u8746 : Upper (D 9) (R 9) [96,96,129,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8746 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8747 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 152 280 295 327 391 263), lower := (rows 97 98 133 152 280 32 64 128 256), losses := [] }

theorem u8747 : Upper (D 9) (R 9) [96,96,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8747 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8748 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 265 400 62 94 158 286), lower := (rows 97 98 133 265 400 32 64 128 256), losses := [] }

theorem u8748 : Upper (D 9) (R 9) [96,96,129,257,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8748 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8749 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 266 276 185 217 153 409), lower := (rows 97 98 133 266 276 32 64 128 256), losses := [] }

theorem u8749 : Upper (D 9) (R 9) [96,96,129,258,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8749 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8750 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 266 400 61 93 157 285), lower := (rows 97 98 133 266 400 32 64 128 256), losses := [] }

theorem u8750 : Upper (D 9) (R 9) [96,96,129,258,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8750 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8751 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 133 268 400 59 91 155 283), lower := (rows 97 98 133 268 400 32 64 128 256), losses := [] }

theorem u8751 : Upper (D 9) (R 9) [96,96,129,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8751 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8752 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 134 152 276 297 329 393 265), lower := (rows 97 98 134 152 276 32 64 128 256), losses := [] }

theorem u8752 : Upper (D 9) (R 9) [96,96,130,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8752 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8753 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 134 152 280 293 325 389 261), lower := (rows 97 98 134 152 280 32 64 128 256), losses := [] }

theorem u8753 : Upper (D 9) (R 9) [96,96,130,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8753 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8754 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 2, targets := 384 },{ cop := 1, region := 1, targets := 384 },{ cop := 0, region := 2, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(1,7),(1,8)], upper := (rows 97 98 134 268 400 57 89 153 281), lower := (rows 97 98 134 268 400 32 64 128 256), losses := [] }

theorem u8754 : Upper (D 9) (R 9) [96,96,130,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8754 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8755 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 4, targets := 352 },{ cop := 2, region := 2, targets := 96 }], pairs := [(1,5),(1,6),(2,5),(2,6),(2,8)], upper := (rows 97 131 133 266 276 120 120 248 376), lower := (rows 97 131 133 266 276 32 64 128 256), losses := [] }

theorem u8755 : Upper (D 9) (R 9) [96,129,129,258,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8755 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8756 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 4, targets := 352 },{ cop := 2, region := 2, targets := 96 }], pairs := [(1,5),(1,6),(2,5),(2,6),(2,8)], upper := (rows 97 131 133 266 304 124 92 220 348), lower := (rows 97 131 133 266 304 32 64 128 256), losses := [] }

theorem u8756 : Upper (D 9) (R 9) [96,129,129,258,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8756 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8757 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 4, targets := 352 },{ cop := 2, region := 2, targets := 96 }], pairs := [(1,5),(1,6),(2,5),(2,6),(2,8)], upper := (rows 97 131 133 296 336 62 94 158 286), lower := (rows 97 131 133 296 336 32 64 128 256), losses := [] }

theorem u8757 : Upper (D 9) (R 9) [96,129,129,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8757 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8758 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 4, targets := 353 },{ cop := 2, region := 377, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 131 134 265 276 120 120 248 376), lower := (rows 97 131 134 265 276 32 64 128 256), losses := [] }

theorem u8758 : Upper (D 9) (R 9) [96,129,130,257,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8758 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8759 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 4, targets := 353 },{ cop := 2, region := 377, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 131 134 265 304 124 92 220 348), lower := (rows 97 131 134 265 304 32 64 128 256), losses := [] }

theorem u8759 : Upper (D 9) (R 9) [96,129,130,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8759 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u8759
end Delivery.IrregularNine14.P09
