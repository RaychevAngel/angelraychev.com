import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0109

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17700 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 137 82 177 241 177 433), lower := (rows 289 38 76 137 82 32 64 128 256), losses := [] }

theorem u17700 : Upper (D 8) (R 8) [288,36,72,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17701 : Route 9 := (fun mask => (mask,id))

def c17701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17701 : Upper (D 8) (R 8) [288,36,72,129,96] 13 := by
  apply FastRouting.sound _ _ [288,36,72,129,96] 13 (by decide) (choices 1) [1,2,16,128] r17701 c17701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6559
  · exact u6560
  · exact u6561
  · exact u6562

def b17702 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 38 76 137 145 114 114 242 370), lower := (rows 289 38 76 137 145 32 64 128 256), losses := [] }

theorem u17702 : Upper (D 8) (R 8) [288,36,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17703 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 137 146 113 113 241 369), lower := (rows 289 38 76 137 146 32 64 128 256), losses := [] }

theorem u17703 : Upper (D 8) (R 8) [288,36,72,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17704 : Route 9 := (fun mask => (mask,id))

def c17704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17704 : Upper (D 8) (R 8) [288,36,72,129,160] 13 := by
  apply FastRouting.sound _ _ [288,36,72,129,160] 13 (by decide) (choices 1) [1,2,16,64] r17704 c17704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6563
  · exact u6564
  · exact u6565
  · exact u6566

def r17705 : Route 9 := (fun mask => (mask,id))

def c17705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17705 : Upper (D 8) (R 8) [288,36,72,129,192] 13 := by
  apply FastRouting.sound _ _ [288,36,72,129,192] 13 (by decide) (choices 1) [1,2,16] r17705 c17705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6567
  · exact u6568
  · exact u6569

def b17706 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 138 81 177 241 177 433), lower := (rows 289 38 76 138 81 32 64 128 256), losses := [] }

theorem u17706 : Upper (D 8) (R 8) [288,36,72,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17707 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 138 112 177 209 145 401), lower := (rows 289 38 76 138 112 32 64 128 256), losses := [] }

theorem u17707 : Upper (D 8) (R 8) [288,36,72,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17708 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 138 145 113 113 241 369), lower := (rows 289 38 76 138 145 32 64 128 256), losses := [] }

theorem u17708 : Upper (D 8) (R 8) [288,36,72,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17709 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 138 176 113 81 209 337), lower := (rows 289 38 76 138 176 32 64 128 256), losses := [] }

theorem u17709 : Upper (D 8) (R 8) [288,36,72,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17710 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 138 208 49 113 177 305), lower := (rows 289 38 76 138 208 32 64 128 256), losses := [] }

theorem u17710 : Upper (D 8) (R 8) [288,36,72,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17711 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 152 81 163 227 163 419), lower := (rows 289 38 76 152 81 32 64 128 256), losses := [] }

theorem u17711 : Upper (D 8) (R 8) [288,36,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17712 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 152 82 161 225 161 417), lower := (rows 289 38 76 152 82 32 64 128 256), losses := [] }

theorem u17712 : Upper (D 8) (R 8) [288,36,72,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17713 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 152 112 163 195 131 387), lower := (rows 289 38 76 152 112 32 64 128 256), losses := [] }

theorem u17713 : Upper (D 8) (R 8) [288,36,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17714 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 152 145 99 99 227 355), lower := (rows 289 38 76 152 145 32 64 128 256), losses := [] }

theorem u17714 : Upper (D 8) (R 8) [288,36,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17715 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 152 146 97 97 225 353), lower := (rows 289 38 76 152 146 32 64 128 256), losses := [] }

theorem u17715 : Upper (D 8) (R 8) [288,36,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17716 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 152 176 99 67 195 323), lower := (rows 289 38 76 152 176 32 64 128 256), losses := [] }

theorem u17716 : Upper (D 8) (R 8) [288,36,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17717 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 289 38 76 152 208 35 99 163 291), lower := (rows 289 38 76 152 208 32 64 128 256), losses := [] }

theorem u17717 : Upper (D 8) (R 8) [288,36,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17718 : Route 9 := (fun mask => (mask,id))

def c17718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17718 : Upper (D 8) (R 8) [288,36,72,160,65] 13 := by
  apply FastRouting.sound _ _ [288,36,72,160,65] 13 (by decide) (choices 1) [1,2,16,128] r17718 c17718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6570
  · exact u6571
  · exact u6572
  · exact u6573

def b17719 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 168 82 177 209 145 401), lower := (rows 289 38 76 168 82 32 64 128 256), losses := [] }

theorem u17719 : Upper (D 8) (R 8) [288,36,72,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17720 : Route 9 := (fun mask => (mask,id))

def c17720 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17720 : Upper (D 8) (R 8) [288,36,72,160,129] 13 := by
  apply FastRouting.sound _ _ [288,36,72,160,129] 13 (by decide) (choices 1) [1,2,16,64] r17720 c17720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6574
  · exact u6575
  · exact u6576
  · exact u6577

def b17721 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 168 146 113 81 209 337), lower := (rows 289 38 76 168 146 32 64 128 256), losses := [] }

theorem u17721 : Upper (D 8) (R 8) [288,36,72,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17722 : Route 9 := (fun mask => (mask,id))

def c17722 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17722 : Upper (D 8) (R 8) [288,36,72,160,192] 13 := by
  apply FastRouting.sound _ _ [288,36,72,160,192] 13 (by decide) (choices 1) [1,2,16] r17722 c17722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6578
  · exact u6579
  · exact u6580

def b17723 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 200 145 51 115 179 307), lower := (rows 289 38 76 200 145 32 64 128 256), losses := [] }

theorem u17723 : Upper (D 8) (R 8) [288,36,72,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17724 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 200 146 49 113 177 305), lower := (rows 289 38 76 200 146 32 64 128 256), losses := [] }

theorem u17724 : Upper (D 8) (R 8) [288,36,72,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17725 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 200 176 51 83 147 275), lower := (rows 289 38 76 200 176 32 64 128 256), losses := [] }

theorem u17725 : Upper (D 8) (R 8) [288,36,72,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17726 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 73 145 186 218 154 410), lower := (rows 289 38 100 73 145 32 64 128 256), losses := [] }

theorem u17726 : Upper (D 8) (R 8) [288,36,96,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17727 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 73 146 185 217 153 409), lower := (rows 289 38 100 73 146 32 64 128 256), losses := [] }

theorem u17727 : Upper (D 8) (R 8) [288,36,96,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17728 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 73 152 179 211 147 403), lower := (rows 289 38 100 73 152 32 64 128 256), losses := [] }

theorem u17728 : Upper (D 8) (R 8) [288,36,96,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17729 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 74 145 185 217 153 409), lower := (rows 289 38 100 74 145 32 64 128 256), losses := [] }

theorem u17729 : Upper (D 8) (R 8) [288,36,96,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17730 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 74 152 177 209 145 401), lower := (rows 289 38 100 74 152 32 64 128 256), losses := [] }

theorem u17730 : Upper (D 8) (R 8) [288,36,96,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17731 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 88 145 171 203 139 395), lower := (rows 289 38 100 88 145 32 64 128 256), losses := [] }

theorem u17731 : Upper (D 8) (R 8) [288,36,96,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17732 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 88 146 169 201 137 393), lower := (rows 289 38 100 88 146 32 64 128 256), losses := [] }

theorem u17732 : Upper (D 8) (R 8) [288,36,96,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17733 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 88 152 163 195 131 387), lower := (rows 289 38 100 88 152 32 64 128 256), losses := [] }

theorem u17733 : Upper (D 8) (R 8) [288,36,96,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17734 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 137 146 121 89 217 345), lower := (rows 289 38 100 137 146 32 64 128 256), losses := [] }

theorem u17734 : Upper (D 8) (R 8) [288,36,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17735 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 137 208 59 91 155 283), lower := (rows 289 38 100 137 208 32 64 128 256), losses := [] }

theorem u17735 : Upper (D 8) (R 8) [288,36,96,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17736 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 138 208 57 89 153 281), lower := (rows 289 38 100 138 208 32 64 128 256), losses := [] }

theorem u17736 : Upper (D 8) (R 8) [288,36,96,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17737 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 38 196 56 208 43 75 139 267), lower := (rows 289 38 196 56 208 32 64 128 256), losses := [] }

theorem u17737 : Upper (D 8) (R 8) [288,36,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17738_16 : Upper (D 8) (R 8) [288,36,192,65,129,16] 13 :=
  permutation_upper _ _ _ [288,36,192,65,129,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6582

def r17738 : Route 9 := (fun mask => (mask,id))

def c17738 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17738 : Upper (D 8) (R 8) [288,36,192,65,129] 13 := by
  apply FastRouting.sound _ _ [288,36,192,65,129] 13 (by decide) (choices 1) [2,8,16] r17738 c17738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6581
  · exact u6582
  · exact m17738_16

def b17739 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 196 73 146 57 121 185 313), lower := (rows 289 38 196 73 146 32 64 128 256), losses := [] }

theorem u17739 : Upper (D 8) (R 8) [288,36,192,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17740 : Route 9 := (fun mask => (mask,id))

def c17740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17740 : Upper (D 8) (R 8) [288,36,192,65,136] 13 := by
  apply FastRouting.sound _ _ [288,36,192,65,136] 13 (by decide) (choices 1) [1,2,16] r17740 c17740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6583
  · exact u6584
  · exact u6585

def r17741 : Route 9 := (fun mask => (mask,id))

def c17741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17741 : Upper (D 8) (R 8) [288,36,192,65,160] 13 := by
  apply FastRouting.sound _ _ [288,36,192,65,160] 13 (by decide) (choices 1) [1,2,8,16] r17741 c17741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6586
  · exact u6587
  · exact u6588
  · exact u6589

def b17742 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 196 74 152 49 113 177 305), lower := (rows 289 38 196 74 152 32 64 128 256), losses := [] }

theorem u17742 : Upper (D 8) (R 8) [288,36,192,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17743 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 196 74 176 57 89 153 281), lower := (rows 289 38 196 74 176 32 64 128 256), losses := [] }

theorem u17743 : Upper (D 8) (R 8) [288,36,192,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17744 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 196 88 152 35 99 163 291), lower := (rows 289 38 196 88 152 32 64 128 256), losses := [] }

theorem u17744 : Upper (D 8) (R 8) [288,36,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17745 : Route 9 := (fun mask => (mask,id))

def c17745 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17745 : Upper (D 8) (R 8) [288,36,192,80,160] 13 := by
  apply FastRouting.sound _ _ [288,36,192,80,160] 13 (by decide) (choices 1) [1,2,8] r17745 c17745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6590
  · exact u6591
  · exact u6592

def b17746 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 289 67 69 138 148 56 120 184 312), lower := (rows 289 67 69 138 148 32 64 128 256), losses := [] }

theorem u17746 : Upper (D 8) (R 8) [288,65,65,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17747 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 289 67 69 138 176 60 124 188 316), lower := (rows 289 67 69 138 176 32 64 128 256), losses := [] }

theorem u17747 : Upper (D 8) (R 8) [288,65,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17748 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 67 70 137 148 56 120 184 312), lower := (rows 289 67 70 137 148 32 64 128 256), losses := [] }

theorem u17748 : Upper (D 8) (R 8) [288,65,66,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17749 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 67 70 137 176 60 124 188 316), lower := (rows 289 67 70 137 176 32 64 128 256), losses := [] }

theorem u17749 : Upper (D 8) (R 8) [288,65,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17750 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 67 70 140 176 57 121 185 313), lower := (rows 289 67 70 140 176 32 64 128 256), losses := [] }

theorem u17750 : Upper (D 8) (R 8) [288,65,66,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17751_16 : Upper (D 8) (R 8) [288,65,72,129,130,16] 13 :=
  permutation_upper _ _ _ [288,65,72,129,130,4] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6593

def r17751 : Route 9 := (fun mask => (mask,id))

def c17751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17751 : Upper (D 8) (R 8) [288,65,72,129,130] 13 := by
  apply FastRouting.sound _ _ [288,65,72,129,130] 13 (by decide) (choices 1) [4,16] r17751 c17751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6593
  · exact m17751_16

def b17752 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 137 148 50 114 178 306), lower := (rows 289 67 76 137 148 32 64 128 256), losses := [] }

theorem u17752 : Upper (D 8) (R 8) [288,65,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17753 : Route 9 := (fun mask => (mask,id))

def c17753 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17753 : Upper (D 8) (R 8) [288,65,72,129,160] 13 := by
  apply FastRouting.sound _ _ [288,65,72,129,160] 13 (by decide) (choices 1) [2,4,16] r17753 c17753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6594
  · exact u6595
  · exact u6596

def b17754 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 138 148 49 113 177 305), lower := (rows 289 67 76 138 148 32 64 128 256), losses := [] }

theorem u17754 : Upper (D 8) (R 8) [288,65,72,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17755 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 138 176 53 117 181 309), lower := (rows 289 67 76 138 176 32 64 128 256), losses := [] }

theorem u17755 : Upper (D 8) (R 8) [288,65,72,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17756 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 140 145 50 114 178 306), lower := (rows 289 67 76 140 145 32 64 128 256), losses := [] }

theorem u17756 : Upper (D 8) (R 8) [288,65,72,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17757 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 140 146 49 113 177 305), lower := (rows 289 67 76 140 146 32 64 128 256), losses := [] }

theorem u17757 : Upper (D 8) (R 8) [288,65,72,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17758 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 140 176 51 115 179 307), lower := (rows 289 67 76 140 176 32 64 128 256), losses := [] }

theorem u17758 : Upper (D 8) (R 8) [288,65,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17759 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 152 146 37 101 165 293), lower := (rows 289 67 76 152 146 32 64 128 256), losses := [] }

theorem u17759 : Upper (D 8) (R 8) [288,65,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17759
end Delivery.IrregularNine14.P08
