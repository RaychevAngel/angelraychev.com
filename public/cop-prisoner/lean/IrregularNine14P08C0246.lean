import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0084
import IrregularNine14P08C0085

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14760 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 280 208 35 99 163 291), lower := (rows 97 38 140 280 208 32 64 128 256), losses := [] }

theorem u14760 : Upper (D 8) (R 8) [96,36,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14761 : PairBound 9 := { available := 147, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 296 81 179 211 147 403), lower := (rows 97 38 140 296 81 32 64 128 256), losses := [] }

theorem u14761 : Upper (D 8) (R 8) [96,36,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14762 : Route 9 := (fun mask => (mask,id))

def c14762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14762 : Upper (D 8) (R 8) [96,36,136,288,66] 13 := by
  apply FastRouting.sound _ _ [96,36,136,288,66] 13 (by decide) (choices 1) [1,16,128] r14762 c14762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5083
  · exact u5084
  · exact u5085

def r14763 : Route 9 := (fun mask => (mask,id))

def c14763 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14763 : Upper (D 8) (R 8) [96,36,136,288,129] 13 := by
  apply FastRouting.sound _ _ [96,36,136,288,129] 13 (by decide) (choices 1) [1,2,16,64] r14763 c14763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5086
  · exact u5087
  · exact u5088
  · exact u5089

def b14764 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 296 146 113 81 209 337), lower := (rows 97 38 140 296 146 32 64 128 256), losses := [] }

theorem u14764 : Upper (D 8) (R 8) [96,36,136,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14765 : Route 9 := (fun mask => (mask,id))

def c14765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14765 : Upper (D 8) (R 8) [96,36,136,288,192] 13 := by
  apply FastRouting.sound _ _ [96,36,136,288,192] 13 (by decide) (choices 1) [1,2,16] r14765 c14765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5090
  · exact u5091
  · exact u5092

def r14766 : Route 9 := (fun mask => (mask,id))

def c14766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14766 : Upper (D 8) (R 8) [96,36,136,320,129] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,129] 13 (by decide) (choices 1) [1,2,16] r14766 c14766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5093
  · exact u5094
  · exact u5095

def b14767 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 328 146 49 113 177 305), lower := (rows 97 38 140 328 146 32 64 128 256), losses := [] }

theorem u14767 : Upper (D 8) (R 8) [96,36,136,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14768 : Route 9 := (fun mask => (mask,id))

def c14768 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14768 : Upper (D 8) (R 8) [96,36,136,320,160] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,160] 13 (by decide) (choices 1) [1,2,16] r14768 c14768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5096
  · exact u5097
  · exact u5098

def b14769 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 392 82 49 113 177 305), lower := (rows 97 38 140 392 82 32 64 128 256), losses := [] }

theorem u14769 : Upper (D 8) (R 8) [96,36,136,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14770 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 74 145 313 345 409 281), lower := (rows 97 38 164 74 145 32 64 128 256), losses := [] }

theorem u14770 : Upper (D 8) (R 8) [96,36,160,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14771 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 74 152 305 337 401 273), lower := (rows 97 38 164 74 152 32 64 128 256), losses := [] }

theorem u14771 : Upper (D 8) (R 8) [96,36,160,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14772 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 74 273 185 217 153 409), lower := (rows 97 38 164 74 273 32 64 128 256), losses := [] }

theorem u14772 : Upper (D 8) (R 8) [96,36,160,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14773 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 74 280 177 209 145 401), lower := (rows 97 38 164 74 280 32 64 128 256), losses := [] }

theorem u14773 : Upper (D 8) (R 8) [96,36,160,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14774 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 74 400 57 89 153 281), lower := (rows 97 38 164 74 400 32 64 128 256), losses := [] }

theorem u14774 : Upper (D 8) (R 8) [96,36,160,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14775 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 88 145 299 331 395 267), lower := (rows 97 38 164 88 145 32 64 128 256), losses := [] }

theorem u14775 : Upper (D 8) (R 8) [96,36,160,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14776 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 88 146 297 329 393 265), lower := (rows 97 38 164 88 146 32 64 128 256), losses := [] }

theorem u14776 : Upper (D 8) (R 8) [96,36,160,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14777 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 88 273 171 203 139 395), lower := (rows 97 38 164 88 273 32 64 128 256), losses := [] }

theorem u14777 : Upper (D 8) (R 8) [96,36,160,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14778 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 88 274 169 201 137 393), lower := (rows 97 38 164 88 274 32 64 128 256), losses := [] }

theorem u14778 : Upper (D 8) (R 8) [96,36,160,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14779 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 88 400 43 75 139 267), lower := (rows 97 38 164 88 400 32 64 128 256), losses := [] }

theorem u14779 : Upper (D 8) (R 8) [96,36,160,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14780 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 137 273 122 90 218 346), lower := (rows 97 38 164 137 273 32 64 128 256), losses := [] }

theorem u14780 : Upper (D 8) (R 8) [96,36,160,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14781 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 137 274 121 89 217 345), lower := (rows 97 38 164 137 274 32 64 128 256), losses := [] }

theorem u14781 : Upper (D 8) (R 8) [96,36,160,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14782 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 137 280 115 83 211 339), lower := (rows 97 38 164 137 280 32 64 128 256), losses := [] }

theorem u14782 : Upper (D 8) (R 8) [96,36,160,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14783 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 137 336 59 91 155 283), lower := (rows 97 38 164 137 336 32 64 128 256), losses := [] }

theorem u14783 : Upper (D 8) (R 8) [96,36,160,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14784 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 138 273 121 89 217 345), lower := (rows 97 38 164 138 273 32 64 128 256), losses := [] }

theorem u14784 : Upper (D 8) (R 8) [96,36,160,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14785 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 138 280 113 81 209 337), lower := (rows 97 38 164 138 280 32 64 128 256), losses := [] }

theorem u14785 : Upper (D 8) (R 8) [96,36,160,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14786 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 138 336 57 89 153 281), lower := (rows 97 38 164 138 336 32 64 128 256), losses := [] }

theorem u14786 : Upper (D 8) (R 8) [96,36,160,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14787 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 152 273 107 75 203 331), lower := (rows 97 38 164 152 273 32 64 128 256), losses := [] }

theorem u14787 : Upper (D 8) (R 8) [96,36,160,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14788 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 152 274 105 73 201 329), lower := (rows 97 38 164 152 274 32 64 128 256), losses := [] }

theorem u14788 : Upper (D 8) (R 8) [96,36,160,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14789 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 152 280 99 67 195 323), lower := (rows 97 38 164 152 280 32 64 128 256), losses := [] }

theorem u14789 : Upper (D 8) (R 8) [96,36,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14790 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 152 336 43 75 139 267), lower := (rows 97 38 164 152 336 32 64 128 256), losses := [] }

theorem u14790 : Upper (D 8) (R 8) [96,36,160,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14791 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 200 273 59 91 155 283), lower := (rows 97 38 164 200 273 32 64 128 256), losses := [] }

theorem u14791 : Upper (D 8) (R 8) [96,36,160,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14792 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 200 274 57 89 153 281), lower := (rows 97 38 164 200 274 32 64 128 256), losses := [] }

theorem u14792 : Upper (D 8) (R 8) [96,36,160,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14793 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 164 200 280 51 83 147 275), lower := (rows 97 38 164 200 280 32 64 128 256), losses := [] }

theorem u14793 : Upper (D 8) (R 8) [96,36,160,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14794 : Route 9 := (fun mask => (mask,id))

def c14794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14794 : Upper (D 8) (R 8) [96,36,192,48,257] 13 := by
  apply FastRouting.sound _ _ [96,36,192,48,257] 13 (by decide) (choices 1) [1,2,8,128] r14794 c14794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5099
  · exact u5100
  · exact u5101
  · exact u5102

def r14795 : Route 9 := (fun mask => (mask,id))

def c14795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14795 : Upper (D 8) (R 8) [96,36,192,48,258] 13 := by
  apply FastRouting.sound _ _ [96,36,192,48,258] 13 (by decide) (choices 1) [1,8,128] r14795 c14795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5103
  · exact u5104
  · exact u5105

def r14796 : Route 9 := (fun mask => (mask,id))

def c14796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14796 : Upper (D 8) (R 8) [96,36,192,48,264] 13 := by
  apply FastRouting.sound _ _ [96,36,192,48,264] 13 (by decide) (choices 1) [1,2,128] r14796 c14796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5106
  · exact u5107
  · exact u5108

def r14797 : Route 9 := (fun mask => (mask,id))

def c14797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14797 : Upper (D 8) (R 8) [96,36,192,48,384] 13 := by
  apply FastRouting.sound _ _ [96,36,192,48,384] 13 (by decide) (choices 1) [1,2,8] r14797 c14797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5109
  · exact u5110
  · exact u5111

def r14798 : Route 9 := (fun mask => (mask,id))

def c14798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14798 : Upper (D 8) (R 8) [96,36,192,129,257] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,257] 13 (by decide) (choices 1) [2,8,16] r14798 c14798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5112
  · exact u5113
  · exact u5114

def r14799 : Route 9 := (fun mask => (mask,id))

def c14799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14799 : Upper (D 8) (R 8) [96,36,192,129,258] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,258] 13 (by decide) (choices 1) [1,8,16] r14799 c14799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5115
  · exact u5116
  · exact u5117

def r14800 : Route 9 := (fun mask => (mask,id))

def c14800 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14800 : Upper (D 8) (R 8) [96,36,192,129,264] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,264] 13 (by decide) (choices 1) [1,2,16] r14800 c14800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5118
  · exact u5119
  · exact u5120

def r14801 : Route 9 := (fun mask => (mask,id))

def c14801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14801 : Upper (D 8) (R 8) [96,36,192,129,288] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,288] 13 (by decide) (choices 1) [1,2,8,16] r14801 c14801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5121
  · exact u5122
  · exact u5123
  · exact u5124

def b14802 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 138 273 57 121 185 313), lower := (rows 97 38 196 138 273 32 64 128 256), losses := [] }

theorem u14802 : Upper (D 8) (R 8) [96,36,192,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14803 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 138 280 49 113 177 305), lower := (rows 97 38 196 138 280 32 64 128 256), losses := [] }

theorem u14803 : Upper (D 8) (R 8) [96,36,192,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14804 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 138 304 57 89 153 281), lower := (rows 97 38 196 138 304 32 64 128 256), losses := [] }

theorem u14804 : Upper (D 8) (R 8) [96,36,192,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14805 : Route 9 := (fun mask => (mask,id))

def c14805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14805 : Upper (D 8) (R 8) [96,36,192,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,257] 13 (by decide) (choices 1) [1,2,8] r14805 c14805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5125
  · exact u5126
  · exact u5127

def b14806 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 152 274 41 105 169 297), lower := (rows 97 38 196 152 274 32 64 128 256), losses := [] }

theorem u14806 : Upper (D 8) (R 8) [96,36,192,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14807 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 152 280 35 99 163 291), lower := (rows 97 38 196 152 280 32 64 128 256), losses := [] }

theorem u14807 : Upper (D 8) (R 8) [96,36,192,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14808 : Route 9 := (fun mask => (mask,id))

def c14808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14808 : Upper (D 8) (R 8) [96,36,192,144,288] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,288] 13 (by decide) (choices 1) [1,2,8] r14808 c14808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5128
  · exact u5129
  · exact u5130

def r14809 : Route 9 := (fun mask => (mask,id))

def c14809 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14809 : Upper (D 8) (R 8) [96,36,192,160,257] 13 := by
  apply FastRouting.sound _ _ [96,36,192,160,257] 13 (by decide) (choices 1) [1,2,8,16] r14809 c14809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5131
  · exact u5132
  · exact u5133
  · exact u5134

def r14810 : Route 9 := (fun mask => (mask,id))

def c14810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14810 : Upper (D 8) (R 8) [96,36,192,160,258] 13 := by
  apply FastRouting.sound _ _ [96,36,192,160,258] 13 (by decide) (choices 1) [1,8,16] r14810 c14810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5135
  · exact u5136
  · exact u5137

def r14811 : Route 9 := (fun mask => (mask,id))

def c14811 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14811 : Upper (D 8) (R 8) [96,36,192,160,264] 13 := by
  apply FastRouting.sound _ _ [96,36,192,160,264] 13 (by decide) (choices 1) [1,2,16] r14811 c14811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5138
  · exact u5139
  · exact u5140

def b14812 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 73 146 184 248 184 440), lower := (rows 97 38 261 73 146 32 64 128 256), losses := [] }

theorem u14812 : Upper (D 8) (R 8) [96,36,257,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14813 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 73 152 178 242 178 434), lower := (rows 97 38 261 73 152 32 64 128 256), losses := [] }

theorem u14813 : Upper (D 8) (R 8) [96,36,257,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14814 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 73 176 186 218 154 410), lower := (rows 97 38 261 73 176 32 64 128 256), losses := [] }

theorem u14814 : Upper (D 8) (R 8) [96,36,257,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14815 : Route 9 := (fun mask => (mask,id))

def c14815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14815 : Upper (D 8) (R 8) [96,36,257,66,129] 13 := by
  apply FastRouting.sound _ _ [96,36,257,66,129] 13 (by decide) (choices 1) [8,16,128] r14815 c14815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5141
  · exact u5142
  · exact u5143

def r14816 : Route 9 := (fun mask => (mask,id))

def c14816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14816 : Upper (D 8) (R 8) [96,36,257,66,136] 13 := by
  apply FastRouting.sound _ _ [96,36,257,66,136] 13 (by decide) (choices 1) [1,16,128] r14816 c14816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5144
  · exact u5145
  · exact u5146

def r14817 : Route 9 := (fun mask => (mask,id))

def c14817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14817 : Upper (D 8) (R 8) [96,36,257,66,160] 13 := by
  apply FastRouting.sound _ _ [96,36,257,66,160] 13 (by decide) (choices 1) [1,8,16,128] r14817 c14817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5147
  · exact u5148
  · exact u5149
  · exact u5150

def r14818 : Route 9 := (fun mask => (mask,id))

def c14818 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14818 : Upper (D 8) (R 8) [96,36,257,80,129] 13 := by
  apply FastRouting.sound _ _ [96,36,257,80,129] 13 (by decide) (choices 1) [2,8,128] r14818 c14818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5151
  · exact u5152
  · exact u5153

def r14819 : Route 9 := (fun mask => (mask,id))

def c14819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14819 : Upper (D 8) (R 8) [96,36,257,80,130] 13 := by
  apply FastRouting.sound _ _ [96,36,257,80,130] 13 (by decide) (choices 1) [1,8,128] r14819 c14819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5154
  · exact u5155
  · exact u5156

#print axioms u14819
end Delivery.IrregularNine14.P08
