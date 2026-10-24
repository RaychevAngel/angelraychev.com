import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0113
import IrregularNine14P08C0114
import IrregularNine14P08C0115

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r18540 : Route 9 := (fun mask => (mask,id))

def c18540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18540 : Upper (D 8) (R 8) [320,33,40,66,160] 13 := by
  apply FastRouting.sound _ _ [320,33,40,66,160] 13 (by decide) (choices 1) [1,4,16,128] r18540 c18540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6836
  · exact u6837
  · exact u6838
  · exact u6839

def b18541 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 76 145 178 242 178 434), lower := (rows 321 35 44 76 145 32 64 128 256), losses := [] }

theorem u18541 : Upper (D 8) (R 8) [320,33,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18542 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 76 146 177 241 177 433), lower := (rows 321 35 44 76 146 32 64 128 256), losses := [] }

theorem u18542 : Upper (D 8) (R 8) [320,33,40,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18543 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 76 176 179 211 147 403), lower := (rows 321 35 44 76 176 32 64 128 256), losses := [] }

theorem u18543 : Upper (D 8) (R 8) [320,33,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18544 : Route 9 := (fun mask => (mask,id))

def c18544 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18544 : Upper (D 8) (R 8) [320,33,40,80,129] 13 := by
  apply FastRouting.sound _ _ [320,33,40,80,129] 13 (by decide) (choices 1) [2,4,128] r18544 c18544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6840
  · exact u6841
  · exact u6842

def r18545 : Route 9 := (fun mask => (mask,id))

def c18545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18545 : Upper (D 8) (R 8) [320,33,40,80,130] 13 := by
  apply FastRouting.sound _ _ [320,33,40,80,130] 13 (by decide) (choices 1) [1,4,128] r18545 c18545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6843
  · exact u6844
  · exact u6845

def b18546 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 88 148 163 227 163 419), lower := (rows 321 35 44 88 148 32 64 128 256), losses := [] }

theorem u18546 : Upper (D 8) (R 8) [320,33,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18547 : Route 9 := (fun mask => (mask,id))

def c18547 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18547 : Upper (D 8) (R 8) [320,33,40,80,160] 13 := by
  apply FastRouting.sound _ _ [320,33,40,80,160] 13 (by decide) (choices 1) [1,2,4,128] r18547 c18547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6846
  · exact u6847
  · exact u6848
  · exact u6849

def b18548 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 104 145 182 214 150 406), lower := (rows 321 35 44 104 145 32 64 128 256), losses := [] }

theorem u18548 : Upper (D 8) (R 8) [320,33,40,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18549 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 104 146 181 213 149 405), lower := (rows 321 35 44 104 146 32 64 128 256), losses := [] }

theorem u18549 : Upper (D 8) (R 8) [320,33,40,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18550 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 104 148 179 211 147 403), lower := (rows 321 35 44 104 148 32 64 128 256), losses := [] }

theorem u18550 : Upper (D 8) (R 8) [320,33,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18551 : Route 9 := (fun mask => (mask,id))

def c18551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18551 : Upper (D 8) (R 8) [320,33,40,129,66] 13 := by
  apply FastRouting.sound _ _ [320,33,40,129,66] 13 (by decide) (choices 1) [4,16,128] r18551 c18551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6850
  · exact u6851
  · exact u6852

def r18552 : Route 9 := (fun mask => (mask,id))

def c18552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18552 : Upper (D 8) (R 8) [320,33,40,129,68] 13 := by
  apply FastRouting.sound _ _ [320,33,40,129,68] 13 (by decide) (choices 1) [2,16,128] r18552 c18552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6853
  · exact u6854
  · exact u6855

def r18553 : Route 9 := (fun mask => (mask,id))

def c18553 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18553 : Upper (D 8) (R 8) [320,33,40,129,96] 13 := by
  apply FastRouting.sound _ _ [320,33,40,129,96] 13 (by decide) (choices 1) [2,4,16,128] r18553 c18553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6856
  · exact u6857
  · exact u6858
  · exact u6859

def r18554 : Route 9 := (fun mask => (mask,id))

def c18554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18554 : Upper (D 8) (R 8) [320,33,40,129,130] 13 := by
  apply FastRouting.sound _ _ [320,33,40,129,130] 13 (by decide) (choices 1) [4,16,64] r18554 c18554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6860
  · exact u6861
  · exact u6862

def b18555 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 137 148 114 114 242 370), lower := (rows 321 35 44 137 148 32 64 128 256), losses := [] }

theorem u18555 : Upper (D 8) (R 8) [320,33,40,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18556 : Route 9 := (fun mask => (mask,id))

def c18556 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18556 : Upper (D 8) (R 8) [320,33,40,129,160] 13 := by
  apply FastRouting.sound _ _ [320,33,40,129,160] 13 (by decide) (choices 1) [2,4,16,64] r18556 c18556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6863
  · exact u6864
  · exact u6865
  · exact u6866

def r18557 : Route 9 := (fun mask => (mask,id))

def c18557 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18557 : Upper (D 8) (R 8) [320,33,40,129,192] 13 := by
  apply FastRouting.sound _ _ [320,33,40,129,192] 13 (by decide) (choices 1) [2,4,16] r18557 c18557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6867
  · exact u6868
  · exact u6869

def b18558 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 138 81 180 244 180 436), lower := (rows 321 35 44 138 81 32 64 128 256), losses := [] }

theorem u18558 : Upper (D 8) (R 8) [320,33,40,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18559 : Route 9 := (fun mask => (mask,id))

def c18559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18559 : Upper (D 8) (R 8) [320,33,40,130,68] 13 := by
  apply FastRouting.sound _ _ [320,33,40,130,68] 13 (by decide) (choices 1) [1,16,128] r18559 c18559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6870
  · exact u6871
  · exact u6872

def r18560 : Route 9 := (fun mask => (mask,id))

def c18560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18560 : Upper (D 8) (R 8) [320,33,40,130,96] 13 := by
  apply FastRouting.sound _ _ [320,33,40,130,96] 13 (by decide) (choices 1) [1,4,16,128] r18560 c18560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6873
  · exact u6874
  · exact u6875
  · exact u6876

def r18561 : Route 9 := (fun mask => (mask,id))

def c18561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18561 : Upper (D 8) (R 8) [320,33,40,130,129] 13 := by
  apply FastRouting.sound _ _ [320,33,40,130,129] 13 (by decide) (choices 1) [4,16,64] r18561 c18561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6877
  · exact u6878
  · exact u6879

def b18562 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 138 148 113 113 241 369), lower := (rows 321 35 44 138 148 32 64 128 256), losses := [] }

theorem u18562 : Upper (D 8) (R 8) [320,33,40,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18563 : Route 9 := (fun mask => (mask,id))

def c18563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18563 : Upper (D 8) (R 8) [320,33,40,130,160] 13 := by
  apply FastRouting.sound _ _ [320,33,40,130,160] 13 (by decide) (choices 1) [1,4,16,64] r18563 c18563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6880
  · exact u6881
  · exact u6882
  · exact u6883

def r18564 : Route 9 := (fun mask => (mask,id))

def c18564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18564 : Upper (D 8) (R 8) [320,33,40,130,192] 13 := by
  apply FastRouting.sound _ _ [320,33,40,130,192] 13 (by decide) (choices 1) [1,4,16] r18564 c18564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6884
  · exact u6885
  · exact u6886

def b18565 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 140 81 178 242 178 434), lower := (rows 321 35 44 140 81 32 64 128 256), losses := [] }

theorem u18565 : Upper (D 8) (R 8) [320,33,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18566 : Route 9 := (fun mask => (mask,id))

def c18566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18566 : Upper (D 8) (R 8) [320,33,40,132,66] 13 := by
  apply FastRouting.sound _ _ [320,33,40,132,66] 13 (by decide) (choices 1) [1,16,128] r18566 c18566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6887
  · exact u6888
  · exact u6889

def r18567 : Route 9 := (fun mask => (mask,id))

def c18567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18567 : Upper (D 8) (R 8) [320,33,40,132,96] 13 := by
  apply FastRouting.sound _ _ [320,33,40,132,96] 13 (by decide) (choices 1) [1,2,16,128] r18567 c18567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6890
  · exact u6891
  · exact u6892
  · exact u6893

def b18568 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 140 145 114 114 242 370), lower := (rows 321 35 44 140 145 32 64 128 256), losses := [] }

theorem u18568 : Upper (D 8) (R 8) [320,33,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18569 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 140 146 113 113 241 369), lower := (rows 321 35 44 140 146 32 64 128 256), losses := [] }

theorem u18569 : Upper (D 8) (R 8) [320,33,40,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18570 : PairBound 9 := { available := 83, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 140 176 115 83 211 339), lower := (rows 321 35 44 140 176 32 64 128 256), losses := [] }

theorem u18570 : Upper (D 8) (R 8) [320,33,40,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18571 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 140 208 51 115 179 307), lower := (rows 321 35 44 140 208 32 64 128 256), losses := [] }

theorem u18571 : Upper (D 8) (R 8) [320,33,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18572 : PairBound 9 := { available := 166, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 152 81 166 230 166 422), lower := (rows 321 35 44 152 81 32 64 128 256), losses := [] }

theorem u18572 : Upper (D 8) (R 8) [320,33,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18573 : Route 9 := (fun mask => (mask,id))

def c18573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18573 : Upper (D 8) (R 8) [320,33,40,144,66] 13 := by
  apply FastRouting.sound _ _ [320,33,40,144,66] 13 (by decide) (choices 1) [1,4,128] r18573 c18573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6894
  · exact u6895
  · exact u6896

def b18574 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 152 84 163 227 163 419), lower := (rows 321 35 44 152 84 32 64 128 256), losses := [] }

theorem u18574 : Upper (D 8) (R 8) [320,33,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18575 : Route 9 := (fun mask => (mask,id))

def c18575 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18575 : Upper (D 8) (R 8) [320,33,40,144,96] 13 := by
  apply FastRouting.sound _ _ [320,33,40,144,96] 13 (by decide) (choices 1) [1,2,4,128] r18575 c18575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6897
  · exact u6898
  · exact u6899
  · exact u6900

def b18576 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 152 145 102 102 230 358), lower := (rows 321 35 44 152 145 32 64 128 256), losses := [] }

theorem u18576 : Upper (D 8) (R 8) [320,33,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18577 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 152 146 101 101 229 357), lower := (rows 321 35 44 152 146 32 64 128 256), losses := [] }

theorem u18577 : Upper (D 8) (R 8) [320,33,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18578 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 152 148 99 99 227 355), lower := (rows 321 35 44 152 148 32 64 128 256), losses := [] }

theorem u18578 : Upper (D 8) (R 8) [320,33,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18579 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 152 176 103 71 199 327), lower := (rows 321 35 44 152 176 32 64 128 256), losses := [] }

theorem u18579 : Upper (D 8) (R 8) [320,33,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18580 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 152 208 39 103 167 295), lower := (rows 321 35 44 152 208 32 64 128 256), losses := [] }

theorem u18580 : Upper (D 8) (R 8) [320,33,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18581 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 168 82 181 213 149 405), lower := (rows 321 35 44 168 82 32 64 128 256), losses := [] }

theorem u18581 : Upper (D 8) (R 8) [320,33,40,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18582 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 168 84 179 211 147 403), lower := (rows 321 35 44 168 84 32 64 128 256), losses := [] }

theorem u18582 : Upper (D 8) (R 8) [320,33,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18583 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 168 145 118 86 214 342), lower := (rows 321 35 44 168 145 32 64 128 256), losses := [] }

theorem u18583 : Upper (D 8) (R 8) [320,33,40,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18584 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 168 146 117 85 213 341), lower := (rows 321 35 44 168 146 32 64 128 256), losses := [] }

theorem u18584 : Upper (D 8) (R 8) [320,33,40,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18585 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 168 148 115 83 211 339), lower := (rows 321 35 44 168 148 32 64 128 256), losses := [] }

theorem u18585 : Upper (D 8) (R 8) [320,33,40,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18586 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 168 208 55 87 151 279), lower := (rows 321 35 44 168 208 32 64 128 256), losses := [] }

theorem u18586 : Upper (D 8) (R 8) [320,33,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18587 : Route 9 := (fun mask => (mask,id))

def c18587 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18587 : Upper (D 8) (R 8) [320,33,40,192,129] 13 := by
  apply FastRouting.sound _ _ [320,33,40,192,129] 13 (by decide) (choices 1) [2,4,16] r18587 c18587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6901
  · exact u6902
  · exact u6903

def r18588 : Route 9 := (fun mask => (mask,id))

def c18588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18588 : Upper (D 8) (R 8) [320,33,40,192,130] 13 := by
  apply FastRouting.sound _ _ [320,33,40,192,130] 13 (by decide) (choices 1) [1,4,16] r18588 c18588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6904
  · exact u6905
  · exact u6906

def b18589 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 35 44 200 148 51 115 179 307), lower := (rows 321 35 44 200 148 32 64 128 256), losses := [] }

theorem u18589 : Upper (D 8) (R 8) [320,33,40,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18590 : Route 9 := (fun mask => (mask,id))

def c18590 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18590 : Upper (D 8) (R 8) [320,33,40,192,160] 13 := by
  apply FastRouting.sound _ _ [320,33,40,192,160] 13 (by decide) (choices 1) [1,2,4,16] r18590 c18590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6907
  · exact u6908
  · exact u6909
  · exact u6910

def b18591 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 69 138 148 56 120 184 312), lower := (rows 321 35 69 138 148 32 64 128 256), losses := [] }

theorem u18591 : Upper (D 8) (R 8) [320,33,65,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18592 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 69 138 176 60 124 188 316), lower := (rows 321 35 69 138 176 32 64 128 256), losses := [] }

theorem u18592 : Upper (D 8) (R 8) [320,33,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18593 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 69 140 176 58 122 186 314), lower := (rows 321 35 69 140 176 32 64 128 256), losses := [] }

theorem u18593 : Upper (D 8) (R 8) [320,33,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18594 : Route 9 := (fun mask => (mask,id))

def c18594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18594 : Upper (D 8) (R 8) [320,33,66,129,132] 13 := by
  apply FastRouting.sound _ _ [320,33,66,129,132] 13 (by decide) (choices 1) [8,16] r18594 c18594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6911
  · exact u6912

def b18595 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 35 70 137 152 52 116 180 308), lower := (rows 321 35 70 137 152 32 64 128 256), losses := [] }

theorem u18595 : Upper (D 8) (R 8) [320,33,66,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18596 : Route 9 := (fun mask => (mask,id))

def c18596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18596 : Upper (D 8) (R 8) [320,33,66,129,160] 13 := by
  apply FastRouting.sound _ _ [320,33,66,129,160] 13 (by decide) (choices 1) [4,8,16] r18596 c18596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6913
  · exact u6914
  · exact u6915

def b18597 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 35 70 140 152 49 113 177 305), lower := (rows 321 35 70 140 152 32 64 128 256), losses := [] }

theorem u18597 : Upper (D 8) (R 8) [320,33,66,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18598 : Route 9 := (fun mask => (mask,id))

def c18598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18598 : Upper (D 8) (R 8) [320,33,66,132,160] 13 := by
  apply FastRouting.sound _ _ [320,33,66,132,160] 13 (by decide) (choices 1) [1,8,16] r18598 c18598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6916
  · exact u6917
  · exact u6918

def b18599 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 321 35 70 152 152 37 101 165 293), lower := (rows 321 35 70 152 152 32 64 128 256), losses := [] }

theorem u18599 : Upper (D 8) (R 8) [320,33,66,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18599
end Delivery.IrregularNine14.P08
