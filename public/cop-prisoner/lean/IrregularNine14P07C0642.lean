import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0430
import IrregularNine14P07C0431
import IrregularNine14P07C0432

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38520 : Route 9 := (fun mask => (mask,id))

def c38520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38520 : Upper (D 7) (R 7) [36,257,66,34,65] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,65] 13 (by decide) (choices 1) [8,16,128] r38520 c38520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25847
  · exact u25848
  · exact u25849

def r38521 : Route 9 := (fun mask => (mask,id))

def c38521 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38521 : Upper (D 7) (R 7) [36,257,66,34,72] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,72] 13 (by decide) (choices 1) [1,16,128] r38521 c38521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25850
  · exact u25851
  · exact u25852

def r38522 : Route 9 := (fun mask => (mask,id))

def c38522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u38522 : Upper (D 7) (R 7) [36,257,66,34,129] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,129] 13 (by decide) (choices 1) [8,16,64,128] r38522 c38522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25853
  · exact u25854
  · exact u25855
  · exact u25856

def r38523 : Route 9 := (fun mask => (mask,id))

def c38523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38523 : Upper (D 7) (R 7) [36,257,66,34,136] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,136] 13 (by decide) (choices 1) [1,16,64,128] r38523 c38523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25857
  · exact u25858
  · exact u25859
  · exact u25860

def r38524 : Route 9 := (fun mask => (mask,id))

def c38524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38524 : Upper (D 7) (R 7) [36,257,66,34,192] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,192] 13 (by decide) (choices 1) [1,8,16,128] r38524 c38524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25861
  · exact u25862
  · exact u25863
  · exact u25864

def r38525 : Route 9 := (fun mask => (mask,id))

def c38525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38525 : Upper (D 7) (R 7) [36,257,66,48,65] 13 := by
  apply FastRouting.sound _ _ [36,257,66,48,65] 13 (by decide) (choices 1) [2,8,128] r38525 c38525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25865
  · exact u25866
  · exact u25867

def b38526 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 37 259 70 56 82 169 201 137 393), lower := (rows 37 259 70 56 82 32 64 128 256), losses := [] }

theorem u38526 : Upper (D 7) (R 7) [36,257,66,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38527 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(2,5)], upper := (rows 37 259 70 56 88 163 195 131 387), lower := (rows 37 259 70 56 88 32 64 128 256), losses := [] }

theorem u38527 : Upper (D 7) (R 7) [36,257,66,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38528 : Route 9 := (fun mask => (mask,id))

def c38528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38528 : Upper (D 7) (R 7) [36,257,66,48,129] 13 := by
  apply FastRouting.sound _ _ [36,257,66,48,129] 13 (by decide) (choices 1) [2,8,64,128] r38528 c38528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25868
  · exact u25869
  · exact u25870
  · exact u25871

def r38529 : Route 9 := (fun mask => (mask,id))

def c38529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38529 : Upper (D 7) (R 7) [36,257,66,48,130] 13 := by
  apply FastRouting.sound _ _ [36,257,66,48,130] 13 (by decide) (choices 1) [1,8,64,128] r38529 c38529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25872
  · exact u25873
  · exact u25874
  · exact u25875

def r38530 : Route 9 := (fun mask => (mask,id))

def c38530 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38530 : Upper (D 7) (R 7) [36,257,66,48,136] 13 := by
  apply FastRouting.sound _ _ [36,257,66,48,136] 13 (by decide) (choices 1) [1,2,64,128] r38530 c38530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25876
  · exact u25877
  · exact u25878
  · exact u25879

def r38531 : Route 9 := (fun mask => (mask,id))

def c38531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38531 : Upper (D 7) (R 7) [36,257,66,48,192] 13 := by
  apply FastRouting.sound _ _ [36,257,66,48,192] 13 (by decide) (choices 1) [1,2,8,128] r38531 c38531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25880
  · exact u25881
  · exact u25882
  · exact u25883

def r38532 : Route 9 := (fun mask => (mask,id))

def c38532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38532 : Upper (D 7) (R 7) [36,257,66,65,130] 13 := by
  apply FastRouting.sound _ _ [36,257,66,65,130] 13 (by decide) (choices 1) [8,16,128] r38532 c38532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25884
  · exact u25885
  · exact u25886

def r38533 : Route 9 := (fun mask => (mask,id))

def c38533 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38533 : Upper (D 7) (R 7) [36,257,66,65,136] 13 := by
  apply FastRouting.sound _ _ [36,257,66,65,136] 13 (by decide) (choices 1) [2,16,128] r38533 c38533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25887
  · exact u25888
  · exact u25889

def r38534 : Route 9 := (fun mask => (mask,id))

def c38534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38534 : Upper (D 7) (R 7) [36,257,66,65,160] 13 := by
  apply FastRouting.sound _ _ [36,257,66,65,160] 13 (by decide) (choices 1) [2,8,16,128] r38534 c38534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25890
  · exact u25891
  · exact u25892
  · exact u25893

def b38535 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 161 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,7)], upper := (rows 37 259 70 74 145 184 248 184 440), lower := (rows 37 259 70 74 145 32 64 128 256), losses := [] }

theorem u38535 : Upper (D 7) (R 7) [36,257,66,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38536 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 161 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,7)], upper := (rows 37 259 70 74 152 177 241 177 433), lower := (rows 37 259 70 74 152 32 64 128 256), losses := [] }

theorem u38536 : Upper (D 7) (R 7) [36,257,66,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38537 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 161 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,7)], upper := (rows 37 259 70 74 176 185 217 153 409), lower := (rows 37 259 70 74 176 32 64 128 256), losses := [] }

theorem u38537 : Upper (D 7) (R 7) [36,257,66,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38538 : Route 9 := (fun mask => (mask,id))

def c38538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38538 : Upper (D 7) (R 7) [36,257,66,80,129] 13 := by
  apply FastRouting.sound _ _ [36,257,66,80,129] 13 (by decide) (choices 1) [2,8,128] r38538 c38538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25894
  · exact u25895
  · exact u25896

def r38539 : Route 9 := (fun mask => (mask,id))

def c38539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38539 : Upper (D 7) (R 7) [36,257,66,80,130] 13 := by
  apply FastRouting.sound _ _ [36,257,66,80,130] 13 (by decide) (choices 1) [1,8,128] r38539 c38539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25897
  · exact u25898
  · exact u25899

def r38540 : Route 9 := (fun mask => (mask,id))

def c38540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38540 : Upper (D 7) (R 7) [36,257,66,80,136] 13 := by
  apply FastRouting.sound _ _ [36,257,66,80,136] 13 (by decide) (choices 1) [1,2,128] r38540 c38540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25900
  · exact u25901
  · exact u25902

def r38541 : Route 9 := (fun mask => (mask,id))

def c38541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38541 : Upper (D 7) (R 7) [36,257,66,80,160] 13 := by
  apply FastRouting.sound _ _ [36,257,66,80,160] 13 (by decide) (choices 1) [1,2,8,128] r38541 c38541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25903
  · exact u25904
  · exact u25905
  · exact u25906

def r38542 : Route 9 := (fun mask => (mask,id))

def c38542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38542 : Upper (D 7) (R 7) [36,257,66,96,129] 13 := by
  apply FastRouting.sound _ _ [36,257,66,96,129] 13 (by decide) (choices 1) [2,8,16,128] r38542 c38542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25907
  · exact u25908
  · exact u25909
  · exact u25910

def r38543 : Route 9 := (fun mask => (mask,id))

def c38543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38543 : Upper (D 7) (R 7) [36,257,66,96,130] 13 := by
  apply FastRouting.sound _ _ [36,257,66,96,130] 13 (by decide) (choices 1) [1,8,16,128] r38543 c38543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25911
  · exact u25912
  · exact u25913
  · exact u25914

def r38544 : Route 9 := (fun mask => (mask,id))

def c38544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38544 : Upper (D 7) (R 7) [36,257,66,96,136] 13 := by
  apply FastRouting.sound _ _ [36,257,66,96,136] 13 (by decide) (choices 1) [1,2,16,128] r38544 c38544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25915
  · exact u25916
  · exact u25917
  · exact u25918

def r38545 : Route 9 := (fun mask => (mask,id))

def c38545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38545 : Upper (D 7) (R 7) [36,257,66,129,130] 13 := by
  apply FastRouting.sound _ _ [36,257,66,129,130] 13 (by decide) (choices 1) [8,16,64] r38545 c38545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25919
  · exact u25920
  · exact u25921

def b38546 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 259 70 137 152 114 114 242 370), lower := (rows 37 259 70 137 152 32 64 128 256), losses := [] }

theorem u38546 : Upper (D 7) (R 7) [36,257,66,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38547 : Route 9 := (fun mask => (mask,id))

def c38547 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38547 : Upper (D 7) (R 7) [36,257,66,129,160] 13 := by
  apply FastRouting.sound _ _ [36,257,66,129,160] 13 (by decide) (choices 1) [2,8,16,64] r38547 c38547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25922
  · exact u25923
  · exact u25924
  · exact u25925

def r38548 : Route 9 := (fun mask => (mask,id))

def c38548 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38548 : Upper (D 7) (R 7) [36,257,66,129,192] 13 := by
  apply FastRouting.sound _ _ [36,257,66,129,192] 13 (by decide) (choices 1) [2,8,16] r38548 c38548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25926
  · exact u25927
  · exact u25928

def b38549 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 259 70 138 152 113 113 241 369), lower := (rows 37 259 70 138 152 32 64 128 256), losses := [] }

theorem u38549 : Upper (D 7) (R 7) [36,257,66,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38550 : Route 9 := (fun mask => (mask,id))

def c38550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38550 : Upper (D 7) (R 7) [36,257,66,130,160] 13 := by
  apply FastRouting.sound _ _ [36,257,66,130,160] 13 (by decide) (choices 1) [1,8,16,64] r38550 c38550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25929
  · exact u25930
  · exact u25931
  · exact u25932

def r38551 : Route 9 := (fun mask => (mask,id))

def c38551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38551 : Upper (D 7) (R 7) [36,257,66,130,192] 13 := by
  apply FastRouting.sound _ _ [36,257,66,130,192] 13 (by decide) (choices 1) [1,8,16] r38551 c38551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25933
  · exact u25934
  · exact u25935

def b38552 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 259 70 152 152 99 99 227 355), lower := (rows 37 259 70 152 152 32 64 128 256), losses := [] }

theorem u38552 : Upper (D 7) (R 7) [36,257,66,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38553 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 259 70 152 176 107 75 203 331), lower := (rows 37 259 70 152 176 32 64 128 256), losses := [] }

theorem u38553 : Upper (D 7) (R 7) [36,257,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38554 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 259 70 152 208 43 107 171 299), lower := (rows 37 259 70 152 208 32 64 128 256), losses := [] }

theorem u38554 : Upper (D 7) (R 7) [36,257,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38555 : Route 9 := (fun mask => (mask,id))

def c38555 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38555 : Upper (D 7) (R 7) [36,257,66,160,192] 13 := by
  apply FastRouting.sound _ _ [36,257,66,160,192] 13 (by decide) (choices 1) [1,2,8,16] r38555 c38555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25936
  · exact u25937
  · exact u25938
  · exact u25939

def b38556 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 240, targets := 1 }], pairs := [(1,5),(2,0),(2,5),(4,0)], upper := (rows 37 259 76 25 50 226 194 194 450), lower := (rows 37 259 76 25 50 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 50 82 146 274), good := (rows 36 498 76 508 498 32 64 128 256) }] }

theorem u38556 : Upper (D 7) (R 7) [36,257,72,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38557 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 37 259 76 25 82 162 226 162 418), lower := (rows 37 259 76 25 82 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 50 82 146 274), good := (rows 36 498 76 508 498 32 64 128 256) }] }

theorem u38557 : Upper (D 7) (R 7) [36,257,72,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38558 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 76 25 112 162 194 130 386), lower := (rows 37 259 76 25 112 32 64 128 256), losses := [] }

theorem u38558 : Upper (D 7) (R 7) [36,257,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38559 : Route 9 := (fun mask => (mask,id))

def c38559 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38559 : Upper (D 7) (R 7) [36,257,72,17,130] 13 := by
  apply FastRouting.sound _ _ [36,257,72,17,130] 13 (by decide) (choices 1) [2,64,128] r38559 c38559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25940
  · exact u25941
  · exact u25942

def r38560 : Route 9 := (fun mask => (mask,id))

def c38560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38560 : Upper (D 7) (R 7) [36,257,72,17,160] 13 := by
  apply FastRouting.sound _ _ [36,257,72,17,160] 13 (by decide) (choices 1) [2,64,128] r38560 c38560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25943
  · exact u25944
  · exact u25945

def r38561 : Route 9 := (fun mask => (mask,id))

def c38561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38561 : Upper (D 7) (R 7) [36,257,72,17,192] 13 := by
  apply FastRouting.sound _ _ [36,257,72,17,192] 13 (by decide) (choices 1) [2,128] r38561 c38561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25946
  · exact u25947

def b38562 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 37 259 76 26 19 224 224 224 480), lower := (rows 37 259 76 26 19 32 64 128 256), losses := [] }

theorem u38562 : Upper (D 7) (R 7) [36,257,72,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38563 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 259 76 26 49 226 194 194 450), lower := (rows 37 259 76 26 49 32 64 128 256), losses := [] }

theorem u38563 : Upper (D 7) (R 7) [36,257,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38564 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 76 26 50 225 193 193 449), lower := (rows 37 259 76 26 50 32 64 128 256), losses := [] }

theorem u38564 : Upper (D 7) (R 7) [36,257,72,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38565 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 228, targets := 1 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 37 259 76 26 81 162 226 162 418), lower := (rows 37 259 76 26 81 32 64 128 256), losses := [] }

theorem u38565 : Upper (D 7) (R 7) [36,257,72,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38566 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 37 259 76 26 82 161 225 161 417), lower := (rows 37 259 76 26 82 32 64 128 256), losses := [] }

theorem u38566 : Upper (D 7) (R 7) [36,257,72,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38567 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,6),(1,5),(1,6),(2,5)], upper := (rows 37 259 76 26 112 163 195 131 387), lower := (rows 37 259 76 26 112 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 12 8 16 0 67 131 259), good := (rows 455 451 76 478 80 0 64 128 256) }] }

theorem u38567 : Upper (D 7) (R 7) [36,257,72,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38568 : Route 9 := (fun mask => (mask,id))

def c38568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38568 : Upper (D 7) (R 7) [36,257,72,18,129] 13 := by
  apply FastRouting.sound _ _ [36,257,72,18,129] 13 (by decide) (choices 1) [2,64,128] r38568 c38568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25948
  · exact u25949
  · exact u25950

def b38569 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 76 26 146 225 225 225 481), lower := (rows 37 259 76 26 146 32 64 128 256), losses := [] }

theorem u38569 : Upper (D 7) (R 7) [36,257,72,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38570 : Route 9 := (fun mask => (mask,id))

def c38570 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38570 : Upper (D 7) (R 7) [36,257,72,18,160] 13 := by
  apply FastRouting.sound _ _ [36,257,72,18,160] 13 (by decide) (choices 1) [1,2,64,128] r38570 c38570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25951
  · exact u25952
  · exact u25953
  · exact u25954

def r38571 : Route 9 := (fun mask => (mask,id))

def c38571 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38571 : Upper (D 7) (R 7) [36,257,72,18,192] 13 := by
  apply FastRouting.sound _ _ [36,257,72,18,192] 13 (by decide) (choices 1) [1,2,128] r38571 c38571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25955
  · exact u25956
  · exact u25957

def b38572 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 37 259 76 42 19 240 208 208 464), lower := (rows 37 259 76 42 19 32 64 128 256), losses := [] }

theorem u38572 : Upper (D 7) (R 7) [36,257,72,34,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38573 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,5),(1,6),(3,6),(4,5)], upper := (rows 37 259 76 42 81 178 210 146 402), lower := (rows 37 259 76 42 81 32 64 128 256), losses := [] }

theorem u38573 : Upper (D 7) (R 7) [36,257,72,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38574 : Route 9 := (fun mask => (mask,id))

def c38574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38574 : Upper (D 7) (R 7) [36,257,72,34,66] 13 := by
  apply FastRouting.sound _ _ [36,257,72,34,66] 13 (by decide) (choices 1) [1,16,128] r38574 c38574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25958
  · exact u25959
  · exact u25960

def r38575 : Route 9 := (fun mask => (mask,id))

def c38575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38575 : Upper (D 7) (R 7) [36,257,72,34,129] 13 := by
  apply FastRouting.sound _ _ [36,257,72,34,129] 13 (by decide) (choices 1) [2,16,64,128] r38575 c38575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25961
  · exact u25962
  · exact u25963
  · exact u25964

def r38576 : Route 9 := (fun mask => (mask,id))

def c38576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38576 : Upper (D 7) (R 7) [36,257,72,34,130] 13 := by
  apply FastRouting.sound _ _ [36,257,72,34,130] 13 (by decide) (choices 1) [1,16,64,128] r38576 c38576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25965
  · exact u25966
  · exact u25967
  · exact u25968

def r38577 : Route 9 := (fun mask => (mask,id))

def c38577 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38577 : Upper (D 7) (R 7) [36,257,72,34,192] 13 := by
  apply FastRouting.sound _ _ [36,257,72,34,192] 13 (by decide) (choices 1) [1,2,16,128] r38577 c38577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25969
  · exact u25970
  · exact u25971
  · exact u25972

def b38578 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 37 259 76 56 19 226 194 194 450), lower := (rows 37 259 76 56 19 32 64 128 256), losses := [] }

theorem u38578 : Upper (D 7) (R 7) [36,257,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38579 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(4,5)], upper := (rows 37 259 76 56 81 162 194 130 386), lower := (rows 37 259 76 56 81 32 64 128 256), losses := [] }

theorem u38579 : Upper (D 7) (R 7) [36,257,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u38579
end Delivery.IrregularNine14.P07
