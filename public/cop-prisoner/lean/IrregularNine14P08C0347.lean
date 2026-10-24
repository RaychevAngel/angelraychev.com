import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0208
import IrregularNine14P08C0209
import IrregularNine14P08C0210
import IrregularNine14P08C0211

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20820 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 504 504 504 504 504), lower := (rows 97 7 7 168 16 32 64 128 256), losses := [] }

theorem u20820 : Upper (D 8) (R 8) [96,5,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20821 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 200 440 440 504 440 440), lower := (rows 97 7 7 200 16 32 64 128 256), losses := [] }

theorem u20821 : Upper (D 8) (R 8) [96,5,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20822 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 296 248 248 248 248 504), lower := (rows 97 7 7 296 16 32 64 128 256), losses := [] }

theorem u20822 : Upper (D 8) (R 8) [96,5,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20823 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 328 184 184 248 184 440), lower := (rows 97 7 7 328 16 32 64 128 256), losses := [] }

theorem u20823 : Upper (D 8) (R 8) [96,5,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20824 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 392 248 248 248 248 504), lower := (rows 97 7 7 392 16 32 64 128 256), losses := [] }

theorem u20824 : Upper (D 8) (R 8) [96,5,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20825 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 26 496 480 480 480 480), lower := (rows 97 7 13 26 16 32 64 128 256), losses := [] }

theorem u20825 : Upper (D 8) (R 8) [96,5,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20826 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 496 496 496 496 496), lower := (rows 97 7 13 42 16 32 64 128 256), losses := [] }

theorem u20826 : Upper (D 8) (R 8) [96,5,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20827 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 74 432 432 496 432 432), lower := (rows 97 7 13 74 16 32 64 128 256), losses := [] }

theorem u20827 : Upper (D 8) (R 8) [96,5,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20828 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 496 496 496 496 496), lower := (rows 97 7 13 138 16 32 64 128 256), losses := [] }

theorem u20828 : Upper (D 8) (R 8) [96,5,9,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20829 : PairBound 9 := { available := 498, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 498 498 498 498 498), lower := (rows 97 7 13 168 16 32 64 128 256), losses := [] }

theorem u20829 : Upper (D 8) (R 8) [96,5,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20830 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 200 434 434 498 434 434), lower := (rows 97 7 13 200 16 32 64 128 256), losses := [] }

theorem u20830 : Upper (D 8) (R 8) [96,5,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20831 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 266 240 240 240 240 496), lower := (rows 97 7 13 266 16 32 64 128 256), losses := [] }

theorem u20831 : Upper (D 8) (R 8) [96,5,9,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20832 : PairBound 9 := { available := 242, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 242 242 242 242 498), lower := (rows 97 7 13 296 16 32 64 128 256), losses := [] }

theorem u20832 : Upper (D 8) (R 8) [96,5,9,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20833 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 328 178 178 242 178 434), lower := (rows 97 7 13 328 16 32 64 128 256), losses := [] }

theorem u20833 : Upper (D 8) (R 8) [96,5,9,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20834 : PairBound 9 := { available := 242, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 242 242 242 242 498), lower := (rows 97 7 13 392 16 32 64 128 256), losses := [] }

theorem u20834 : Upper (D 8) (R 8) [96,5,9,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20835 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 496 480 480 480 480), lower := (rows 97 7 14 25 16 32 64 128 256), losses := [] }

theorem u20835 : Upper (D 8) (R 8) [96,5,10,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20836 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 496 496 496 496 496), lower := (rows 97 7 14 41 16 32 64 128 256), losses := [] }

theorem u20836 : Upper (D 8) (R 8) [96,5,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20837 : Route 9 := (fun mask => (mask,id))

def c20837 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20837 : Upper (D 8) (R 8) [96,5,10,48] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20837 c20837
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12586
  · exact u12587
  · exact u12588
  · exact u12589
  · exact u12590
  · exact u12591
  · exact u12592
  · exact u12593
  · exact u12594
  · exact u12595

def b20838 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 73 432 432 496 432 432), lower := (rows 97 7 14 73 16 32 64 128 256), losses := [] }

theorem u20838 : Upper (D 8) (R 8) [96,5,10,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20839 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 88 433 417 481 417 417), lower := (rows 97 7 14 88 16 32 64 128 256), losses := [] }

theorem u20839 : Upper (D 8) (R 8) [96,5,10,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20840 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 104 433 433 497 433 433), lower := (rows 97 7 14 104 16 32 64 128 256), losses := [] }

theorem u20840 : Upper (D 8) (R 8) [96,5,10,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20841 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 496 496 496 496 496), lower := (rows 97 7 14 137 16 32 64 128 256), losses := [] }

theorem u20841 : Upper (D 8) (R 8) [96,5,10,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20842 : Route 9 := (fun mask => (mask,id))

def c20842 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20842 : Upper (D 8) (R 8) [96,5,10,144] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20842 c20842
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12612
  · exact u12613
  · exact u12614
  · exact u12615
  · exact u12616
  · exact u12617
  · exact u12618
  · exact u12619
  · exact u12620
  · exact u12621

def r20843 : Route 9 := (fun mask => (mask,id))

def c20843 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20843 : Upper (D 8) (R 8) [96,5,10,160] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20843 c20843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12622
  · exact u12623
  · exact u12624
  · exact u12625
  · exact u12626
  · exact u12627
  · exact u12628
  · exact u12629
  · exact u12630
  · exact u12631

def b20844 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 200 433 433 497 433 433), lower := (rows 97 7 14 200 16 32 64 128 256), losses := [] }

theorem u20844 : Upper (D 8) (R 8) [96,5,10,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20845 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 265 240 240 240 240 496), lower := (rows 97 7 14 265 16 32 64 128 256), losses := [] }

theorem u20845 : Upper (D 8) (R 8) [96,5,10,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20846 : Route 9 := (fun mask => (mask,id))

def c20846 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20846 : Upper (D 8) (R 8) [96,5,10,272] 13 := by
  apply FastRouting.sound _ _ [96,5,10,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20846 c20846
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12639
  · exact u12640
  · exact u12641
  · exact u12642
  · exact u12643
  · exact u12644

def r20847 : Route 9 := (fun mask => (mask,id))

def c20847 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20847 : Upper (D 8) (R 8) [96,5,10,288] 13 := by
  apply FastRouting.sound _ _ [96,5,10,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20847 c20847
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12645
  · exact u12646
  · exact u12647
  · exact u12648
  · exact u12649
  · exact u12650

def b20848 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 328 177 177 241 177 433), lower := (rows 97 7 14 328 16 32 64 128 256), losses := [] }

theorem u20848 : Upper (D 8) (R 8) [96,5,10,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r20849 : Route 9 := (fun mask => (mask,id))

def c20849 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20849 : Upper (D 8) (R 8) [96,5,10,384] 13 := by
  apply FastRouting.sound _ _ [96,5,10,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20849 c20849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u12653
  · exact u12654
  · exact u12655
  · exact u12656
  · exact u12657
  · exact u12658

def b20850 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 42 504 488 488 488 488), lower := (rows 97 7 21 42 16 32 64 128 256), losses := [] }

theorem u20850 : Upper (D 8) (R 8) [96,5,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20851 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 74 440 424 488 424 424), lower := (rows 97 7 21 74 16 32 64 128 256), losses := [] }

theorem u20851 : Upper (D 8) (R 8) [96,5,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20852 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 138 504 488 488 488 488), lower := (rows 97 7 21 138 16 32 64 128 256), losses := [] }

theorem u20852 : Upper (D 8) (R 8) [96,5,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20853 : PairBound 9 := { available := 490, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 168 506 490 490 490 490), lower := (rows 97 7 21 168 16 32 64 128 256), losses := [] }

theorem u20853 : Upper (D 8) (R 8) [96,5,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20854 : PairBound 9 := { available := 426, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 200 442 426 490 426 426), lower := (rows 97 7 21 200 16 32 64 128 256), losses := [] }

theorem u20854 : Upper (D 8) (R 8) [96,5,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20855 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 266 248 232 232 232 488), lower := (rows 97 7 21 266 16 32 64 128 256), losses := [] }

theorem u20855 : Upper (D 8) (R 8) [96,5,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20856 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 296 250 234 234 234 490), lower := (rows 97 7 21 296 16 32 64 128 256), losses := [] }

theorem u20856 : Upper (D 8) (R 8) [96,5,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20857 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 328 186 170 234 170 426), lower := (rows 97 7 21 328 16 32 64 128 256), losses := [] }

theorem u20857 : Upper (D 8) (R 8) [96,5,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20858 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 392 250 234 234 234 490), lower := (rows 97 7 21 392 16 32 64 128 256), losses := [] }

theorem u20858 : Upper (D 8) (R 8) [96,5,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20859 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 368, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 22 137 504 488 488 488 488), lower := (rows 97 7 22 137 16 32 64 128 256), losses := [] }

theorem u20859 : Upper (D 8) (R 8) [96,5,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20860_9 : Upper (D 8) (R 8) [96,5,18,160,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12576

theorem m20860_33 : Upper (D 8) (R 8) [96,5,18,160,33] 13 :=
  permutation_upper _ _ _ [96,5,10,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12581

theorem m20860_40 : Upper (D 8) (R 8) [96,5,18,160,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12590

theorem m20860_65 : Upper (D 8) (R 8) [96,5,18,160,65] 13 :=
  permutation_upper _ _ _ [96,5,10,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12596

theorem m20860_72 : Upper (D 8) (R 8) [96,5,18,160,72] 13 :=
  permutation_upper _ _ _ [96,5,10,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12600

theorem m20860_96 : Upper (D 8) (R 8) [96,5,18,160,96] 13 :=
  permutation_upper _ _ _ [96,5,10,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12604

theorem m20860_129 : Upper (D 8) (R 8) [96,5,18,160,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12607

theorem m20860_136 : Upper (D 8) (R 8) [96,5,18,160,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12616

theorem m20860_160 : Upper (D 8) (R 8) [96,5,18,160,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12626

theorem m20860_192 : Upper (D 8) (R 8) [96,5,18,160,192] 13 :=
  permutation_upper _ _ _ [96,5,10,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12633

theorem m20860_257 : Upper (D 8) (R 8) [96,5,18,160,257] 13 :=
  permutation_upper _ _ _ [96,5,10,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12637

theorem m20860_264 : Upper (D 8) (R 8) [96,5,18,160,264] 13 :=
  permutation_upper _ _ _ [96,5,10,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12643

theorem m20860_288 : Upper (D 8) (R 8) [96,5,18,160,288] 13 :=
  permutation_upper _ _ _ [96,5,10,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12649

theorem m20860_320 : Upper (D 8) (R 8) [96,5,18,160,320] 13 :=
  permutation_upper _ _ _ [96,5,10,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12652

theorem m20860_384 : Upper (D 8) (R 8) [96,5,18,160,384] 13 :=
  permutation_upper _ _ _ [96,5,10,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12657

def r20860 : Route 9 := (fun mask => (mask,id))

def c20860 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u20860 : Upper (D 8) (R 8) [96,5,18,160] 13 := by
  apply FastRouting.sound _ _ [96,5,18,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r20860 c20860
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20860_9
  · exact m20860_33
  · exact m20860_40
  · exact m20860_65
  · exact m20860_72
  · exact m20860_96
  · exact m20860_129
  · exact m20860_136
  · exact m20860_160
  · exact m20860_192
  · exact m20860_257
  · exact m20860_264
  · exact m20860_288
  · exact m20860_320
  · exact m20860_384

theorem m20861_9 : Upper (D 8) (R 8) [96,5,18,192,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12577

theorem m20861_33 : Upper (D 8) (R 8) [96,5,18,192,33] 13 :=
  permutation_upper _ _ _ [96,5,10,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12582

theorem m20861_40 : Upper (D 8) (R 8) [96,5,18,192,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12591

theorem m20861_129 : Upper (D 8) (R 8) [96,5,18,192,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12608

theorem m20861_136 : Upper (D 8) (R 8) [96,5,18,192,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12617

theorem m20861_160 : Upper (D 8) (R 8) [96,5,18,192,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12627

theorem m20861_257 : Upper (D 8) (R 8) [96,5,18,192,257] 13 :=
  permutation_upper _ _ _ [96,5,10,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12638

theorem m20861_264 : Upper (D 8) (R 8) [96,5,18,192,264] 13 :=
  permutation_upper _ _ _ [96,5,10,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12644

theorem m20861_288 : Upper (D 8) (R 8) [96,5,18,192,288] 13 :=
  permutation_upper _ _ _ [96,5,10,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12650

theorem m20861_384 : Upper (D 8) (R 8) [96,5,18,192,384] 13 :=
  permutation_upper _ _ _ [96,5,10,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12658

def r20861 : Route 9 := (fun mask => (mask,id))

def c20861 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u20861 : Upper (D 8) (R 8) [96,5,18,192] 13 := by
  apply FastRouting.sound _ _ [96,5,18,192] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r20861 c20861
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20861_9
  · exact m20861_33
  · exact m20861_40
  · exact m20861_129
  · exact m20861_136
  · exact m20861_160
  · exact m20861_257
  · exact m20861_264
  · exact m20861_288
  · exact m20861_384

def b20862 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 22 265 248 232 232 232 488), lower := (rows 97 7 22 265 16 32 64 128 256), losses := [] }

theorem u20862 : Upper (D 8) (R 8) [96,5,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20863_9 : Upper (D 8) (R 8) [96,5,18,288,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12578

theorem m20863_33 : Upper (D 8) (R 8) [96,5,18,288,33] 13 :=
  permutation_upper _ _ _ [96,5,10,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12583

theorem m20863_40 : Upper (D 8) (R 8) [96,5,18,288,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12593

theorem m20863_65 : Upper (D 8) (R 8) [96,5,18,288,65] 13 :=
  permutation_upper _ _ _ [96,5,10,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12597

theorem m20863_72 : Upper (D 8) (R 8) [96,5,18,288,72] 13 :=
  permutation_upper _ _ _ [96,5,10,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12602

theorem m20863_96 : Upper (D 8) (R 8) [96,5,18,288,96] 13 :=
  permutation_upper _ _ _ [96,5,10,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12605

theorem m20863_129 : Upper (D 8) (R 8) [96,5,18,288,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12609

theorem m20863_136 : Upper (D 8) (R 8) [96,5,18,288,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12619

theorem m20863_160 : Upper (D 8) (R 8) [96,5,18,288,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12629

theorem m20863_192 : Upper (D 8) (R 8) [96,5,18,288,192] 13 :=
  permutation_upper _ _ _ [96,5,10,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12635

def r20863 : Route 9 := (fun mask => (mask,id))

def c20863 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20863 : Upper (D 8) (R 8) [96,5,18,288] 13 := by
  apply FastRouting.sound _ _ [96,5,18,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20863 c20863
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20863_9
  · exact m20863_33
  · exact m20863_40
  · exact m20863_65
  · exact m20863_72
  · exact m20863_96
  · exact m20863_129
  · exact m20863_136
  · exact m20863_160
  · exact m20863_192

theorem m20864_9 : Upper (D 8) (R 8) [96,5,18,320,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12579

theorem m20864_33 : Upper (D 8) (R 8) [96,5,18,320,33] 13 :=
  permutation_upper _ _ _ [96,5,10,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12584

theorem m20864_40 : Upper (D 8) (R 8) [96,5,18,320,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12594

theorem m20864_129 : Upper (D 8) (R 8) [96,5,18,320,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12610

theorem m20864_136 : Upper (D 8) (R 8) [96,5,18,320,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12620

theorem m20864_160 : Upper (D 8) (R 8) [96,5,18,320,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12630

def r20864 : Route 9 := (fun mask => (mask,id))

def c20864 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u20864 : Upper (D 8) (R 8) [96,5,18,320] 13 := by
  apply FastRouting.sound _ _ [96,5,18,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r20864 c20864
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20864_9
  · exact m20864_33
  · exact m20864_40
  · exact m20864_129
  · exact m20864_136
  · exact m20864_160

theorem m20865_9 : Upper (D 8) (R 8) [96,5,18,384,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12580

theorem m20865_33 : Upper (D 8) (R 8) [96,5,18,384,33] 13 :=
  permutation_upper _ _ _ [96,5,10,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12585

theorem m20865_40 : Upper (D 8) (R 8) [96,5,18,384,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12595

theorem m20865_65 : Upper (D 8) (R 8) [96,5,18,384,65] 13 :=
  permutation_upper _ _ _ [96,5,10,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12598

theorem m20865_72 : Upper (D 8) (R 8) [96,5,18,384,72] 13 :=
  permutation_upper _ _ _ [96,5,10,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12603

theorem m20865_96 : Upper (D 8) (R 8) [96,5,18,384,96] 13 :=
  permutation_upper _ _ _ [96,5,10,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12606

theorem m20865_129 : Upper (D 8) (R 8) [96,5,18,384,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12611

theorem m20865_136 : Upper (D 8) (R 8) [96,5,18,384,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12621

theorem m20865_160 : Upper (D 8) (R 8) [96,5,18,384,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12631

theorem m20865_192 : Upper (D 8) (R 8) [96,5,18,384,192] 13 :=
  permutation_upper _ _ _ [96,5,10,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12636

def r20865 : Route 9 := (fun mask => (mask,id))

def c20865 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20865 : Upper (D 8) (R 8) [96,5,18,384] 13 := by
  apply FastRouting.sound _ _ [96,5,18,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r20865 c20865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20865_9
  · exact m20865_33
  · exact m20865_40
  · exact m20865_65
  · exact m20865_72
  · exact m20865_96
  · exact m20865_129
  · exact m20865_136
  · exact m20865_160
  · exact m20865_192

def b20866 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 41 498 482 482 482 482), lower := (rows 97 7 28 41 16 32 64 128 256), losses := [] }

theorem u20866 : Upper (D 8) (R 8) [96,5,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20867_33 : Upper (D 8) (R 8) [96,5,24,34,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12659

def r20867 : Route 9 := (fun mask => (mask,id))

def c20867 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20867 : Upper (D 8) (R 8) [96,5,24,34] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20867 c20867
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20867_33
  · exact u12665
  · exact u12666
  · exact u12667
  · exact u12668
  · exact u12669
  · exact u12670
  · exact u12671
  · exact u12672
  · exact u12673

def b20868 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 73 434 418 482 418 418), lower := (rows 97 7 28 73 16 32 64 128 256), losses := [] }

theorem u20868 : Upper (D 8) (R 8) [96,5,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20869 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 74 433 417 481 417 417), lower := (rows 97 7 28 74 16 32 64 128 256), losses := [] }

theorem u20869 : Upper (D 8) (R 8) [96,5,24,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20870 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 435 419 483 419 419), lower := (rows 97 7 28 104 16 32 64 128 256), losses := [] }

theorem u20870 : Upper (D 8) (R 8) [96,5,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20871 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 28 137 498 482 482 482 482), lower := (rows 97 7 28 137 16 32 64 128 256), losses := [] }

theorem u20871 : Upper (D 8) (R 8) [96,5,24,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20872_33 : Upper (D 8) (R 8) [96,5,24,130,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12660

theorem m20872_65 : Upper (D 8) (R 8) [96,5,24,130,65] 13 :=
  permutation_upper _ _ _ [96,5,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12674

theorem m20872_96 : Upper (D 8) (R 8) [96,5,24,130,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12684

theorem m20872_129 : Upper (D 8) (R 8) [96,5,24,130,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12689

def r20872 : Route 9 := (fun mask => (mask,id))

def c20872 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20872 : Upper (D 8) (R 8) [96,5,24,130] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r20872 c20872
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20872_33
  · exact m20872_65
  · exact m20872_96
  · exact m20872_129
  · exact u12696
  · exact u12697
  · exact u12698
  · exact u12699
  · exact u12700
  · exact u12701

theorem m20873_3 : Upper (D 8) (R 8) [96,5,24,160,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12507

theorem m20873_33 : Upper (D 8) (R 8) [96,5,24,160,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12661

theorem m20873_34 : Upper (D 8) (R 8) [96,5,24,160,34] 13 :=
  permutation_upper _ _ _ [96,5,24,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12668

theorem m20873_65 : Upper (D 8) (R 8) [96,5,24,160,65] 13 :=
  permutation_upper _ _ _ [96,5,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12675

theorem m20873_66 : Upper (D 8) (R 8) [96,5,24,160,66] 13 :=
  permutation_upper _ _ _ [96,5,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12680

theorem m20873_96 : Upper (D 8) (R 8) [96,5,24,160,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12685

theorem m20873_129 : Upper (D 8) (R 8) [96,5,24,160,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12690

theorem m20873_130 : Upper (D 8) (R 8) [96,5,24,160,130] 13 :=
  permutation_upper _ _ _ [96,5,24,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12696

def r20873 : Route 9 := (fun mask => (mask,id))

def c20873 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u20873 : Upper (D 8) (R 8) [96,5,24,160] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r20873 c20873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20873_3
  · exact m20873_33
  · exact m20873_34
  · exact m20873_65
  · exact m20873_66
  · exact m20873_96
  · exact m20873_129
  · exact m20873_130
  · exact u12702
  · exact u12703
  · exact u12704
  · exact u12705
  · exact u12706
  · exact u12707
  · exact u12708

def b20874 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 200 435 419 483 419 419), lower := (rows 97 7 28 200 16 32 64 128 256), losses := [] }

theorem u20874 : Upper (D 8) (R 8) [96,5,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20875 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 28 265 242 226 226 226 482), lower := (rows 97 7 28 265 16 32 64 128 256), losses := [] }

theorem u20875 : Upper (D 8) (R 8) [96,5,24,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20876_33 : Upper (D 8) (R 8) [96,5,24,258,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12662

theorem m20876_65 : Upper (D 8) (R 8) [96,5,24,258,65] 13 :=
  permutation_upper _ _ _ [96,5,24,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12676

theorem m20876_96 : Upper (D 8) (R 8) [96,5,24,258,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12686

theorem m20876_129 : Upper (D 8) (R 8) [96,5,24,258,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12692

theorem m20876_160 : Upper (D 8) (R 8) [96,5,24,258,160] 13 :=
  permutation_upper _ _ _ [96,5,24,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12705

theorem m20876_192 : Upper (D 8) (R 8) [96,5,24,258,192] 13 :=
  permutation_upper _ _ _ [96,5,24,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12710

def r20876 : Route 9 := (fun mask => (mask,id))

def c20876 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20876 : Upper (D 8) (R 8) [96,5,24,258] 13 := by
  apply FastRouting.sound _ _ [96,5,24,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r20876 c20876
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20876_33
  · exact m20876_65
  · exact m20876_96
  · exact m20876_129
  · exact m20876_160
  · exact m20876_192

theorem m20877_3 : Upper (D 8) (R 8) [96,5,24,288,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12509

theorem m20877_33 : Upper (D 8) (R 8) [96,5,24,288,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12663

theorem m20877_34 : Upper (D 8) (R 8) [96,5,24,288,34] 13 :=
  permutation_upper _ _ _ [96,5,24,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12671

theorem m20877_65 : Upper (D 8) (R 8) [96,5,24,288,65] 13 :=
  permutation_upper _ _ _ [96,5,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12677

theorem m20877_66 : Upper (D 8) (R 8) [96,5,24,288,66] 13 :=
  permutation_upper _ _ _ [96,5,24,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12682

theorem m20877_96 : Upper (D 8) (R 8) [96,5,24,288,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12687

theorem m20877_129 : Upper (D 8) (R 8) [96,5,24,288,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12693

theorem m20877_130 : Upper (D 8) (R 8) [96,5,24,288,130] 13 :=
  permutation_upper _ _ _ [96,5,24,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12699

theorem m20877_160 : Upper (D 8) (R 8) [96,5,24,288,160] 13 :=
  permutation_upper _ _ _ [96,5,24,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12706

theorem m20877_192 : Upper (D 8) (R 8) [96,5,24,288,192] 13 :=
  permutation_upper _ _ _ [96,5,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12711

def r20877 : Route 9 := (fun mask => (mask,id))

def c20877 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20877 : Upper (D 8) (R 8) [96,5,24,288] 13 := by
  apply FastRouting.sound _ _ [96,5,24,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r20877 c20877
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20877_3
  · exact m20877_33
  · exact m20877_34
  · exact m20877_65
  · exact m20877_66
  · exact m20877_96
  · exact m20877_129
  · exact m20877_130
  · exact m20877_160
  · exact m20877_192

def b20878 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 328 179 163 227 163 419), lower := (rows 97 7 28 328 16 32 64 128 256), losses := [] }

theorem u20878 : Upper (D 8) (R 8) [96,5,24,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m20879_3 : Upper (D 8) (R 8) [96,5,24,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12511

theorem m20879_33 : Upper (D 8) (R 8) [96,5,24,384,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12664

theorem m20879_34 : Upper (D 8) (R 8) [96,5,24,384,34] 13 :=
  permutation_upper _ _ _ [96,5,24,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12673

theorem m20879_65 : Upper (D 8) (R 8) [96,5,24,384,65] 13 :=
  permutation_upper _ _ _ [96,5,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12678

theorem m20879_66 : Upper (D 8) (R 8) [96,5,24,384,66] 13 :=
  permutation_upper _ _ _ [96,5,24,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12683

theorem m20879_96 : Upper (D 8) (R 8) [96,5,24,384,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12688

theorem m20879_129 : Upper (D 8) (R 8) [96,5,24,384,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12695

theorem m20879_130 : Upper (D 8) (R 8) [96,5,24,384,130] 13 :=
  permutation_upper _ _ _ [96,5,24,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12701

theorem m20879_160 : Upper (D 8) (R 8) [96,5,24,384,160] 13 :=
  permutation_upper _ _ _ [96,5,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12708

theorem m20879_192 : Upper (D 8) (R 8) [96,5,24,384,192] 13 :=
  permutation_upper _ _ _ [96,5,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12712

def r20879 : Route 9 := (fun mask => (mask,id))

def c20879 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u20879 : Upper (D 8) (R 8) [96,5,24,384] 13 := by
  apply FastRouting.sound _ _ [96,5,24,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r20879 c20879
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m20879_3
  · exact m20879_33
  · exact m20879_34
  · exact m20879_65
  · exact m20879_66
  · exact m20879_96
  · exact m20879_129
  · exact m20879_130
  · exact m20879_160
  · exact m20879_192

#print axioms u20879
end Delivery.IrregularNine14.P08
