import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0002

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2700 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 266 37 88 176 96 192 131 259), lower := (rows 7 266 37 88 176 96 192 128 256), losses := [] }

theorem u2700 : Upper (D 7) (R 7) [6,264,33,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2701 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 172, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(3,1)], upper := (rows 7 266 37 104 81 160 66 144 400), lower := (rows 7 266 37 104 81 160 66 128 256), losses := [] }

theorem u2701 : Upper (D 7) (R 7) [6,264,33,96,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2702 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 7 266 37 104 81 160 80 130 386), lower := (rows 7 266 37 104 81 160 80 128 256), losses := [] }

theorem u2702 : Upper (D 7) (R 7) [6,264,33,96,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2702 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2703 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 266 37 104 81 160 192 146 274), lower := (rows 7 266 37 104 81 160 192 128 256), losses := [] }

theorem u2703 : Upper (D 7) (R 7) [6,264,33,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2704 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 266 37 104 82 160 65 144 400), lower := (rows 7 266 37 104 82 160 65 128 256), losses := [] }

theorem u2704 : Upper (D 7) (R 7) [6,264,33,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2705 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 266 37 104 82 160 80 129 385), lower := (rows 7 266 37 104 82 160 80 128 256), losses := [] }

theorem u2705 : Upper (D 7) (R 7) [6,264,33,96,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2705 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2706 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 266 37 104 82 160 192 145 273), lower := (rows 7 266 37 104 82 160 192 128 256), losses := [] }

theorem u2706 : Upper (D 7) (R 7) [6,264,33,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2707 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 266 37 104 146 160 65 208 336), lower := (rows 7 266 37 104 146 160 65 128 256), losses := [] }

theorem u2707 : Upper (D 7) (R 7) [6,264,33,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2708 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 266 37 104 146 160 80 193 321), lower := (rows 7 266 37 104 146 160 80 128 256), losses := [] }

theorem u2708 : Upper (D 7) (R 7) [6,264,33,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2708 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2709 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 266 37 104 208 160 65 146 274), lower := (rows 7 266 37 104 208 160 65 128 256), losses := [] }

theorem u2709 : Upper (D 7) (R 7) [6,264,33,96,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2710 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 40, targets := 3 },{ cop := 0, region := 208, targets := 32 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 7 266 37 104 208 160 66 145 273), lower := (rows 7 266 37 104 208 160 66 128 256), losses := [{ target := 7, region := (rows 1 2 4 12 16 32 67 0 256), good := (rows 79 330 109 104 80 32 66 0 256) }] }

theorem u2710 : Upper (D 7) (R 7) [6,264,33,96,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2711 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 266 37 104 208 160 80 131 259), lower := (rows 7 266 37 104 208 160 80 128 256), losses := [] }

theorem u2711 : Upper (D 7) (R 7) [6,264,33,96,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2711 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2712 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 266 37 200 82 160 65 176 304), lower := (rows 7 266 37 200 82 160 65 128 256), losses := [] }

theorem u2712 : Upper (D 7) (R 7) [6,264,33,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2713 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 266 37 200 82 160 80 161 289), lower := (rows 7 266 37 200 82 160 80 128 256), losses := [] }

theorem u2713 : Upper (D 7) (R 7) [6,264,33,192,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2713 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2714 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 165, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 7 266 37 200 82 160 96 145 273), lower := (rows 7 266 37 200 82 160 96 128 256), losses := [] }

theorem u2714 : Upper (D 7) (R 7) [6,264,33,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2715 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 266 52 42 81 160 65 192 448), lower := (rows 7 266 52 42 81 160 65 128 256), losses := [] }

theorem u2715 : Upper (D 7) (R 7) [6,264,48,34,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2716 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(2,1),(4,1),(4,5)], upper := (rows 7 266 52 42 81 160 192 193 321), lower := (rows 7 266 52 42 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 224 224 128 256), good := (rows 6 266 116 106 116 224 224 224 256) }] }

theorem u2716 : Upper (D 7) (R 7) [6,264,48,34,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2717 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 180, targets := 2 },{ cop := 0, region := 72, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 266 52 73 145 96 66 160 416), lower := (rows 7 266 52 73 145 96 66 128 256), losses := [] }

theorem u2717 : Upper (D 7) (R 7) [6,264,48,65,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2718 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 7 266 52 73 145 96 96 130 386), lower := (rows 7 266 52 73 145 96 96 128 256), losses := [] }

theorem u2718 : Upper (D 7) (R 7) [6,264,48,65,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2719 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 3, region := 290, targets := 1 },{ cop := 3, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(3,1)], upper := (rows 7 266 52 73 145 96 192 162 290), lower := (rows 7 266 52 73 145 96 192 128 256), losses := [] }

theorem u2719 : Upper (D 7) (R 7) [6,264,48,65,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2720 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(4,0)], upper := (rows 7 266 52 73 146 96 65 160 416), lower := (rows 7 266 52 73 146 96 65 128 256), losses := [] }

theorem u2720 : Upper (D 7) (R 7) [6,264,48,65,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2721 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 7 266 52 73 146 96 96 129 385), lower := (rows 7 266 52 73 146 96 96 128 256), losses := [] }

theorem u2721 : Upper (D 7) (R 7) [6,264,48,65,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2722 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 0, region := 232, targets := 2 },{ cop := 3, region := 290, targets := 128 }], pairs := [(1,7),(2,0),(2,1),(3,1)], upper := (rows 7 266 52 73 146 96 192 161 289), lower := (rows 7 266 52 73 146 96 192 128 256), losses := [] }

theorem u2722 : Upper (D 7) (R 7) [6,264,48,65,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2723 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 180, targets := 2 },{ cop := 0, region := 72, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 266 52 73 208 33 66 160 416), lower := (rows 7 266 52 73 208 33 66 128 256), losses := [] }

theorem u2723 : Upper (D 7) (R 7) [6,264,48,65,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2724 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 7 266 52 73 208 33 96 130 386), lower := (rows 7 266 52 73 208 33 96 128 256), losses := [] }

theorem u2724 : Upper (D 7) (R 7) [6,264,48,65,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2725 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 52 73 208 33 192 162 290), lower := (rows 7 266 52 73 208 33 192 128 256), losses := [] }

theorem u2725 : Upper (D 7) (R 7) [6,264,48,65,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2726 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 266 52 73 208 34 65 160 416), lower := (rows 7 266 52 73 208 34 65 128 256), losses := [] }

theorem u2726 : Upper (D 7) (R 7) [6,264,48,65,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2727 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 402, targets := 32 },{ cop := 0, region := 104, targets := 128 },{ cop := 3, region := 144, targets := 2 }], pairs := [(1,5),(3,7),(4,1),(4,5)], upper := (rows 7 266 52 73 208 34 96 129 385), lower := (rows 7 266 52 73 208 34 96 128 256), losses := [] }

theorem u2727 : Upper (D 7) (R 7) [6,264,48,65,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2728 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 52 73 208 34 192 161 289), lower := (rows 7 266 52 73 208 34 192 128 256), losses := [] }

theorem u2728 : Upper (D 7) (R 7) [6,264,48,65,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2729 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 266 52 74 81 160 65 160 416), lower := (rows 7 266 52 74 81 160 65 128 256), losses := [] }

theorem u2729 : Upper (D 7) (R 7) [6,264,48,66,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2730 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 394, targets := 32 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 266 52 74 81 160 96 129 385), lower := (rows 7 266 52 74 81 160 96 128 256), losses := [] }

theorem u2730 : Upper (D 7) (R 7) [6,264,48,66,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2731 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 164, targets := 64 }], pairs := [(2,0),(2,1),(2,6),(4,1)], upper := (rows 7 266 52 74 81 160 192 161 289), lower := (rows 7 266 52 74 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 224 224 128 256), good := (rows 6 266 116 106 116 224 224 224 256) }] }

theorem u2731 : Upper (D 7) (R 7) [6,264,48,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2732 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 5, region := 394, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 266 52 74 145 96 65 160 416), lower := (rows 7 266 52 74 145 96 65 128 256), losses := [] }

theorem u2732 : Upper (D 7) (R 7) [6,264,48,66,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2733 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 266 52 74 145 96 96 129 385), lower := (rows 7 266 52 74 145 96 96 128 256), losses := [] }

theorem u2733 : Upper (D 7) (R 7) [6,264,48,66,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2734 : Route 9 := (fun mask => (mask,id))

def c2734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2734 : Upper (D 7) (R 7) [6,264,48,66,129,64,128] 13 := by
  apply FastRouting.sound _ _ [6,264,48,66,129,64,128] 13 (by decide) (choices 1) [1,32] r2734 c2734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u170
  · exact u171

def b2735 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 72, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 266 52 74 208 33 65 160 416), lower := (rows 7 266 52 74 208 33 65 128 256), losses := [] }

theorem u2735 : Upper (D 7) (R 7) [6,264,48,66,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2736 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 104, targets := 128 }], pairs := [(2,1),(3,0),(3,7),(4,1)], upper := (rows 7 266 52 74 208 33 96 129 385), lower := (rows 7 266 52 74 208 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 16 32 100 128 256), good := (rows 78 266 116 74 208 104 96 128 256) }] }

theorem u2736 : Upper (D 7) (R 7) [6,264,48,66,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2737 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 52 74 208 33 192 161 289), lower := (rows 7 266 52 74 208 33 192 128 256), losses := [] }

theorem u2737 : Upper (D 7) (R 7) [6,264,48,66,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2738 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 266 52 104 81 160 65 130 386), lower := (rows 7 266 52 104 81 160 65 128 256), losses := [] }

theorem u2738 : Upper (D 7) (R 7) [6,264,48,96,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2739 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 172, targets := 2 },{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 266 52 104 81 160 66 129 385), lower := (rows 7 266 52 104 81 160 66 128 256), losses := [] }

theorem u2739 : Upper (D 7) (R 7) [6,264,48,96,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2740 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 266 52 104 81 160 192 131 259), lower := (rows 7 266 52 104 81 160 192 128 256), losses := [] }

theorem u2740 : Upper (D 7) (R 7) [6,264,48,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2741 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 1 },{ cop := 0, region := 104, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 266 52 104 208 33 65 130 386), lower := (rows 7 266 52 104 208 33 65 128 256), losses := [] }

theorem u2741 : Upper (D 7) (R 7) [6,264,48,96,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2742 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 208, targets := 32 },{ cop := 0, region := 104, targets := 128 }], pairs := [(2,1),(3,0),(3,7),(4,5)], upper := (rows 7 266 52 104 208 33 66 129 385), lower := (rows 7 266 52 104 208 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 67 128 256), good := (rows 70 330 60 104 208 104 66 128 256) },{ target := 1, region := (rows 1 0 12 8 24 33 64 161 289), good := (rows 421 284 436 508 208 417 64 128 256) }] }

theorem u2742 : Upper (D 7) (R 7) [6,264,48,96,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2743 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 52 104 208 33 192 131 259), lower := (rows 7 266 52 104 208 33 192 128 256), losses := [] }

theorem u2743 : Upper (D 7) (R 7) [6,264,48,96,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2744 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 104, targets := 128 }], pairs := [(3,0),(3,7),(4,1),(4,5)], upper := (rows 7 266 52 104 208 34 65 129 385), lower := (rows 7 266 52 104 208 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 16 35 64 128 256), good := (rows 38 298 52 104 216 34 104 128 256) }] }

theorem u2744 : Upper (D 7) (R 7) [6,264,48,96,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2745 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 52 104 208 34 192 129 257), lower := (rows 7 266 52 104 208 34 192 128 256), losses := [] }

theorem u2745 : Upper (D 7) (R 7) [6,264,48,96,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2746 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 117, targets := 128 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 266 52 200 81 34 65 160 416), lower := (rows 7 266 52 200 81 34 65 128 256), losses := [] }

theorem u2746 : Upper (D 7) (R 7) [6,264,48,192,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2747 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 117, targets := 128 },{ cop := 4, region := 394, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 7 266 52 200 81 34 96 129 385), lower := (rows 7 266 52 200 81 34 96 128 256), losses := [] }

theorem u2747 : Upper (D 7) (R 7) [6,264,48,192,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2748 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 266 52 200 81 34 192 161 289), lower := (rows 7 266 52 200 81 34 192 128 256), losses := [] }

theorem u2748 : Upper (D 7) (R 7) [6,264,48,192,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2749 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 7 266 52 200 81 160 65 162 290), lower := (rows 7 266 52 200 81 160 65 128 256), losses := [] }

theorem u2749 : Upper (D 7) (R 7) [6,264,48,192,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2750 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 4, region := 172, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 266 52 200 81 160 66 161 289), lower := (rows 7 266 52 200 81 160 66 128 256), losses := [] }

theorem u2750 : Upper (D 7) (R 7) [6,264,48,192,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2751 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 394, targets := 32 },{ cop := 5, region := 72, targets := 3 }], pairs := [(1,5),(3,0),(3,1),(3,5)], upper := (rows 7 266 52 200 81 160 96 131 259), lower := (rows 7 266 52 200 81 160 96 128 256), losses := [] }

theorem u2751 : Upper (D 7) (R 7) [6,264,48,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2752 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(4,5),(4,7)], upper := (rows 7 266 52 200 82 160 65 161 289), lower := (rows 7 266 52 200 82 160 65 128 256), losses := [] }

theorem u2752 : Upper (D 7) (R 7) [6,264,48,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2753 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 165, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 7 266 52 200 82 160 96 129 257), lower := (rows 7 266 52 200 82 160 96 128 256), losses := [] }

theorem u2753 : Upper (D 7) (R 7) [6,264,48,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2754 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 6, region := 164, targets := 1 }], pairs := [(0,7),(2,0),(2,7),(3,7)], upper := (rows 7 266 100 25 50 160 65 192 448), lower := (rows 7 266 100 25 50 160 65 128 256), losses := [] }

theorem u2754 : Upper (D 7) (R 7) [6,264,96,17,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2755 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 266 100 25 50 160 192 193 321), lower := (rows 7 266 100 25 50 160 192 128 256), losses := [] }

theorem u2755 : Upper (D 7) (R 7) [6,264,96,17,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2756 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5),(4,5)], upper := (rows 7 266 100 25 146 33 96 192 448), lower := (rows 7 266 100 25 146 33 96 128 256), losses := [] }

theorem u2756 : Upper (D 7) (R 7) [6,264,96,17,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2757 : Route 9 := (fun mask => (mask,id))

def c2757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2757 : Upper (D 7) (R 7) [6,264,96,17,130,1,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17,130,1,128] 13 (by decide) (choices 1) [32,64] r2757 c2757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u172
  · exact u173

def b2758 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 25 146 96 192 161 289), lower := (rows 7 266 100 25 146 96 192 128 256), losses := [] }

theorem u2758 : Upper (D 7) (R 7) [6,264,96,17,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2759 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 144, targets := 3 }], pairs := [(0,7),(2,7),(4,0),(4,1)], upper := (rows 7 266 100 25 176 34 65 192 448), lower := (rows 7 266 100 25 176 34 65 128 256), losses := [] }

theorem u2759 : Upper (D 7) (R 7) [6,264,96,17,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2759
end Delivery.IrregularNine14.P07
