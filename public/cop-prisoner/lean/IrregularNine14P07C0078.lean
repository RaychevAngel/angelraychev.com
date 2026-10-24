import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4680 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 13 290 70 200 19 160 80 161 289), lower := (rows 13 290 70 200 19 160 80 128 256), losses := [] }

theorem u4680 : Upper (D 7) (R 7) [12,288,66,192,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4680 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4681 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 290 70 200 19 160 96 145 273), lower := (rows 13 290 70 200 19 160 96 128 256), losses := [] }

theorem u4681 : Upper (D 7) (R 7) [12,288,66,192,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4682 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 70 200 146 33 65 176 304), lower := (rows 13 290 70 200 146 33 65 128 256), losses := [] }

theorem u4682 : Upper (D 7) (R 7) [12,288,66,192,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4683 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 70 200 146 33 80 161 289), lower := (rows 13 290 70 200 146 33 80 128 256), losses := [] }

theorem u4683 : Upper (D 7) (R 7) [12,288,66,192,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4683 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4684 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 153, targets := 32 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,5),(1,6),(3,5),(4,5)], upper := (rows 13 290 70 200 146 33 96 145 273), lower := (rows 13 290 70 200 146 33 96 128 256), losses := [] }

theorem u4684 : Upper (D 7) (R 7) [12,288,66,192,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4685 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 70 200 146 48 65 161 289), lower := (rows 13 290 70 200 146 48 65 128 256), losses := [] }

theorem u4685 : Upper (D 7) (R 7) [12,288,66,192,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4685 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4686 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 13 290 70 200 146 48 96 129 257), lower := (rows 13 290 70 200 146 48 96 128 256), losses := [] }

theorem u4686 : Upper (D 7) (R 7) [12,288,66,192,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4686 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4687 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 70 200 176 33 65 146 274), lower := (rows 13 290 70 200 176 33 65 128 256), losses := [] }

theorem u4687 : Upper (D 7) (R 7) [12,288,66,192,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4688 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 290 70 200 176 33 66 145 273), lower := (rows 13 290 70 200 176 33 66 128 256), losses := [] }

theorem u4688 : Upper (D 7) (R 7) [12,288,66,192,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4689 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 70 200 176 33 80 131 259), lower := (rows 13 290 70 200 176 33 80 128 256), losses := [] }

theorem u4689 : Upper (D 7) (R 7) [12,288,66,192,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4689 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4690 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 84 104 19 160 65 130 386), lower := (rows 13 290 84 104 19 160 65 128 256), losses := [] }

theorem u4690 : Upper (D 7) (R 7) [12,288,80,96,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4691 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 84 104 19 160 66 129 385), lower := (rows 13 290 84 104 19 160 66 128 256), losses := [] }

theorem u4691 : Upper (D 7) (R 7) [12,288,80,96,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4692 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 84 104 19 160 192 131 259), lower := (rows 13 290 84 104 19 160 192 128 256), losses := [] }

theorem u4692 : Upper (D 7) (R 7) [12,288,80,96,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4693 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 290 84 168 19 96 65 130 386), lower := (rows 13 290 84 168 19 96 65 128 256), losses := [] }

theorem u4693 : Upper (D 7) (R 7) [12,288,80,160,3,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4694 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 129 }], pairs := [(0,1),(2,0),(2,7),(3,1)], upper := (rows 13 290 84 168 19 96 66 129 385), lower := (rows 13 290 84 168 19 96 66 128 256), losses := [] }

theorem u4694 : Upper (D 7) (R 7) [12,288,80,160,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4695 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 40, targets := 3 },{ cop := 4, region := 196, targets := 32 }], pairs := [(0,1),(2,5),(3,0),(3,1)], upper := (rows 13 290 84 168 19 96 192 131 259), lower := (rows 13 290 84 168 19 96 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 200 16 237 200 128 256), good := (rows 109 288 125 232 49 104 232 232 256) }] }

theorem u4695 : Upper (D 7) (R 7) [12,288,80,160,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4696 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 290 84 168 145 96 65 130 258), lower := (rows 13 290 84 168 145 96 65 128 256), losses := [] }

theorem u4696 : Upper (D 7) (R 7) [12,288,80,160,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4697 : Route 9 := (fun mask => (mask,id))

def c4697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4697 : Upper (D 7) (R 7) [12,288,80,160,129,64,2] 13 := by
  apply FastRouting.sound _ _ [12,288,80,160,129,64,2] 13 (by decide) (choices 1) [1,2] r4697 c4697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u366
  · exact u367

def b4698 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 0, region := 354, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 13 290 84 168 146 33 65 194 322), lower := (rows 13 290 84 168 146 33 65 128 256), losses := [] }

theorem u4698 : Upper (D 7) (R 7) [12,288,80,160,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4699 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 161 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 13 290 84 168 146 33 66 193 321), lower := (rows 13 290 84 168 146 33 66 128 256), losses := [] }

theorem u4699 : Upper (D 7) (R 7) [12,288,80,160,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4700 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 0, region := 354, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 13 290 84 168 146 96 65 131 259), lower := (rows 13 290 84 168 146 96 65 128 256), losses := [] }

theorem u4700 : Upper (D 7) (R 7) [12,288,80,160,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4701 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 108, targets := 1 }], pairs := [(0,1),(2,0),(3,0),(3,1)], upper := (rows 13 290 84 168 146 96 66 129 257), lower := (rows 13 290 84 168 146 96 66 128 256), losses := [] }

theorem u4701 : Upper (D 7) (R 7) [12,288,80,160,130,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4702 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 13 290 84 200 19 160 65 162 290), lower := (rows 13 290 84 200 19 160 65 128 256), losses := [] }

theorem u4702 : Upper (D 7) (R 7) [12,288,80,192,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4703 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 68, targets := 161 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(2,0),(2,5),(2,7)], upper := (rows 13 290 84 200 19 160 66 161 289), lower := (rows 13 290 84 200 19 160 66 128 256), losses := [] }

theorem u4703 : Upper (D 7) (R 7) [12,288,80,192,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4704 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(1,6),(3,0),(3,1),(4,6)], upper := (rows 13 290 84 200 19 160 96 131 259), lower := (rows 13 290 84 200 19 160 96 128 256), losses := [] }

theorem u4704 : Upper (D 7) (R 7) [12,288,80,192,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4705 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 84 200 146 33 65 162 290), lower := (rows 13 290 84 200 146 33 65 128 256), losses := [] }

theorem u4705 : Upper (D 7) (R 7) [12,288,80,192,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4706 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 0, region := 290, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 290 84 200 146 33 66 161 289), lower := (rows 13 290 84 200 146 33 66 128 256), losses := [] }

theorem u4706 : Upper (D 7) (R 7) [12,288,80,192,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4707 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 0, region := 290, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(3,1)], upper := (rows 13 290 84 200 146 33 96 131 259), lower := (rows 13 290 84 200 146 33 96 128 256), losses := [] }

theorem u4707 : Upper (D 7) (R 7) [12,288,80,192,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4708 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 290 100 200 146 48 65 131 259), lower := (rows 13 290 100 200 146 48 65 128 256), losses := [] }

theorem u4708 : Upper (D 7) (R 7) [12,288,96,192,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4708 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4709 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 137, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 13 290 100 200 146 48 66 129 257), lower := (rows 13 290 100 200 146 48 66 128 256), losses := [] }

theorem u4709 : Upper (D 7) (R 7) [12,288,96,192,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4709 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4710 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 26 148 288 96 192 448), lower := (rows 35 67 13 26 148 288 96 128 256), losses := [] }

theorem u4710 : Upper (D 7) (R 7) [34,65,9,18,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4710 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4711 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,7),(4,0),(4,1)], upper := (rows 35 67 13 26 148 288 192 224 352), lower := (rows 35 67 13 26 148 288 192 128 256), losses := [] }

theorem u4711 : Upper (D 7) (R 7) [34,65,9,18,132,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4711 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4712 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,5),(3,5),(4,0),(4,5)], upper := (rows 35 67 13 26 276 160 96 192 448), lower := (rows 35 67 13 26 276 160 96 128 256), losses := [] }

theorem u4712 : Upper (D 7) (R 7) [34,65,9,18,260,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4713 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 496, targets := 3 }], pairs := [(0,6),(1,5),(4,0),(4,1)], upper := (rows 35 67 13 26 276 160 192 224 352), lower := (rows 35 67 13 26 276 160 192 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 224 128 256), good := (rows 67 67 15 26 276 192 192 192 256) },{ target := 6, region := (rows 3 2 12 8 16 224 0 128 256), good := (rows 35 35 13 31 276 160 160 160 256) }] }

theorem u4713 : Upper (D 7) (R 7) [34,65,9,18,260,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4714 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 26 304 160 68 192 448), lower := (rows 35 67 13 26 304 160 68 128 256), losses := [] }

theorem u4714 : Upper (D 7) (R 7) [34,65,9,18,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4714 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4715 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 2, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(4,0),(4,1)], upper := (rows 35 67 13 26 304 160 192 196 324), lower := (rows 35 67 13 26 304 160 192 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 224 0 128 256), good := (rows 35 35 13 31 304 160 160 160 256) }] }

theorem u4715 : Upper (D 7) (R 7) [34,65,9,18,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4716 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 28 146 288 96 192 448), lower := (rows 35 67 13 28 146 288 96 128 256), losses := [] }

theorem u4716 : Upper (D 7) (R 7) [34,65,9,20,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4716 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4717 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 291, targets := 128 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,7),(1,7),(4,0)], upper := (rows 35 67 13 28 146 288 192 224 352), lower := (rows 35 67 13 28 146 288 192 128 256), losses := [] }

theorem u4717 : Upper (D 7) (R 7) [34,65,9,20,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4717 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4718 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 28 274 160 96 192 448), lower := (rows 35 67 13 28 274 160 96 128 256), losses := [] }

theorem u4718 : Upper (D 7) (R 7) [34,65,9,20,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4719 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 464, targets := 1 }], pairs := [(0,6),(1,5),(3,0),(4,0)], upper := (rows 35 67 13 28 274 160 192 224 352), lower := (rows 35 67 13 28 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 19 511 511 511 511), good := (rows 498 498 508 508 498 480 480 480 480) },{ target := 5, region := (rows 1 3 4 8 16 0 224 128 256), good := (rows 67 67 15 28 274 192 192 192 256) },{ target := 6, region := (rows 3 2 20 24 16 224 0 128 256), good := (rows 35 35 13 28 287 160 160 160 256) }] }

theorem u4719 : Upper (D 7) (R 7) [34,65,9,20,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4720 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 28 304 160 66 192 448), lower := (rows 35 67 13 28 304 160 66 128 256), losses := [] }

theorem u4720 : Upper (D 7) (R 7) [34,65,9,20,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4721 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(3,0),(4,0)], upper := (rows 35 67 13 28 304 160 192 194 322), lower := (rows 35 67 13 28 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 231 231 131 259), good := (rows 498 498 508 124 368 224 224 224 256) },{ target := 6, region := (rows 3 2 4 8 16 224 0 128 256), good := (rows 35 35 13 28 304 160 160 160 256) }] }

theorem u4721 : Upper (D 7) (R 7) [34,65,9,20,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4722 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 28 336 160 66 160 416), lower := (rows 35 67 13 28 336 160 66 128 256), losses := [] }

theorem u4722 : Upper (D 7) (R 7) [34,65,9,20,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4723 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 28 336 160 96 130 386), lower := (rows 35 67 13 28 336 160 96 128 256), losses := [] }

theorem u4723 : Upper (D 7) (R 7) [34,65,9,20,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4724 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(4,0)], upper := (rows 35 67 13 28 336 160 192 162 290), lower := (rows 35 67 13 28 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 231 231 131 259), good := (rows 498 498 508 124 368 224 224 224 256) },{ target := 5, region := (rows 1 3 4 8 16 0 224 128 256), good := (rows 67 67 15 28 336 192 192 192 256) }] }

theorem u4724 : Upper (D 7) (R 7) [34,65,9,20,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4725 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 56 146 288 68 192 448), lower := (rows 35 67 13 56 146 288 68 128 256), losses := [] }

theorem u4725 : Upper (D 7) (R 7) [34,65,9,48,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4725 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4726 : Route 9 := (fun mask => (mask,id))

def c4726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4726 : Upper (D 7) (R 7) [34,65,9,48,130,256,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,130,256,128] 13 (by decide) (choices 1) [4,64] r4726 c4726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u368
  · exact u369

def b4727 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 13 56 208 288 66 132 388), lower := (rows 35 67 13 56 208 288 66 128 256), losses := [] }

theorem u4727 : Upper (D 7) (R 7) [34,65,9,48,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4727 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4728 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 56 208 288 68 130 386), lower := (rows 35 67 13 56 208 288 68 128 256), losses := [] }

theorem u4728 : Upper (D 7) (R 7) [34,65,9,48,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4728 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4729 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 56 208 288 192 134 262), lower := (rows 35 67 13 56 208 288 192 128 256), losses := [] }

theorem u4729 : Upper (D 7) (R 7) [34,65,9,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4729 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4730 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 56 274 160 68 192 448), lower := (rows 35 67 13 56 274 160 68 128 256), losses := [] }

theorem u4730 : Upper (D 7) (R 7) [34,65,9,48,258,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4730 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4731 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(0,6),(1,5),(2,7),(4,5)], upper := (rows 35 67 13 56 274 160 192 196 324), lower := (rows 35 67 13 56 274 160 192 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 224 0 128 256), good := (rows 35 35 13 56 275 160 160 160 256) },{ target := 7, region := (rows 1 2 7 9 19 32 64 0 258), good := (rows 319 351 29 56 278 32 64 0 256) }] }

theorem u4731 : Upper (D 7) (R 7) [34,65,9,48,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4732 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 56 336 160 66 132 388), lower := (rows 35 67 13 56 336 160 66 128 256), losses := [] }

theorem u4732 : Upper (D 7) (R 7) [34,65,9,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4733 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 56 336 160 68 130 386), lower := (rows 35 67 13 56 336 160 68 128 256), losses := [] }

theorem u4733 : Upper (D 7) (R 7) [34,65,9,48,320,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4733 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4734 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 35 67 13 56 336 160 192 134 262), lower := (rows 35 67 13 56 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 98 98 12 120 376 224 224 224 256) },{ target := 1, region := (rows 1 0 4 24 16 224 224 128 256), good := (rows 97 97 13 120 376 224 224 224 256) }] }

theorem u4734 : Upper (D 7) (R 7) [34,65,9,48,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4735 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 88 146 160 68 416 288), lower := (rows 35 67 13 88 146 160 68 128 256), losses := [] }

theorem u4735 : Upper (D 7) (R 7) [34,65,9,80,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4735 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4736 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 4, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(3,5),(4,5)], upper := (rows 35 67 13 88 146 160 96 388 260), lower := (rows 35 67 13 88 146 160 96 128 256), losses := [] }

theorem u4736 : Upper (D 7) (R 7) [34,65,9,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4737 : Route 9 := (fun mask => (mask,id))

def c4737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4737 : Upper (D 7) (R 7) [34,65,9,80,130,128,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,130,128,256] 13 (by decide) (choices 1) [4,32] r4737 c4737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u370
  · exact u371

def b4738 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 13 88 146 288 68 160 416), lower := (rows 35 67 13 88 146 288 68 128 256), losses := [] }

theorem u4738 : Upper (D 7) (R 7) [34,65,9,80,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4738 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4739 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 88 146 288 96 132 388), lower := (rows 35 67 13 88 146 288 96 128 256), losses := [] }

theorem u4739 : Upper (D 7) (R 7) [34,65,9,80,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4739 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4739
end Delivery.IrregularNine14.P07
