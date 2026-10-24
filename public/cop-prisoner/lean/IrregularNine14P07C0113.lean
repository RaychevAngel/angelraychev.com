import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6780 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 305, targets := 128 },{ cop := 2, region := 33, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,7)], upper := (rows 37 42 70 152 336 33 192 131 259), lower := (rows 37 42 70 152 336 33 192 128 256), losses := [] }

theorem u6780 : Upper (D 7) (R 7) [36,40,66,144,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6781 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7)], upper := (rows 37 42 70 200 145 288 65 146 274), lower := (rows 37 42 70 200 145 288 65 128 256), losses := [] }

theorem u6781 : Upper (D 7) (R 7) [36,40,66,192,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6781 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6782 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 42 70 200 145 288 66 145 273), lower := (rows 37 42 70 200 145 288 66 128 256), losses := [] }

theorem u6782 : Upper (D 7) (R 7) [36,40,66,192,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6782 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6783 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 42 70 200 145 288 80 131 259), lower := (rows 37 42 70 200 145 288 80 128 256), losses := [] }

theorem u6783 : Upper (D 7) (R 7) [36,40,66,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6783 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6784 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 136, targets := 1 }], pairs := [(0,7),(2,7),(3,0)], upper := (rows 37 42 70 200 273 48 65 130 386), lower := (rows 37 42 70 200 273 48 65 128 256), losses := [] }

theorem u6784 : Upper (D 7) (R 7) [36,40,66,192,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6784 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6785 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 42 70 200 273 48 66 129 385), lower := (rows 37 42 70 200 273 48 66 128 256), losses := [] }

theorem u6785 : Upper (D 7) (R 7) [36,40,66,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6785 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6786 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 70 200 273 48 192 131 259), lower := (rows 37 42 70 200 273 48 192 128 256), losses := [] }

theorem u6786 : Upper (D 7) (R 7) [36,40,66,192,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6786 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6787 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 42 70 265 81 160 66 144 400), lower := (rows 37 42 70 265 81 160 66 128 256), losses := [] }

theorem u6787 : Upper (D 7) (R 7) [36,40,66,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6788 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 42 70 265 81 160 80 130 386), lower := (rows 37 42 70 265 81 160 80 128 256), losses := [] }

theorem u6788 : Upper (D 7) (R 7) [36,40,66,257,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6788 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6789 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(2,0),(3,6)], upper := (rows 37 42 70 265 81 160 192 146 274), lower := (rows 37 42 70 265 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 224 224 128 256), good := (rows 100 110 102 264 112 224 224 224 256) },{ target := 1, region := (rows 5 0 4 8 21 224 224 128 256), good := (rows 117 104 117 281 113 224 224 224 256) }] }

theorem u6789 : Upper (D 7) (R 7) [36,40,66,257,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6790 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 42 70 265 145 160 66 208 336), lower := (rows 37 42 70 265 145 160 66 128 256), losses := [] }

theorem u6790 : Upper (D 7) (R 7) [36,40,66,257,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6791 : PairBound 9 := { available := 66, camps := [], pairs := [(1,0),(2,5),(3,5)], upper := (rows 37 42 70 265 145 160 80 194 322), lower := (rows 37 42 70 265 145 160 80 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 181 80 132 260), good := (rows 420 42 486 298 240 160 112 160 256) },{ target := 5, region := (rows 1 2 6 9 17 0 89 134 262), good := (rows 477 462 454 345 217 128 80 128 256) }] }

theorem u6791 : Upper (D 7) (R 7) [36,40,66,257,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6791 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6792 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 1 },{ cop := 2, region := 144, targets := 32 }], pairs := [(0,7),(2,7),(4,0),(4,5)], upper := (rows 37 42 70 265 146 160 65 208 336), lower := (rows 37 42 70 265 146 160 65 128 256), losses := [] }

theorem u6792 : Upper (D 7) (R 7) [36,40,66,257,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6793 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 425, targets := 2 },{ cop := 4, region := 68, targets := 32 }], pairs := [(0,1),(2,5),(3,1)], upper := (rows 37 42 70 265 146 160 80 193 321), lower := (rows 37 42 70 265 146 160 80 128 256), losses := [] }

theorem u6793 : Upper (D 7) (R 7) [36,40,66,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6793 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6794 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 37 42 70 265 208 48 65 130 386), lower := (rows 37 42 70 265 208 48 65 128 256), losses := [] }

theorem u6794 : Upper (D 7) (R 7) [36,40,66,257,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6794 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6795 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 42 70 265 208 48 66 129 385), lower := (rows 37 42 70 265 208 48 66 128 256), losses := [] }

theorem u6795 : Upper (D 7) (R 7) [36,40,66,257,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6795 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6796 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 70 265 208 48 192 131 259), lower := (rows 37 42 70 265 208 48 192 128 256), losses := [] }

theorem u6796 : Upper (D 7) (R 7) [36,40,66,257,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6796 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6797 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 1 },{ cop := 2, region := 144, targets := 32 }], pairs := [(0,7),(2,7),(4,0),(4,5)], upper := (rows 37 42 70 265 208 160 65 146 274), lower := (rows 37 42 70 265 208 160 65 128 256), losses := [] }

theorem u6797 : Upper (D 7) (R 7) [36,40,66,257,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6798 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 42 70 265 208 160 66 145 273), lower := (rows 37 42 70 265 208 160 66 128 256), losses := [] }

theorem u6798 : Upper (D 7) (R 7) [36,40,66,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6799 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 42 70 265 208 160 80 131 259), lower := (rows 37 42 70 265 208 160 80 128 256), losses := [] }

theorem u6799 : Upper (D 7) (R 7) [36,40,66,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6799 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6800 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 42 70 266 145 160 65 208 336), lower := (rows 37 42 70 266 145 160 65 128 256), losses := [] }

theorem u6800 : Upper (D 7) (R 7) [36,40,66,258,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6801 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,1),(4,1),(4,5)], upper := (rows 37 42 70 266 145 160 80 193 321), lower := (rows 37 42 70 266 145 160 80 128 256), losses := [] }

theorem u6801 : Upper (D 7) (R 7) [36,40,66,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6801 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6802 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 42 70 266 208 160 65 145 273), lower := (rows 37 42 70 266 208 160 65 128 256), losses := [] }

theorem u6802 : Upper (D 7) (R 7) [36,40,66,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6803 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 42 70 266 208 160 80 129 257), lower := (rows 37 42 70 266 208 160 80 128 256), losses := [] }

theorem u6803 : Upper (D 7) (R 7) [36,40,66,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6803 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6804 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 42 70 280 81 160 65 130 386), lower := (rows 37 42 70 280 81 160 65 128 256), losses := [] }

theorem u6804 : Upper (D 7) (R 7) [36,40,66,272,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6805 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 42 70 280 81 160 66 129 385), lower := (rows 37 42 70 280 81 160 66 128 256), losses := [] }

theorem u6805 : Upper (D 7) (R 7) [36,40,66,272,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6806 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 37 42 70 280 81 160 192 131 259), lower := (rows 37 42 70 280 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 224 224 128 256), good := (rows 100 110 102 280 112 224 224 224 256) }] }

theorem u6806 : Upper (D 7) (R 7) [36,40,66,272,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6807 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 70 280 208 33 65 130 386), lower := (rows 37 42 70 280 208 33 65 128 256), losses := [] }

theorem u6807 : Upper (D 7) (R 7) [36,40,66,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6808 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 37 42 70 280 208 33 66 129 385), lower := (rows 37 42 70 280 208 33 66 128 256), losses := [] }

theorem u6808 : Upper (D 7) (R 7) [36,40,66,272,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6809 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 42 70 280 208 33 192 131 259), lower := (rows 37 42 70 280 208 33 192 128 256), losses := [] }

theorem u6809 : Upper (D 7) (R 7) [36,40,66,272,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6810 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 392, targets := 1 }], pairs := [(0,7),(2,7),(3,0)], upper := (rows 37 42 70 328 145 48 65 130 386), lower := (rows 37 42 70 328 145 48 65 128 256), losses := [] }

theorem u6810 : Upper (D 7) (R 7) [36,40,66,320,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6810 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6811 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 42 70 328 145 48 66 129 385), lower := (rows 37 42 70 328 145 48 66 128 256), losses := [] }

theorem u6811 : Upper (D 7) (R 7) [36,40,66,320,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6811 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6812 : Route 9 := (fun mask => (mask,id))

def c6812 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6812 : Upper (D 7) (R 7) [36,40,66,320,129,16,128] 13 := by
  apply FastRouting.sound _ _ [36,40,66,320,129,16,128] 13 (by decide) (choices 1) [1,2] r6812 c6812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u494
  · exact u495

def b6813 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 37 42 70 328 145 160 65 146 274), lower := (rows 37 42 70 328 145 160 65 128 256), losses := [] }

theorem u6813 : Upper (D 7) (R 7) [36,40,66,320,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6814 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 42 70 328 145 160 66 145 273), lower := (rows 37 42 70 328 145 160 66 128 256), losses := [] }

theorem u6814 : Upper (D 7) (R 7) [36,40,66,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6815 : Route 9 := (fun mask => (mask,id))

def c6815 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6815 : Upper (D 7) (R 7) [36,40,66,320,129,128,16] 13 := by
  apply FastRouting.sound _ _ [36,40,66,320,129,128,16] 13 (by decide) (choices 1) [1,2] r6815 c6815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u496
  · exact u497

def b6816 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 37 42 70 328 146 160 65 145 273), lower := (rows 37 42 70 328 146 160 65 128 256), losses := [] }

theorem u6816 : Upper (D 7) (R 7) [36,40,66,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6817 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 425, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 42 70 328 146 160 80 129 257), lower := (rows 37 42 70 328 146 160 80 128 256), losses := [] }

theorem u6817 : Upper (D 7) (R 7) [36,40,66,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6817 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6818 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 37 42 70 392 145 33 66 208 336), lower := (rows 37 42 70 392 145 33 66 128 256), losses := [] }

theorem u6818 : Upper (D 7) (R 7) [36,40,66,384,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6819 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 392, targets := 33 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(3,0),(3,5)], upper := (rows 37 42 70 392 145 33 80 194 322), lower := (rows 37 42 70 392 145 33 80 128 256), losses := [] }

theorem u6819 : Upper (D 7) (R 7) [36,40,66,384,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6819 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6820 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 392, targets := 1 }], pairs := [(0,7),(2,7),(3,0)], upper := (rows 37 42 70 392 145 48 65 194 322), lower := (rows 37 42 70 392 145 48 65 128 256), losses := [] }

theorem u6820 : Upper (D 7) (R 7) [36,40,66,384,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6820 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6821 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 42 70 392 145 48 66 193 321), lower := (rows 37 42 70 392 145 48 66 128 256), losses := [] }

theorem u6821 : Upper (D 7) (R 7) [36,40,66,384,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6821 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6822 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 70 392 208 33 65 146 274), lower := (rows 37 42 70 392 208 33 65 128 256), losses := [] }

theorem u6822 : Upper (D 7) (R 7) [36,40,66,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6823 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 37 42 70 392 208 33 66 145 273), lower := (rows 37 42 70 392 208 33 66 128 256), losses := [] }

theorem u6823 : Upper (D 7) (R 7) [36,40,66,384,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6824 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 42 70 392 208 33 80 131 259), lower := (rows 37 42 70 392 208 33 80 128 256), losses := [] }

theorem u6824 : Upper (D 7) (R 7) [36,40,66,384,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6824 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6825 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 42 84 200 145 34 65 386 258), lower := (rows 37 42 84 200 145 34 65 128 256), losses := [] }

theorem u6825 : Upper (D 7) (R 7) [36,40,80,192,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6826 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 400, targets := 98 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,6)], upper := (rows 37 42 84 200 145 34 66 385 257), lower := (rows 37 42 84 200 145 34 66 128 256), losses := [] }

theorem u6826 : Upper (D 7) (R 7) [36,40,80,192,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6827 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7)], upper := (rows 37 42 84 200 145 34 320 131 259), lower := (rows 37 42 84 200 145 34 320 128 256), losses := [] }

theorem u6827 : Upper (D 7) (R 7) [36,40,80,192,129,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6827 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6828 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 37 42 84 200 145 288 65 130 258), lower := (rows 37 42 84 200 145 288 65 128 256), losses := [] }

theorem u6828 : Upper (D 7) (R 7) [36,40,80,192,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6828 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6829 : Route 9 := (fun mask => (mask,id))

def c6829 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6829 : Upper (D 7) (R 7) [36,40,80,192,129,256,2] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,129,256,2] 13 (by decide) (choices 1) [1,2] r6829 c6829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u498
  · exact u499

def r6830 : Route 9 := (fun mask => (mask,id))

def c6830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6830 : Upper (D 7) (R 7) [36,40,80,192,130,256,1] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,130,256,1] 13 (by decide) (choices 1) [1,2] r6830 c6830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u500
  · exact u501

def b6831 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 42 84 200 146 288 66 129 257), lower := (rows 37 42 84 200 146 288 66 128 256), losses := [] }

theorem u6831 : Upper (D 7) (R 7) [36,40,80,192,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6831 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6832 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 2, region := 170, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 37 42 84 200 273 34 65 130 386), lower := (rows 37 42 84 200 273 34 65 128 256), losses := [] }

theorem u6832 : Upper (D 7) (R 7) [36,40,80,192,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6833 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 98 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,6)], upper := (rows 37 42 84 200 273 34 66 129 385), lower := (rows 37 42 84 200 273 34 66 128 256), losses := [] }

theorem u6833 : Upper (D 7) (R 7) [36,40,80,192,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6834 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 84 200 273 34 192 131 259), lower := (rows 37 42 84 200 273 34 192 128 256), losses := [] }

theorem u6834 : Upper (D 7) (R 7) [36,40,80,192,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6835 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 84 200 274 33 65 130 386), lower := (rows 37 42 84 200 274 33 65 128 256), losses := [] }

theorem u6835 : Upper (D 7) (R 7) [36,40,80,192,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6836 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 33 }], pairs := [(0,1),(2,0),(2,5),(3,1)], upper := (rows 37 42 84 200 274 33 66 129 385), lower := (rows 37 42 84 200 274 33 66 128 256), losses := [] }

theorem u6836 : Upper (D 7) (R 7) [36,40,80,192,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6837 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 84 200 274 33 192 131 259), lower := (rows 37 42 84 200 274 33 192 128 256), losses := [] }

theorem u6837 : Upper (D 7) (R 7) [36,40,80,192,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6838 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 400, targets := 97 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,6)], upper := (rows 37 42 84 200 400 33 65 130 258), lower := (rows 37 42 84 200 400 33 65 128 256), losses := [] }

theorem u6838 : Upper (D 7) (R 7) [36,40,80,192,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6839 : Route 9 := (fun mask => (mask,id))

def c6839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6839 : Upper (D 7) (R 7) [36,40,80,192,384,1,2] 13 := by
  apply FastRouting.sound _ _ [36,40,80,192,384,1,2] 13 (by decide) (choices 1) [1,2] r6839 c6839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u502
  · exact u503

#print axioms u6839
end Delivery.IrregularNine14.P07
