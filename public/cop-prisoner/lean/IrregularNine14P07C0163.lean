import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9780 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 68, targets := 32 }], pairs := [(0,7),(2,5),(2,7),(3,7)], upper := (rows 37 290 70 11 152 160 65 208 336), lower := (rows 37 290 70 11 152 160 65 128 256), losses := [] }

theorem u9780 : Upper (D 7) (R 7) [36,288,66,3,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9781 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,5),(4,5)], upper := (rows 37 290 70 11 152 160 80 193 321), lower := (rows 37 290 70 11 152 160 80 128 256), losses := [] }

theorem u9781 : Upper (D 7) (R 7) [36,288,66,3,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9781 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9782 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 68, targets := 32 }], pairs := [(0,7),(2,5),(2,7),(3,7)], upper := (rows 37 290 70 11 208 160 65 152 280), lower := (rows 37 290 70 11 208 160 65 128 256), losses := [] }

theorem u9782 : Upper (D 7) (R 7) [36,288,66,3,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9783 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 70 11 208 160 72 145 273), lower := (rows 37 290 70 11 208 160 72 128 256), losses := [] }

theorem u9783 : Upper (D 7) (R 7) [36,288,66,3,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9783 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9784 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 290 70 11 208 160 80 137 265), lower := (rows 37 290 70 11 208 160 80 128 256), losses := [] }

theorem u9784 : Upper (D 7) (R 7) [36,288,66,3,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9784 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9785 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 70 25 26 160 65 192 448), lower := (rows 37 290 70 25 26 160 65 128 256), losses := [] }

theorem u9785 : Upper (D 7) (R 7) [36,288,66,17,10,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9786 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(2,0),(2,5)], upper := (rows 37 290 70 25 26 160 192 193 321), lower := (rows 37 290 70 25 26 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 224 224 128 256), good := (rows 100 358 102 24 30 224 224 224 256) },{ target := 5, region := (rows 1 2 22 8 16 0 249 137 265), good := (rows 453 326 70 477 478 192 192 192 256) },{ target := 6, region := (rows 5 2 4 13 20 224 0 128 256), good := (rows 61 290 63 25 26 160 160 160 256) }] }

theorem u9786 : Upper (D 7) (R 7) [36,288,66,17,10,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9787 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 37 290 70 25 88 160 65 130 386), lower := (rows 37 290 70 25 88 160 65 128 256), losses := [] }

theorem u9787 : Upper (D 7) (R 7) [36,288,66,17,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9788 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 70 25 88 160 66 129 385), lower := (rows 37 290 70 25 88 160 66 128 256), losses := [] }

theorem u9788 : Upper (D 7) (R 7) [36,288,66,17,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9789 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,6),(1,6),(1,7),(2,0)], upper := (rows 37 290 70 25 88 160 192 131 259), lower := (rows 37 290 70 25 88 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 224 224 128 256), good := (rows 100 358 102 24 120 224 224 224 256) }] }

theorem u9789 : Upper (D 7) (R 7) [36,288,66,17,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9790 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 70 25 146 33 72 192 448), lower := (rows 37 290 70 25 146 33 72 128 256), losses := [] }

theorem u9790 : Upper (D 7) (R 7) [36,288,66,17,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9790 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9791 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 290 70 25 146 33 192 200 328), lower := (rows 37 290 70 25 146 33 192 128 256), losses := [] }

theorem u9791 : Upper (D 7) (R 7) [36,288,66,17,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9792 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 70 25 146 40 65 192 448), lower := (rows 37 290 70 25 146 40 65 128 256), losses := [] }

theorem u9792 : Upper (D 7) (R 7) [36,288,66,17,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9792 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9793 : Route 9 := (fun mask => (mask,id))

def c9793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9793 : Upper (D 7) (R 7) [36,288,66,17,130,8,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,130,8,128] 13 (by decide) (choices 1) [1,64] r9793 c9793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u765
  · exact u766

def b9794 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 37 290 70 25 146 160 65 200 328), lower := (rows 37 290 70 25 146 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 20 0 73 201 329), good := (rows 477 258 470 473 146 128 457 128 256) }] }

theorem u9794 : Upper (D 7) (R 7) [36,288,66,17,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9795 : Route 9 := (fun mask => (mask,id))

def c9795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9795 : Upper (D 7) (R 7) [36,288,66,17,130,128,8] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,130,128,8] 13 (by decide) (choices 1) [1,64] r9795 c9795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u767
  · exact u768

def b9796 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 6, region := 418, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 290 70 25 152 160 65 194 322), lower := (rows 37 290 70 25 152 160 65 128 256), losses := [] }

theorem u9796 : Upper (D 7) (R 7) [36,288,66,17,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9797 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 5, region := 327, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 37 290 70 25 152 160 66 193 321), lower := (rows 37 290 70 25 152 160 66 128 256), losses := [] }

theorem u9797 : Upper (D 7) (R 7) [36,288,66,17,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9798 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(4,0)], upper := (rows 37 290 70 25 208 40 65 130 386), lower := (rows 37 290 70 25 208 40 65 128 256), losses := [] }

theorem u9798 : Upper (D 7) (R 7) [36,288,66,17,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9798 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9799 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 290 70 25 208 40 66 129 385), lower := (rows 37 290 70 25 208 40 66 128 256), losses := [] }

theorem u9799 : Upper (D 7) (R 7) [36,288,66,17,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9799 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9800 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 290 70 25 208 40 192 131 259), lower := (rows 37 290 70 25 208 40 192 128 256), losses := [] }

theorem u9800 : Upper (D 7) (R 7) [36,288,66,17,192,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9800 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9801 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 418, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 37 290 70 25 208 160 65 138 266), lower := (rows 37 290 70 25 208 160 65 128 256), losses := [] }

theorem u9801 : Upper (D 7) (R 7) [36,288,66,17,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9802 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 290 70 25 208 160 66 137 265), lower := (rows 37 290 70 25 208 160 66 128 256), losses := [] }

theorem u9802 : Upper (D 7) (R 7) [36,288,66,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9803 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,6),(1,6),(1,7)], upper := (rows 37 290 70 25 208 160 72 131 259), lower := (rows 37 290 70 25 208 160 72 128 256), losses := [] }

theorem u9803 : Upper (D 7) (R 7) [36,288,66,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9803 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9804 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 70 26 81 160 65 136 392), lower := (rows 37 290 70 26 81 160 65 128 256), losses := [] }

theorem u9804 : Upper (D 7) (R 7) [36,288,66,18,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9805 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 70 26 81 160 72 129 385), lower := (rows 37 290 70 26 81 160 72 128 256), losses := [] }

theorem u9805 : Upper (D 7) (R 7) [36,288,66,18,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9805 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9806 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(0,1),(1,6),(2,0),(3,6)], upper := (rows 37 290 70 26 81 160 192 137 265), lower := (rows 37 290 70 26 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 224 224 128 256), good := (rows 100 358 102 30 112 224 224 224 256) },{ target := 1, region := (rows 5 0 4 8 21 224 224 128 256), good := (rows 117 352 117 24 113 224 224 224 256) }] }

theorem u9806 : Upper (D 7) (R 7) [36,288,66,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9807 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,5),(2,7),(3,5)], upper := (rows 37 290 70 26 145 160 65 200 328), lower := (rows 37 290 70 26 145 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 12 12 81 0 81 141 269), good := (rows 477 258 478 478 465 128 465 128 256) }] }

theorem u9807 : Upper (D 7) (R 7) [36,288,66,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9808 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 290 70 26 145 160 72 193 321), lower := (rows 37 290 70 26 145 160 72 128 256), losses := [] }

theorem u9808 : Upper (D 7) (R 7) [36,288,66,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9808 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9809 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 152, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 70 26 208 33 65 136 392), lower := (rows 37 290 70 26 208 33 65 128 256), losses := [] }

theorem u9809 : Upper (D 7) (R 7) [36,288,66,18,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9810 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 290 70 26 208 33 72 129 385), lower := (rows 37 290 70 26 208 33 72 128 256), losses := [] }

theorem u9810 : Upper (D 7) (R 7) [36,288,66,18,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9810 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9811 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 290 70 26 208 33 192 137 265), lower := (rows 37 290 70 26 208 33 192 128 256), losses := [] }

theorem u9811 : Upper (D 7) (R 7) [36,288,66,18,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9812 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 37 290 70 26 208 160 65 137 265), lower := (rows 37 290 70 26 208 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 81 0 65 129 257), good := (rows 477 258 94 26 208 128 465 128 256) }] }

theorem u9812 : Upper (D 7) (R 7) [36,288,66,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9813 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 290 70 26 208 160 72 129 257), lower := (rows 37 290 70 26 208 160 72 128 256), losses := [] }

theorem u9813 : Upper (D 7) (R 7) [36,288,66,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9813 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9814 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 70 73 145 48 66 136 392), lower := (rows 37 290 70 73 145 48 66 128 256), losses := [] }

theorem u9814 : Upper (D 7) (R 7) [36,288,66,65,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9814 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9815 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 37 290 70 73 145 48 72 130 386), lower := (rows 37 290 70 73 145 48 72 128 256), losses := [] }

theorem u9815 : Upper (D 7) (R 7) [36,288,66,65,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9815 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9816 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 37 290 70 73 145 48 192 138 266), lower := (rows 37 290 70 73 145 48 192 128 256), losses := [] }

theorem u9816 : Upper (D 7) (R 7) [36,288,66,65,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9816 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9817 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 290 70 73 145 160 66 152 280), lower := (rows 37 290 70 73 145 160 66 128 256), losses := [] }

theorem u9817 : Upper (D 7) (R 7) [36,288,66,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9818 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 290 70 73 145 160 72 146 274), lower := (rows 37 290 70 73 145 160 72 128 256), losses := [] }

theorem u9818 : Upper (D 7) (R 7) [36,288,66,65,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9818 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9819 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 37 290 70 73 145 160 80 138 266), lower := (rows 37 290 70 73 145 160 80 128 256), losses := [] }

theorem u9819 : Upper (D 7) (R 7) [36,288,66,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9819 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9820 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 70 73 146 160 65 152 280), lower := (rows 37 290 70 73 146 160 65 128 256), losses := [] }

theorem u9820 : Upper (D 7) (R 7) [36,288,66,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9821 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 290 70 73 146 160 72 145 273), lower := (rows 37 290 70 73 146 160 72 128 256), losses := [] }

theorem u9821 : Upper (D 7) (R 7) [36,288,66,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9821 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9822 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(3,1)], upper := (rows 37 290 70 73 146 160 80 137 265), lower := (rows 37 290 70 73 146 160 80 128 256), losses := [] }

theorem u9822 : Upper (D 7) (R 7) [36,288,66,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9822 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9823 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 290 70 73 152 48 65 130 386), lower := (rows 37 290 70 73 152 48 65 128 256), losses := [] }

theorem u9823 : Upper (D 7) (R 7) [36,288,66,65,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9823 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9824 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 70 73 152 48 66 129 385), lower := (rows 37 290 70 73 152 48 66 128 256), losses := [] }

theorem u9824 : Upper (D 7) (R 7) [36,288,66,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9824 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9825 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(4,6)], upper := (rows 37 290 70 73 152 48 192 131 259), lower := (rows 37 290 70 73 152 48 192 128 256), losses := [] }

theorem u9825 : Upper (D 7) (R 7) [36,288,66,65,136,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9825 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9826 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 290 70 73 152 160 65 146 274), lower := (rows 37 290 70 73 152 160 65 128 256), losses := [] }

theorem u9826 : Upper (D 7) (R 7) [36,288,66,65,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9827 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 290 70 73 152 160 66 145 273), lower := (rows 37 290 70 73 152 160 66 128 256), losses := [] }

theorem u9827 : Upper (D 7) (R 7) [36,288,66,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9828 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,6),(1,6),(1,7)], upper := (rows 37 290 70 73 152 160 80 131 259), lower := (rows 37 290 70 73 152 160 80 128 256), losses := [] }

theorem u9828 : Upper (D 7) (R 7) [36,288,66,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9828 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9829 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,6),(4,6)], upper := (rows 37 290 70 88 145 40 65 130 386), lower := (rows 37 290 70 88 145 40 65 128 256), losses := [] }

theorem u9829 : Upper (D 7) (R 7) [36,288,66,80,129,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9829 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9830 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 290 70 88 145 40 66 129 385), lower := (rows 37 290 70 88 145 40 66 128 256), losses := [] }

theorem u9830 : Upper (D 7) (R 7) [36,288,66,80,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9830 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9831 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 290 70 88 145 40 192 131 259), lower := (rows 37 290 70 88 145 40 192 128 256), losses := [] }

theorem u9831 : Upper (D 7) (R 7) [36,288,66,80,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9831 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9832 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 422, targets := 1 }], pairs := [(0,7),(1,0),(2,0),(2,7)], upper := (rows 37 290 70 88 145 160 65 138 266), lower := (rows 37 290 70 88 145 160 65 128 256), losses := [] }

theorem u9832 : Upper (D 7) (R 7) [36,288,66,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9833 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 290 70 88 145 160 66 137 265), lower := (rows 37 290 70 88 145 160 66 128 256), losses := [] }

theorem u9833 : Upper (D 7) (R 7) [36,288,66,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9834 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 37 290 70 88 145 160 72 131 259), lower := (rows 37 290 70 88 145 160 72 128 256), losses := [] }

theorem u9834 : Upper (D 7) (R 7) [36,288,66,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9834 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9835 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 152, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 70 88 146 33 65 136 392), lower := (rows 37 290 70 88 146 33 65 128 256), losses := [] }

theorem u9835 : Upper (D 7) (R 7) [36,288,66,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9836 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 290 70 88 146 33 72 129 385), lower := (rows 37 290 70 88 146 33 72 128 256), losses := [] }

theorem u9836 : Upper (D 7) (R 7) [36,288,66,80,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9836 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9837 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 290 70 88 146 33 192 137 265), lower := (rows 37 290 70 88 146 33 192 128 256), losses := [] }

theorem u9837 : Upper (D 7) (R 7) [36,288,66,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9838 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 70 88 146 40 65 129 385), lower := (rows 37 290 70 88 146 40 65 128 256), losses := [] }

theorem u9838 : Upper (D 7) (R 7) [36,288,66,80,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9838 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9839 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 290 70 88 146 40 192 129 257), lower := (rows 37 290 70 88 146 40 192 128 256), losses := [] }

theorem u9839 : Upper (D 7) (R 7) [36,288,66,80,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9839 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9839
end Delivery.IrregularNine14.P07
