import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0161
import IrregularNine14P07C0162

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r26820 : Route 9 := (fun mask => (mask,id))

def c26820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26820 : Upper (D 7) (R 7) [36,288,10,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,10,80,130,128] 13 (by decide) (choices 1) [1] r26820 c26820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u9710

def b26821 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 290 14 200 19 33 208 208 464), lower := (rows 37 290 14 200 19 33 64 128 256), losses := [] }

theorem u26821 : Upper (D 7) (R 7) [36,288,10,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26822 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 290 14 200 19 48 193 193 449), lower := (rows 37 290 14 200 19 48 64 128 256), losses := [] }

theorem u26822 : Upper (D 7) (R 7) [36,288,10,192,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26822 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26823 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 4, region := 204, targets := 32 }], pairs := [(1,6),(2,5),(3,5),(4,6)], upper := (rows 37 290 14 200 19 96 209 145 401), lower := (rows 37 290 14 200 19 96 64 128 256), losses := [] }

theorem u26823 : Upper (D 7) (R 7) [36,288,10,192,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26824 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 418, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 290 14 200 81 33 210 146 402), lower := (rows 37 290 14 200 81 33 64 128 256), losses := [] }

theorem u26824 : Upper (D 7) (R 7) [36,288,10,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26825 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 290 14 200 81 34 209 145 401), lower := (rows 37 290 14 200 81 34 64 128 256), losses := [] }

theorem u26825 : Upper (D 7) (R 7) [36,288,10,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26826 : Route 9 := (fun mask => (mask,id))

def c26826 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26826 : Upper (D 7) (R 7) [36,288,10,192,65,16] 13 := by
  apply FastRouting.sound _ _ [36,288,10,192,65,16] 13 (by decide) (choices 1) [1,2,128] r26826 c26826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9711
  · exact u9712
  · exact u9713

def b26827 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(1,7),(4,7)], upper := (rows 37 290 14 200 81 160 83 147 275), lower := (rows 37 290 14 200 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 288 45 232 81 160 64 160 256) }] }

theorem u26827 : Upper (D 7) (R 7) [36,288,10,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26828 : Route 9 := (fun mask => (mask,id))

def c26828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26828 : Upper (D 7) (R 7) [36,288,10,192,66,1] 13 := by
  apply FastRouting.sound _ _ [36,288,10,192,66,1] 13 (by decide) (choices 1) [1,16,128] r26828 c26828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9714
  · exact u9715
  · exact u9716

def b26829 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6),(3,1),(3,5)], upper := (rows 37 290 14 200 82 48 193 129 385), lower := (rows 37 290 14 200 82 48 64 128 256), losses := [] }

theorem u26829 : Upper (D 7) (R 7) [36,288,10,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26829 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26830 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 290 14 200 82 160 81 145 273), lower := (rows 37 290 14 200 82 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 288 45 232 80 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 290 47 168 18 160 0 160 256) }] }

theorem u26830 : Upper (D 7) (R 7) [36,288,10,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26831 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 290 28 11 81 34 192 192 448), lower := (rows 37 290 28 11 81 34 64 128 256), losses := [] }

theorem u26831 : Upper (D 7) (R 7) [36,288,24,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26832 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,6),(2,5),(3,6),(4,5)], upper := (rows 37 290 28 11 81 96 194 130 386), lower := (rows 37 290 28 11 81 96 64 128 256), losses := [] }

theorem u26832 : Upper (D 7) (R 7) [36,288,24,3,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26833 : Route 9 := (fun mask => (mask,id))

def c26833 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26833 : Upper (D 7) (R 7) [36,288,24,3,65,128] 13 := by
  apply FastRouting.sound _ _ [36,288,24,3,65,128] 13 (by decide) (choices 1) [2,128] r26833 c26833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9717
  · exact u9718

def b26834 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 28 11 82 33 192 192 448), lower := (rows 37 290 28 11 82 33 64 128 256), losses := [] }

theorem u26834 : Upper (D 7) (R 7) [36,288,24,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26835 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 37 290 28 11 82 96 193 129 385), lower := (rows 37 290 28 11 82 96 64 128 256), losses := [] }

theorem u26835 : Upper (D 7) (R 7) [36,288,24,3,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26836 : Route 9 := (fun mask => (mask,id))

def c26836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26836 : Upper (D 7) (R 7) [36,288,24,3,66,128] 13 := by
  apply FastRouting.sound _ _ [36,288,24,3,66,128] 13 (by decide) (choices 1) [1,128] r26836 c26836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9719
  · exact u9720

def b26837 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 28 11 208 33 194 194 450), lower := (rows 37 290 28 11 208 33 64 128 256), losses := [] }

theorem u26837 : Upper (D 7) (R 7) [36,288,24,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26838 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 290 28 11 208 34 193 193 449), lower := (rows 37 290 28 11 208 34 64 128 256), losses := [] }

theorem u26838 : Upper (D 7) (R 7) [36,288,24,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26839 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 3, region := 212, targets := 32 }], pairs := [(1,6),(2,5),(3,6),(4,5)], upper := (rows 37 290 28 11 208 96 195 131 387), lower := (rows 37 290 28 11 208 96 64 128 256), losses := [] }

theorem u26839 : Upper (D 7) (R 7) [36,288,24,3,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26840 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 28 73 82 33 194 130 386), lower := (rows 37 290 28 73 82 33 64 128 256), losses := [] }

theorem u26840 : Upper (D 7) (R 7) [36,288,24,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26841 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 8, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 290 28 73 82 34 193 129 385), lower := (rows 37 290 28 73 82 34 64 128 256), losses := [] }

theorem u26841 : Upper (D 7) (R 7) [36,288,24,65,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26842 : Route 9 := (fun mask => (mask,id))

def c26842 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26842 : Upper (D 7) (R 7) [36,288,24,65,66,128] 13 := by
  apply FastRouting.sound _ _ [36,288,24,65,66,128] 13 (by decide) (choices 1) [1,2,128] r26842 c26842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9721
  · exact u9722
  · exact u9723

def b26843 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 34, targets := 192 },{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(2,5)], upper := (rows 37 290 28 73 145 34 194 194 450), lower := (rows 37 290 28 73 145 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 29 9 17 0 98 162 290), good := (rows 477 450 28 93 157 450 64 128 256) }] }

theorem u26843 : Upper (D 7) (R 7) [36,288,24,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26844 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(4,6)], upper := (rows 37 290 28 73 145 96 194 130 386), lower := (rows 37 290 28 73 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 288 61 105 145 96 96 128 256) }] }

theorem u26844 : Upper (D 7) (R 7) [36,288,24,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26845 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 290 28 73 146 33 194 194 450), lower := (rows 37 290 28 73 146 33 64 128 256), losses := [] }

theorem u26845 : Upper (D 7) (R 7) [36,288,24,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26846 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 37 290 28 73 146 34 193 193 449), lower := (rows 37 290 28 73 146 34 64 128 256), losses := [] }

theorem u26846 : Upper (D 7) (R 7) [36,288,24,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26847 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 402, targets := 64 }], pairs := [(0,1),(1,6),(2,6),(4,6)], upper := (rows 37 290 28 73 146 96 195 131 387), lower := (rows 37 290 28 73 146 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 288 61 105 144 96 96 128 256) },{ target := 6, region := (rows 1 3 12 8 25 32 0 137 265), good := (rows 439 290 412 415 146 32 0 128 256) }] }

theorem u26847 : Upper (D 7) (R 7) [36,288,24,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26848 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 290 28 73 146 160 67 195 323), lower := (rows 37 290 28 73 146 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 288 61 73 176 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 290 61 9 178 160 0 160 256) }] }

theorem u26848 : Upper (D 7) (R 7) [36,288,24,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26849 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 28 73 208 33 194 130 386), lower := (rows 37 290 28 73 208 33 64 128 256), losses := [] }

theorem u26849 : Upper (D 7) (R 7) [36,288,24,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26850 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 37 290 28 73 208 34 195 131 387), lower := (rows 37 290 28 73 208 34 64 128 256), losses := [] }

theorem u26850 : Upper (D 7) (R 7) [36,288,24,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26851 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 37 290 28 73 208 160 67 131 259), lower := (rows 37 290 28 73 208 160 64 128 256), losses := [] }

theorem u26851 : Upper (D 7) (R 7) [36,288,24,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26852 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 290 28 74 146 33 193 193 449), lower := (rows 37 290 28 74 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 30 10 18 0 97 161 289), good := (rows 453 478 28 94 158 449 64 128 256) }] }

theorem u26852 : Upper (D 7) (R 7) [36,288,24,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26853 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 37 290 28 74 146 96 193 129 385), lower := (rows 37 290 28 74 146 96 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 104 64 0 256), good := (rows 37 290 61 106 18 96 96 0 256) }] }

theorem u26853 : Upper (D 7) (R 7) [36,288,24,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26854 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 290 28 74 208 33 195 131 387), lower := (rows 37 290 28 74 208 33 64 128 256), losses := [] }

theorem u26854 : Upper (D 7) (R 7) [36,288,24,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26855 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 37 290 28 74 208 34 193 129 385), lower := (rows 37 290 28 74 208 34 64 128 256), losses := [] }

theorem u26855 : Upper (D 7) (R 7) [36,288,24,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26856 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(3,7)], upper := (rows 37 290 28 74 208 160 67 131 259), lower := (rows 37 290 28 74 208 160 64 128 256), losses := [] }

theorem u26856 : Upper (D 7) (R 7) [36,288,24,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26857 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(4,0)], upper := (rows 37 290 69 25 26 34 192 192 448), lower := (rows 37 290 69 25 26 34 64 128 256), losses := [] }

theorem u26857 : Upper (D 7) (R 7) [36,288,65,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26858 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 69 25 26 96 194 130 386), lower := (rows 37 290 69 25 26 96 64 128 256), losses := [] }

theorem u26858 : Upper (D 7) (R 7) [36,288,65,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26859 : Route 9 := (fun mask => (mask,id))

def c26859 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26859 : Upper (D 7) (R 7) [36,288,65,17,10,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,17,10,128] 13 (by decide) (choices 1) [2,128] r26859 c26859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9724
  · exact u9725

def b26860 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 8, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 290 69 25 82 34 200 136 392), lower := (rows 37 290 69 25 82 34 64 128 256), losses := [] }

theorem u26860 : Upper (D 7) (R 7) [36,288,65,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26861 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 69 25 82 40 194 130 386), lower := (rows 37 290 69 25 82 40 64 128 256), losses := [] }

theorem u26861 : Upper (D 7) (R 7) [36,288,65,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26861 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26862 : Route 9 := (fun mask => (mask,id))

def c26862 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26862 : Upper (D 7) (R 7) [36,288,65,17,66,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,17,66,128] 13 (by decide) (choices 1) [2,8,128] r26862 c26862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9726
  · exact u9727
  · exact u9728

def b26863 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 290 69 25 146 34 200 200 456), lower := (rows 37 290 69 25 146 34 64 128 256), losses := [] }

theorem u26863 : Upper (D 7) (R 7) [36,288,65,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26864 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 290 69 25 146 40 194 194 450), lower := (rows 37 290 69 25 146 40 64 128 256), losses := [] }

theorem u26864 : Upper (D 7) (R 7) [36,288,65,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26864 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26865 : PairBound 9 := { available := 138, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 69 25 146 96 202 138 394), lower := (rows 37 290 69 25 146 96 64 128 256), losses := [] }

theorem u26865 : Upper (D 7) (R 7) [36,288,65,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26866 : Route 9 := (fun mask => (mask,id))

def c26866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26866 : Upper (D 7) (R 7) [36,288,65,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,17,130,128] 13 (by decide) (choices 1) [2,8] r26866 c26866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9729
  · exact u9730

def b26867 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 290 69 25 152 34 194 194 450), lower := (rows 37 290 69 25 152 34 64 128 256), losses := [] }

theorem u26867 : Upper (D 7) (R 7) [36,288,65,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26868 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 69 25 152 96 194 130 386), lower := (rows 37 290 69 25 152 96 64 128 256), losses := [] }

theorem u26868 : Upper (D 7) (R 7) [36,288,65,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26869 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 290 69 25 152 160 66 194 322), lower := (rows 37 290 69 25 152 160 64 128 256), losses := [] }

theorem u26869 : Upper (D 7) (R 7) [36,288,65,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26870 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 290 69 25 208 34 202 138 394), lower := (rows 37 290 69 25 208 34 64 128 256), losses := [] }

theorem u26870 : Upper (D 7) (R 7) [36,288,65,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26871 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 69 25 208 40 194 130 386), lower := (rows 37 290 69 25 208 40 64 128 256), losses := [] }

theorem u26871 : Upper (D 7) (R 7) [36,288,65,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26871 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26872 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 290 69 25 208 160 74 138 266), lower := (rows 37 290 69 25 208 160 64 128 256), losses := [] }

theorem u26872 : Upper (D 7) (R 7) [36,288,65,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26873 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 69 26 88 33 194 130 386), lower := (rows 37 290 69 26 88 33 64 128 256), losses := [] }

theorem u26873 : Upper (D 7) (R 7) [36,288,65,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26874 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 290 69 26 88 34 193 129 385), lower := (rows 37 290 69 26 88 34 64 128 256), losses := [] }

theorem u26874 : Upper (D 7) (R 7) [36,288,65,18,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26875 : Route 9 := (fun mask => (mask,id))

def c26875 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26875 : Upper (D 7) (R 7) [36,288,65,18,72,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,72,128] 13 (by decide) (choices 1) [1,2,128] r26875 c26875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9731
  · exact u9732
  · exact u9733

def b26876 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 290 69 26 145 34 200 200 456), lower := (rows 37 290 69 26 145 34 64 128 256), losses := [] }

theorem u26876 : Upper (D 7) (R 7) [36,288,65,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26877 : Route 9 := (fun mask => (mask,id))

def c26877 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26877 : Upper (D 7) (R 7) [36,288,65,18,129,8] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,129,8] 13 (by decide) (choices 1) [2,128] r26877 c26877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9734
  · exact u9735

def b26878 : PairBound 9 := { available := 138, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 69 26 145 96 202 138 394), lower := (rows 37 290 69 26 145 96 64 128 256), losses := [] }

theorem u26878 : Upper (D 7) (R 7) [36,288,65,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26879 : Route 9 := (fun mask => (mask,id))

def c26879 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26879 : Upper (D 7) (R 7) [36,288,65,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,129,128] 13 (by decide) (choices 1) [2,8] r26879 c26879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9736
  · exact u9737

#print axioms u26879
end Delivery.IrregularNine14.P07
