import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0011

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8820 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 200 112 288 86 150 278), lower := (rows 7 11 37 200 112 288 64 128 256), losses := [] }

theorem u8820 : Upper (D 6) (R 6) [6,9,33,192,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8820 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8821 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 200 274 36 112 240 368), lower := (rows 7 11 37 200 274 36 64 128 256), losses := [] }

theorem u8821 : Upper (D 6) (R 6) [6,9,33,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8822 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 200 274 48 100 228 356), lower := (rows 7 11 37 200 274 48 64 128 256), losses := [] }

theorem u8822 : Upper (D 6) (R 6) [6,9,33,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8822 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8823 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 200 274 96 116 180 308), lower := (rows 7 11 37 200 274 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 24 16 120 80 144 272), good := (rows 5 45 37 232 508 96 96 128 256) }] }

theorem u8823 : Upper (D 6) (R 6) [6,9,33,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8824 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 200 276 34 112 240 368), lower := (rows 7 11 37 200 276 34 64 128 256), losses := [] }

theorem u8824 : Upper (D 6) (R 6) [6,9,33,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8825 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 200 276 48 98 226 354), lower := (rows 7 11 37 200 276 48 64 128 256), losses := [] }

theorem u8825 : Upper (D 6) (R 6) [6,9,33,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8825 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8826 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 200 276 96 114 178 306), lower := (rows 7 11 37 200 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 8 16 104 64 128 256), good := (rows 5 45 37 232 276 96 96 128 256) }] }

theorem u8826 : Upper (D 6) (R 6) [6,9,33,192,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8827 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 200 304 34 84 212 340), lower := (rows 7 11 37 200 304 34 64 128 256), losses := [] }

theorem u8827 : Upper (D 6) (R 6) [6,9,33,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8828 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 200 304 36 82 210 338), lower := (rows 7 11 37 200 304 36 64 128 256), losses := [] }

theorem u8828 : Upper (D 6) (R 6) [6,9,33,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8829 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 37 200 304 48 70 198 326), lower := (rows 7 11 37 200 304 48 64 128 256), losses := [] }

theorem u8829 : Upper (D 6) (R 6) [6,9,33,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8829 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8830 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 200 304 96 86 150 278), lower := (rows 7 11 37 200 304 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 8 16 104 64 128 256), good := (rows 5 45 37 232 304 96 96 128 256) }] }

theorem u8830 : Upper (D 6) (R 6) [6,9,33,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8831 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 200 336 34 116 180 308), lower := (rows 7 11 37 200 336 34 64 128 256), losses := [] }

theorem u8831 : Upper (D 6) (R 6) [6,9,33,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8832 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 200 336 36 114 178 306), lower := (rows 7 11 37 200 336 36 64 128 256), losses := [] }

theorem u8832 : Upper (D 6) (R 6) [6,9,33,192,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8833 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 200 336 48 102 166 294), lower := (rows 7 11 37 200 336 48 64 128 256), losses := [] }

theorem u8833 : Upper (D 6) (R 6) [6,9,33,192,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8833 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8834 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 392 82 36 112 240 368), lower := (rows 7 11 37 392 82 36 64 128 256), losses := [] }

theorem u8834 : Upper (D 6) (R 6) [6,9,33,384,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8835 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 392 82 48 100 228 356), lower := (rows 7 11 37 392 82 48 64 128 256), losses := [] }

theorem u8835 : Upper (D 6) (R 6) [6,9,33,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8835 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8836 : Route 9 := (fun mask => (mask,id))

def c8836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8836 : Upper (D 6) (R 6) [6,9,33,384,66,64] 13 := by
  apply FastRouting.sound _ _ [6,9,33,384,66,64] 13 (by decide) (choices 1) [4,16,32] r8836 c8836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u682
  · exact u683
  · exact u684

def b8837 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 392 84 34 112 240 368), lower := (rows 7 11 37 392 84 34 64 128 256), losses := [] }

theorem u8837 : Upper (D 6) (R 6) [6,9,33,384,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8838 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 392 84 48 98 226 354), lower := (rows 7 11 37 392 84 48 64 128 256), losses := [] }

theorem u8838 : Upper (D 6) (R 6) [6,9,33,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8838 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8839 : Route 9 := (fun mask => (mask,id))

def c8839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8839 : Upper (D 6) (R 6) [6,9,33,384,68,64] 13 := by
  apply FastRouting.sound _ _ [6,9,33,384,68,64] 13 (by decide) (choices 1) [2,16,32] r8839 c8839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u685
  · exact u686
  · exact u687

def b8840 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 392 112 34 84 212 340), lower := (rows 7 11 37 392 112 34 64 128 256), losses := [] }

theorem u8840 : Upper (D 6) (R 6) [6,9,33,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8841 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 11 37 392 112 36 82 210 338), lower := (rows 7 11 37 392 112 36 64 128 256), losses := [] }

theorem u8841 : Upper (D 6) (R 6) [6,9,33,384,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8842 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 37 392 112 48 70 198 326), lower := (rows 7 11 37 392 112 48 64 128 256), losses := [] }

theorem u8842 : Upper (D 6) (R 6) [6,9,33,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8842 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8843 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 392 112 96 86 150 278), lower := (rows 7 11 37 392 112 96 64 128 256), losses := [] }

theorem u8843 : Upper (D 6) (R 6) [6,9,33,384,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8844 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 74 208 33 356 420 292), lower := (rows 7 11 52 74 208 33 64 128 256), losses := [] }

theorem u8844 : Upper (D 6) (R 6) [6,9,48,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8845 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 74 208 36 353 417 289), lower := (rows 7 11 52 74 208 36 64 128 256), losses := [] }

theorem u8845 : Upper (D 6) (R 6) [6,9,48,66,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8846 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 52 74 208 288 101 165 293), lower := (rows 7 11 52 74 208 288 64 128 256), losses := [] }

theorem u8846 : Upper (D 6) (R 6) [6,9,48,66,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8846 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8847 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 74 400 33 100 228 356), lower := (rows 7 11 52 74 400 33 64 128 256), losses := [] }

theorem u8847 : Upper (D 6) (R 6) [6,9,48,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8848 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 74 400 36 97 225 353), lower := (rows 7 11 52 74 400 36 64 128 256), losses := [] }

theorem u8848 : Upper (D 6) (R 6) [6,9,48,66,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8849 : Route 9 := (fun mask => (mask,id))

def c8849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8849 : Upper (D 6) (R 6) [6,9,48,66,384,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,66,384,64] 13 (by decide) (choices 1) [1,4,32] r8849 c8849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u688
  · exact u689
  · exact u690

def b8850 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 7 11 52 104 146 33 324 452 324), lower := (rows 7 11 52 104 146 33 64 128 256), losses := [] }

theorem u8850 : Upper (D 6) (R 6) [6,9,48,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8851 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 11 52 104 146 36 321 449 321), lower := (rows 7 11 52 104 146 36 64 128 256), losses := [] }

theorem u8851 : Upper (D 6) (R 6) [6,9,48,96,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8852 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 52 104 146 96 325 389 261), lower := (rows 7 11 52 104 146 96 64 128 256), losses := [] }

theorem u8852 : Upper (D 6) (R 6) [6,9,48,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8853 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 360, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(3,1),(4,5)], upper := (rows 7 11 52 104 146 288 69 197 325), lower := (rows 7 11 52 104 146 288 64 128 256), losses := [] }

theorem u8853 : Upper (D 6) (R 6) [6,9,48,96,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8853 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8854 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 52 104 208 33 326 390 262), lower := (rows 7 11 52 104 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 51 32 67 131 259), good := (rows 470 478 60 124 208 508 64 128 256) }] }

theorem u8854 : Upper (D 6) (R 6) [6,9,48,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8855 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 464, targets := 34 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 52 104 208 34 325 389 261), lower := (rows 7 11 52 104 208 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 44 40 51 32 67 131 259), good := (rows 469 477 60 124 208 508 64 128 256) }] }

theorem u8855 : Upper (D 6) (R 6) [6,9,48,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8856 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 52 104 208 36 323 387 259), lower := (rows 7 11 52 104 208 36 64 128 256), losses := [] }

theorem u8856 : Upper (D 6) (R 6) [6,9,48,96,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8857 : Route 9 := (fun mask => (mask,id))

def c8857 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8857 : Upper (D 6) (R 6) [6,9,48,96,192,256] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,192,256] 13 (by decide) (choices 1) [1,2,4] r8857 c8857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u691
  · exact u692
  · exact u693

def b8858 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 52 104 400 33 70 198 326), lower := (rows 7 11 52 104 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 51 32 67 131 259), good := (rows 470 478 60 124 400 508 64 128 256) }] }

theorem u8858 : Upper (D 6) (R 6) [6,9,48,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8859 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 464, targets := 34 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 52 104 400 34 69 197 325), lower := (rows 7 11 52 104 400 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 44 40 51 32 67 131 259), good := (rows 469 477 60 124 400 508 64 128 256) }] }

theorem u8859 : Upper (D 6) (R 6) [6,9,48,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8860 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 104 400 36 67 195 323), lower := (rows 7 11 52 104 400 36 64 128 256), losses := [] }

theorem u8860 : Upper (D 6) (R 6) [6,9,48,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8861 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 52 104 400 96 71 135 263), lower := (rows 7 11 52 104 400 96 64 128 256), losses := [] }

theorem u8861 : Upper (D 6) (R 6) [6,9,48,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8862 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 138 336 33 100 228 356), lower := (rows 7 11 52 138 336 33 64 128 256), losses := [] }

theorem u8862 : Upper (D 6) (R 6) [6,9,48,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8863 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 138 336 36 97 225 353), lower := (rows 7 11 52 138 336 36 64 128 256), losses := [] }

theorem u8863 : Upper (D 6) (R 6) [6,9,48,130,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8864 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 52 138 336 96 101 165 293), lower := (rows 7 11 52 138 336 96 64 128 256), losses := [] }

theorem u8864 : Upper (D 6) (R 6) [6,9,48,130,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8865 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 456, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 7 11 52 168 82 33 324 452 324), lower := (rows 7 11 52 168 82 33 64 128 256), losses := [] }

theorem u8865 : Upper (D 6) (R 6) [6,9,48,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8866 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 11 52 168 82 36 321 449 321), lower := (rows 7 11 52 168 82 36 64 128 256), losses := [] }

theorem u8866 : Upper (D 6) (R 6) [6,9,48,160,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8867 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 52 168 82 96 325 389 261), lower := (rows 7 11 52 168 82 96 64 128 256), losses := [] }

theorem u8867 : Upper (D 6) (R 6) [6,9,48,160,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8868 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 488, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(4,5)], upper := (rows 7 11 52 168 82 288 69 197 325), lower := (rows 7 11 52 168 82 288 64 128 256), losses := [] }

theorem u8868 : Upper (D 6) (R 6) [6,9,48,160,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8868 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8869 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 200, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 7 11 52 168 274 33 68 196 324), lower := (rows 7 11 52 168 274 33 64 128 256), losses := [] }

theorem u8869 : Upper (D 6) (R 6) [6,9,48,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8870 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 11 52 168 274 36 65 193 321), lower := (rows 7 11 52 168 274 36 64 128 256), losses := [] }

theorem u8870 : Upper (D 6) (R 6) [6,9,48,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8871 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 11 52 168 274 96 69 197 325), lower := (rows 7 11 52 168 274 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 11 16 99 65 129 257), good := (rows 493 489 52 168 316 96 96 128 256) }] }

theorem u8871 : Upper (D 6) (R 6) [6,9,48,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8872 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 52 168 336 33 70 198 326), lower := (rows 7 11 52 168 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 51 32 67 131 259), good := (rows 470 478 60 188 336 508 64 128 256) }] }

theorem u8872 : Upper (D 6) (R 6) [6,9,48,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8873 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 336, targets := 34 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 52 168 336 34 69 197 325), lower := (rows 7 11 52 168 336 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 44 40 51 32 67 131 259), good := (rows 469 477 60 188 336 508 64 128 256) }] }

theorem u8873 : Upper (D 6) (R 6) [6,9,48,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8874 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 168 336 36 67 195 323), lower := (rows 7 11 52 168 336 36 64 128 256), losses := [] }

theorem u8874 : Upper (D 6) (R 6) [6,9,48,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8875 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 52 168 336 96 71 135 263), lower := (rows 7 11 52 168 336 96 64 128 256), losses := [] }

theorem u8875 : Upper (D 6) (R 6) [6,9,48,160,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8876 : Route 9 := (fun mask => (mask,id))

def c8876 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8876 : Upper (D 6) (R 6) [6,9,48,192,68,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,68,1] 13 (by decide) (choices 1) [2,32,256] r8876 c8876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u694
  · exact u695
  · exact u696

def r8877 : Route 9 := (fun mask => (mask,id))

def c8877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8877 : Upper (D 6) (R 6) [6,9,48,192,68,2] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,68,2] 13 (by decide) (choices 1) [1,32,256] r8877 c8877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u697
  · exact u698
  · exact u699

def b8878 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 52 200 84 288 99 163 291), lower := (rows 7 11 52 200 84 288 64 128 256), losses := [] }

theorem u8878 : Upper (D 6) (R 6) [6,9,48,192,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8878 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8879 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 200, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 11 52 200 273 34 100 228 356), lower := (rows 7 11 52 200 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 31 16 35 85 149 277), good := (rows 494 490 508 200 508 42 64 128 256) }] }

theorem u8879 : Upper (D 6) (R 6) [6,9,48,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8879
end Delivery.IrregularNine14.P06
