import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0045

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14880 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 104 146 33 208 208 464), lower := (rows 7 266 37 104 146 33 64 128 256), losses := [] }

theorem u14880 : Upper (D 7) (R 7) [6,264,33,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14881 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 266 37 104 146 48 193 193 449), lower := (rows 7 266 37 104 146 48 64 128 256), losses := [] }

theorem u14881 : Upper (D 7) (R 7) [6,264,33,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14881 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14882 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 266 37 104 146 96 209 145 401), lower := (rows 7 266 37 104 146 96 64 128 256), losses := [] }

theorem u14882 : Upper (D 7) (R 7) [6,264,33,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14883 : Route 9 := (fun mask => (mask,id))

def c14883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14883 : Upper (D 7) (R 7) [6,264,33,96,130,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96,130,128] 13 (by decide) (choices 1) [1,16] r14883 c14883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2707
  · exact u2708

def b14884 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 104 208 33 210 146 402), lower := (rows 7 266 37 104 208 33 64 128 256), losses := [] }

theorem u14884 : Upper (D 7) (R 7) [6,264,33,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14885 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 104 208 34 209 145 401), lower := (rows 7 266 37 104 208 34 64 128 256), losses := [] }

theorem u14885 : Upper (D 7) (R 7) [6,264,33,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14886 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 266 37 104 208 48 195 131 387), lower := (rows 7 266 37 104 208 48 64 128 256), losses := [] }

theorem u14886 : Upper (D 7) (R 7) [6,264,33,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14886 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14887 : Route 9 := (fun mask => (mask,id))

def c14887 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14887 : Upper (D 7) (R 7) [6,264,33,96,192,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96,192,128] 13 (by decide) (choices 1) [1,2,16] r14887 c14887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2709
  · exact u2710
  · exact u2711

def b14888 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 200 81 34 240 176 432), lower := (rows 7 266 37 200 81 34 64 128 256), losses := [] }

theorem u14888 : Upper (D 7) (R 7) [6,264,33,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14889 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 36, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 7 266 37 200 81 48 226 162 418), lower := (rows 7 266 37 200 81 48 64 128 256), losses := [] }

theorem u14889 : Upper (D 7) (R 7) [6,264,33,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14889 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14890 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 7 266 37 200 81 160 114 178 306), lower := (rows 7 266 37 200 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 7 303 37 168 17 160 0 160 256) }] }

theorem u14890 : Upper (D 7) (R 7) [6,264,33,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14891 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 200 82 33 240 176 432), lower := (rows 7 266 37 200 82 33 64 128 256), losses := [] }

theorem u14891 : Upper (D 7) (R 7) [6,264,33,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14892 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 37, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 266 37 200 82 48 225 161 417), lower := (rows 7 266 37 200 82 48 64 128 256), losses := [] }

theorem u14892 : Upper (D 7) (R 7) [6,264,33,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14892 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14893 : Route 9 := (fun mask => (mask,id))

def c14893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14893 : Upper (D 7) (R 7) [6,264,33,192,66,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,192,66,128] 13 (by decide) (choices 1) [1,16,32] r14893 c14893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2712
  · exact u2713
  · exact u2714

def b14894 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 200 112 33 210 146 402), lower := (rows 7 266 37 200 112 33 64 128 256), losses := [] }

theorem u14894 : Upper (D 7) (R 7) [6,264,33,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14895 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 200 112 34 209 145 401), lower := (rows 7 266 37 200 112 34 64 128 256), losses := [] }

theorem u14895 : Upper (D 7) (R 7) [6,264,33,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14896 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 37 200 112 48 195 131 387), lower := (rows 7 266 37 200 112 48 64 128 256), losses := [] }

theorem u14896 : Upper (D 7) (R 7) [6,264,33,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14896 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14897 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 7 266 37 200 112 160 83 147 275), lower := (rows 7 266 37 200 112 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 7 303 37 168 48 160 0 160 256) }] }

theorem u14897 : Upper (D 7) (R 7) [6,264,33,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14898 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 52 41 82 33 192 192 448), lower := (rows 7 266 52 41 82 33 64 128 256), losses := [] }

theorem u14898 : Upper (D 7) (R 7) [6,264,48,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14899 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(3,6)], upper := (rows 7 266 52 41 82 96 193 129 385), lower := (rows 7 266 52 41 82 96 64 128 256), losses := [] }

theorem u14899 : Upper (D 7) (R 7) [6,264,48,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14900 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 0, region := 232, targets := 2 }], pairs := [(1,5),(2,1),(3,1),(4,5)], upper := (rows 7 266 52 41 82 160 193 193 449), lower := (rows 7 266 52 41 82 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 9 16 171 73 137 265), good := (rows 493 488 52 489 116 160 64 160 256) }] }

theorem u14900 : Upper (D 7) (R 7) [6,264,48,33,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14901 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 266 52 41 208 33 194 194 450), lower := (rows 7 266 52 41 208 33 64 128 256), losses := [] }

theorem u14901 : Upper (D 7) (R 7) [6,264,48,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14902 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 40, targets := 192 }], pairs := [(3,6),(3,7),(4,1),(4,5)], upper := (rows 7 266 52 41 208 34 193 193 449), lower := (rows 7 266 52 41 208 34 64 128 256), losses := [] }

theorem u14902 : Upper (D 7) (R 7) [6,264,48,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14903 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 266 52 41 208 96 195 131 387), lower := (rows 7 266 52 41 208 96 64 128 256), losses := [] }

theorem u14903 : Upper (D 7) (R 7) [6,264,48,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14904 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 40, targets := 192 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 266 52 42 81 33 192 192 448), lower := (rows 7 266 52 42 81 33 64 128 256), losses := [] }

theorem u14904 : Upper (D 7) (R 7) [6,264,48,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14905 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 0, region := 244, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(3,6)], upper := (rows 7 266 52 42 81 96 193 129 385), lower := (rows 7 266 52 42 81 96 64 128 256), losses := [] }

theorem u14905 : Upper (D 7) (R 7) [6,264,48,34,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14906 : Route 9 := (fun mask => (mask,id))

def c14906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14906 : Upper (D 7) (R 7) [6,264,48,34,65,128] 13 := by
  apply FastRouting.sound _ _ [6,264,48,34,65,128] 13 (by decide) (choices 1) [1,128] r14906 c14906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2715
  · exact u2716

def b14907 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 40, targets := 192 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 266 52 42 208 33 193 193 449), lower := (rows 7 266 52 42 208 33 64 128 256), losses := [] }

theorem u14907 : Upper (D 7) (R 7) [6,264,48,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14908 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 266 52 42 208 96 193 129 385), lower := (rows 7 266 52 42 208 96 64 128 256), losses := [] }

theorem u14908 : Upper (D 7) (R 7) [6,264,48,34,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14909 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 7 266 52 73 145 34 224 224 480), lower := (rows 7 266 52 73 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 127 191 319), good := (rows 486 490 500 490 500 482 64 128 256) },{ target := 1, region := (rows 1 0 4 9 17 32 100 164 292), good := (rows 477 264 500 89 153 480 64 128 256) }] }

theorem u14909 : Upper (D 7) (R 7) [6,264,48,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14910 : Route 9 := (fun mask => (mask,id))

def c14910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14910 : Upper (D 7) (R 7) [6,264,48,65,129,64] 13 := by
  apply FastRouting.sound _ _ [6,264,48,65,129,64] 13 (by decide) (choices 1) [2,32,128] r14910 c14910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2717
  · exact u2718
  · exact u2719

def b14911 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 266 52 73 145 160 98 226 354), lower := (rows 7 266 52 73 145 160 64 128 256), losses := [] }

theorem u14911 : Upper (D 7) (R 7) [6,264,48,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14912 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 52 73 146 33 224 224 480), lower := (rows 7 266 52 73 146 33 64 128 256), losses := [] }

theorem u14912 : Upper (D 7) (R 7) [6,264,48,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14913 : Route 9 := (fun mask => (mask,id))

def c14913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14913 : Upper (D 7) (R 7) [6,264,48,65,130,64] 13 := by
  apply FastRouting.sound _ _ [6,264,48,65,130,64] 13 (by decide) (choices 1) [1,32,128] r14913 c14913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2720
  · exact u2721
  · exact u2722

def b14914 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 266 52 73 146 160 97 225 353), lower := (rows 7 266 52 73 146 160 64 128 256), losses := [] }

theorem u14914 : Upper (D 7) (R 7) [6,264,48,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14915 : Route 9 := (fun mask => (mask,id))

def c14915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14915 : Upper (D 7) (R 7) [6,264,48,65,192,1] 13 := by
  apply FastRouting.sound _ _ [6,264,48,65,192,1] 13 (by decide) (choices 1) [2,32,128] r14915 c14915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2723
  · exact u2724
  · exact u2725

def r14916 : Route 9 := (fun mask => (mask,id))

def c14916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14916 : Upper (D 7) (R 7) [6,264,48,65,192,2] 13 := by
  apply FastRouting.sound _ _ [6,264,48,65,192,2] 13 (by decide) (choices 1) [1,32,128] r14916 c14916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2726
  · exact u2727
  · exact u2728

def b14917 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 266 52 73 208 160 99 163 291), lower := (rows 7 266 52 73 208 160 64 128 256), losses := [] }

theorem u14917 : Upper (D 7) (R 7) [6,264,48,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14918 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 0, region := 244, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(4,7)], upper := (rows 7 266 52 74 81 33 224 160 416), lower := (rows 7 266 52 74 81 33 64 128 256), losses := [] }

theorem u14918 : Upper (D 7) (R 7) [6,264,48,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14919 : Route 9 := (fun mask => (mask,id))

def c14919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14919 : Upper (D 7) (R 7) [6,264,48,66,65,128] 13 := by
  apply FastRouting.sound _ _ [6,264,48,66,65,128] 13 (by decide) (choices 1) [1,32,128] r14919 c14919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2729
  · exact u2730
  · exact u2731

def b14920 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 266 52 74 145 33 224 224 480), lower := (rows 7 266 52 74 145 33 64 128 256), losses := [] }

theorem u14920 : Upper (D 7) (R 7) [6,264,48,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14921 : Route 9 := (fun mask => (mask,id))

def c14921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14921 : Upper (D 7) (R 7) [6,264,48,66,129,64] 13 := by
  apply FastRouting.sound _ _ [6,264,48,66,129,64] 13 (by decide) (choices 1) [1,32,128] r14921 c14921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2732
  · exact u2733
  · exact u2734

def b14922 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 0, region := 244, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 266 52 74 145 160 97 225 353), lower := (rows 7 266 52 74 145 160 64 128 256), losses := [] }

theorem u14922 : Upper (D 7) (R 7) [6,264,48,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14923 : Route 9 := (fun mask => (mask,id))

def c14923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14923 : Upper (D 7) (R 7) [6,264,48,66,192,1] 13 := by
  apply FastRouting.sound _ _ [6,264,48,66,192,1] 13 (by decide) (choices 1) [1,32,128] r14923 c14923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2735
  · exact u2736
  · exact u2737

def b14924 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 266 52 74 208 160 97 161 289), lower := (rows 7 266 52 74 208 160 64 128 256), losses := [] }

theorem u14924 : Upper (D 7) (R 7) [6,264,48,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14925 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 44, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 7 266 52 104 81 33 194 130 386), lower := (rows 7 266 52 104 81 33 64 128 256), losses := [] }

theorem u14925 : Upper (D 7) (R 7) [6,264,48,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14926 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 208, targets := 34 }], pairs := [(2,0),(3,0),(4,1),(4,5)], upper := (rows 7 266 52 104 81 34 193 129 385), lower := (rows 7 266 52 104 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 64 128 256), good := (rows 38 298 60 104 124 34 64 128 256) }] }

theorem u14926 : Upper (D 7) (R 7) [6,264,48,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14927 : Route 9 := (fun mask => (mask,id))

def c14927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14927 : Upper (D 7) (R 7) [6,264,48,96,65,128] 13 := by
  apply FastRouting.sound _ _ [6,264,48,96,65,128] 13 (by decide) (choices 1) [1,2,128] r14927 c14927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2738
  · exact u2739
  · exact u2740

def b14928 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 7 266 52 104 145 33 194 194 450), lower := (rows 7 266 52 104 145 33 64 128 256), losses := [] }

theorem u14928 : Upper (D 7) (R 7) [6,264,48,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14929 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 }], pairs := [(2,0),(3,1),(4,1),(4,5)], upper := (rows 7 266 52 104 145 34 193 193 449), lower := (rows 7 266 52 104 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 35 64 128 256), good := (rows 38 298 52 104 180 34 64 128 256) },{ target := 1, region := (rows 1 0 4 12 17 32 81 145 273), good := (rows 477 264 508 104 465 32 64 128 256) }] }

theorem u14929 : Upper (D 7) (R 7) [6,264,48,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14930 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 266 52 104 145 96 195 131 387), lower := (rows 7 266 52 104 145 96 64 128 256), losses := [] }

theorem u14930 : Upper (D 7) (R 7) [6,264,48,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14931 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 266 52 104 145 160 67 195 323), lower := (rows 7 266 52 104 145 160 64 128 256), losses := [] }

theorem u14931 : Upper (D 7) (R 7) [6,264,48,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14932 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 52 104 146 33 193 193 449), lower := (rows 7 266 52 104 146 33 64 128 256), losses := [] }

theorem u14932 : Upper (D 7) (R 7) [6,264,48,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14933 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 266 52 104 146 96 193 129 385), lower := (rows 7 266 52 104 146 96 64 128 256), losses := [] }

theorem u14933 : Upper (D 7) (R 7) [6,264,48,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14934 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 266 52 104 146 160 65 193 321), lower := (rows 7 266 52 104 146 160 64 128 256), losses := [] }

theorem u14934 : Upper (D 7) (R 7) [6,264,48,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14935 : Route 9 := (fun mask => (mask,id))

def c14935 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14935 : Upper (D 7) (R 7) [6,264,48,96,192,1] 13 := by
  apply FastRouting.sound _ _ [6,264,48,96,192,1] 13 (by decide) (choices 1) [1,2,128] r14935 c14935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2741
  · exact u2742
  · exact u2743

def r14936 : Route 9 := (fun mask => (mask,id))

def c14936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14936 : Upper (D 7) (R 7) [6,264,48,96,192,2] 13 := by
  apply FastRouting.sound _ _ [6,264,48,96,192,2] 13 (by decide) (choices 1) [1,128] r14936 c14936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2744
  · exact u2745

def b14937 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 266 52 104 208 160 67 131 259), lower := (rows 7 266 52 104 208 160 64 128 256), losses := [] }

theorem u14937 : Upper (D 7) (R 7) [6,264,48,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14938 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 7 266 52 200 81 33 226 162 418), lower := (rows 7 266 52 200 81 33 64 128 256), losses := [] }

theorem u14938 : Upper (D 7) (R 7) [6,264,48,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14939 : Route 9 := (fun mask => (mask,id))

def c14939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14939 : Upper (D 7) (R 7) [6,264,48,192,65,2] 13 := by
  apply FastRouting.sound _ _ [6,264,48,192,65,2] 13 (by decide) (choices 1) [1,32,128] r14939 c14939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2746
  · exact u2747
  · exact u2748

#print axioms u14939
end Delivery.IrregularNine14.P07
