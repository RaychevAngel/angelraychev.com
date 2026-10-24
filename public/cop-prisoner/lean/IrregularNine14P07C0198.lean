import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0016

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11880 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 200 304 33 194 194 450), lower := (rows 7 26 37 200 304 33 64 128 256), losses := [] }

theorem u11880 : Upper (D 7) (R 7) [6,24,33,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11881 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 200 304 34 193 193 449), lower := (rows 7 26 37 200 304 34 64 128 256), losses := [] }

theorem u11881 : Upper (D 7) (R 7) [6,24,33,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11882 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,6)], upper := (rows 7 26 37 200 304 96 195 131 387), lower := (rows 7 26 37 200 304 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 20 32 0 129 257), good := (rows 407 26 437 136 304 32 0 128 256) },{ target := 7, region := (rows 3 2 6 8 16 104 64 0 256), good := (rows 7 63 37 104 304 96 96 0 256) }] }

theorem u11882 : Upper (D 7) (R 7) [6,24,33,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11883 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 474, targets := 1 },{ cop := 5, region := 4, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 26 37 200 336 33 226 162 418), lower := (rows 7 26 37 200 336 33 64 128 256), losses := [] }

theorem u11883 : Upper (D 7) (R 7) [6,24,33,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11884 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 200 336 34 225 161 417), lower := (rows 7 26 37 200 336 34 64 128 256), losses := [] }

theorem u11884 : Upper (D 7) (R 7) [6,24,33,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11885 : Route 9 := (fun mask => (mask,id))

def c11885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11885 : Upper (D 7) (R 7) [6,24,33,192,320,128] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,320,128] 13 (by decide) (choices 1) [1,2,32] r11885 c11885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u989
  · exact u990
  · exact u991

def b11886 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 26 100 41 145 34 448 448 448), lower := (rows 7 26 100 41 145 34 64 128 256), losses := [] }

theorem u11886 : Upper (D 7) (R 7) [6,24,96,33,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11887 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 41 145 96 450 386 386), lower := (rows 7 26 100 41 145 96 64 128 256), losses := [] }

theorem u11887 : Upper (D 7) (R 7) [6,24,96,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11888 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 42, targets := 64 }], pairs := [(1,5),(1,6),(3,6),(4,5)], upper := (rows 7 26 100 41 145 160 322 450 322), lower := (rows 7 26 100 41 145 160 64 128 256), losses := [] }

theorem u11888 : Upper (D 7) (R 7) [6,24,96,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11889 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 0, region := 484, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 7 26 100 41 145 288 194 194 450), lower := (rows 7 26 100 41 145 288 64 128 256), losses := [] }

theorem u11889 : Upper (D 7) (R 7) [6,24,96,33,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11889 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11890 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 100 41 208 33 450 386 386), lower := (rows 7 26 100 41 208 33 64 128 256), losses := [] }

theorem u11890 : Upper (D 7) (R 7) [6,24,96,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11891 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 100 41 208 34 449 385 385), lower := (rows 7 26 100 41 208 34 64 128 256), losses := [] }

theorem u11891 : Upper (D 7) (R 7) [6,24,96,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11892 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(1,5),(2,0),(2,1),(4,5)], upper := (rows 7 26 100 41 208 160 323 387 259), lower := (rows 7 26 100 41 208 160 64 128 256), losses := [] }

theorem u11892 : Upper (D 7) (R 7) [6,24,96,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11893 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 0, region := 424, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 7 26 100 41 208 288 195 131 387), lower := (rows 7 26 100 41 208 288 64 128 256), losses := [] }

theorem u11893 : Upper (D 7) (R 7) [6,24,96,33,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11893 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11894 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 26 100 41 273 34 192 192 448), lower := (rows 7 26 100 41 273 34 64 128 256), losses := [] }

theorem u11894 : Upper (D 7) (R 7) [6,24,96,33,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11895 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 41 273 96 194 130 386), lower := (rows 7 26 100 41 273 96 64 128 256), losses := [] }

theorem u11895 : Upper (D 7) (R 7) [6,24,96,33,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11896 : Route 9 := (fun mask => (mask,id))

def c11896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11896 : Upper (D 7) (R 7) [6,24,96,33,257,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,257,128] 13 (by decide) (choices 1) [2,128] r11896 c11896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u992
  · exact u993

def b11897 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 100 41 336 33 194 130 386), lower := (rows 7 26 100 41 336 33 64 128 256), losses := [] }

theorem u11897 : Upper (D 7) (R 7) [6,24,96,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11898 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 100 41 336 34 193 129 385), lower := (rows 7 26 100 41 336 34 64 128 256), losses := [] }

theorem u11898 : Upper (D 7) (R 7) [6,24,96,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11899 : Route 9 := (fun mask => (mask,id))

def c11899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11899 : Upper (D 7) (R 7) [6,24,96,33,320,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,320,128] 13 (by decide) (choices 1) [1,2,128] r11899 c11899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u994
  · exact u995
  · exact u996

def b11900 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 26 100 41 400 33 194 194 450), lower := (rows 7 26 100 41 400 33 64 128 256), losses := [] }

theorem u11900 : Upper (D 7) (R 7) [6,24,96,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11901 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 0, region := 40, targets := 192 }], pairs := [(3,6),(3,7),(4,1),(4,5)], upper := (rows 7 26 100 41 400 34 193 193 449), lower := (rows 7 26 100 41 400 34 64 128 256), losses := [] }

theorem u11901 : Upper (D 7) (R 7) [6,24,96,33,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11902 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 41 400 96 195 131 387), lower := (rows 7 26 100 41 400 96 64 128 256), losses := [] }

theorem u11902 : Upper (D 7) (R 7) [6,24,96,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11903 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,5)], upper := (rows 7 26 100 41 400 160 67 195 323), lower := (rows 7 26 100 41 400 160 64 128 256), losses := [{ target := 7, region := (rows 3 2 12 8 16 32 67 0 259), good := (rows 327 351 100 365 272 32 64 0 256) }] }

theorem u11903 : Upper (D 7) (R 7) [6,24,96,33,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11904 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 26 100 42 145 33 448 448 448), lower := (rows 7 26 100 42 145 33 64 128 256), losses := [] }

theorem u11904 : Upper (D 7) (R 7) [6,24,96,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11905 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 42 145 96 449 385 385), lower := (rows 7 26 100 42 145 96 64 128 256), losses := [] }

theorem u11905 : Upper (D 7) (R 7) [6,24,96,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11906 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 26 100 42 145 160 321 449 321), lower := (rows 7 26 100 42 145 160 64 128 256), losses := [] }

theorem u11906 : Upper (D 7) (R 7) [6,24,96,34,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11907 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 26 100 42 145 288 193 193 449), lower := (rows 7 26 100 42 145 288 64 128 256), losses := [] }

theorem u11907 : Upper (D 7) (R 7) [6,24,96,34,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11907 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11908 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 26 100 42 273 33 192 192 448), lower := (rows 7 26 100 42 273 33 64 128 256), losses := [] }

theorem u11908 : Upper (D 7) (R 7) [6,24,96,34,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11909 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 42 273 96 193 129 385), lower := (rows 7 26 100 42 273 96 64 128 256), losses := [] }

theorem u11909 : Upper (D 7) (R 7) [6,24,96,34,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11910 : Route 9 := (fun mask => (mask,id))

def c11910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11910 : Upper (D 7) (R 7) [6,24,96,34,257,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,257,128] 13 (by decide) (choices 1) [1,128] r11910 c11910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u997
  · exact u998

def b11911 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 40, targets := 192 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 26 100 42 400 33 193 193 449), lower := (rows 7 26 100 42 400 33 64 128 256), losses := [] }

theorem u11911 : Upper (D 7) (R 7) [6,24,96,34,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11912 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 42 400 96 193 129 385), lower := (rows 7 26 100 42 400 96 64 128 256), losses := [] }

theorem u11912 : Upper (D 7) (R 7) [6,24,96,34,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11913 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 26 100 42 400 160 65 193 321), lower := (rows 7 26 100 42 400 160 64 128 256), losses := [] }

theorem u11913 : Upper (D 7) (R 7) [6,24,96,34,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11914 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 357, targets := 128 },{ cop := 3, region := 50, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(4,6)], upper := (rows 7 26 100 137 176 33 322 450 322), lower := (rows 7 26 100 137 176 33 64 128 256), losses := [] }

theorem u11914 : Upper (D 7) (R 7) [6,24,96,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11915 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 26 100 137 176 34 321 449 321), lower := (rows 7 26 100 137 176 34 64 128 256), losses := [] }

theorem u11915 : Upper (D 7) (R 7) [6,24,96,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11916 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 137 176 96 323 387 259), lower := (rows 7 26 100 137 176 96 64 128 256), losses := [] }

theorem u11916 : Upper (D 7) (R 7) [6,24,96,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11917 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 357, targets := 128 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,7),(2,7),(3,5)], upper := (rows 7 26 100 137 176 288 67 195 323), lower := (rows 7 26 100 137 176 288 64 128 256), losses := [] }

theorem u11917 : Upper (D 7) (R 7) [6,24,96,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11917 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11918 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,1),(4,1)], upper := (rows 7 26 100 137 273 34 224 224 480), lower := (rows 7 26 100 137 273 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 9 17 32 100 164 292), good := (rows 477 24 484 153 281 484 64 128 256) }] }

theorem u11918 : Upper (D 7) (R 7) [6,24,96,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11919 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 137 273 96 226 162 418), lower := (rows 7 26 100 137 273 96 64 128 256), losses := [] }

theorem u11919 : Upper (D 7) (R 7) [6,24,96,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m11920_2 : Upper (D 7) (R 7) [6,24,96,129,257,128,2] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u999

theorem m11920_32 : Upper (D 7) (R 7) [6,24,96,129,257,128,32] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1000

def r11920 : Route 9 := (fun mask => (mask,id))

def c11920 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11920 : Upper (D 7) (R 7) [6,24,96,129,257,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257,128] 13 (by decide) (choices 1) [2,32] r11920 c11920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11920_2
  · exact m11920_32

def b11921 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 5, region := 196, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(3,1)], upper := (rows 7 26 100 137 274 33 224 224 480), lower := (rows 7 26 100 137 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 36 8 17 32 100 164 292), good := (rows 470 26 484 154 274 500 64 128 256) }] }

theorem u11921 : Upper (D 7) (R 7) [6,24,96,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11922 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 137 274 96 225 161 417), lower := (rows 7 26 100 137 274 96 64 128 256), losses := [] }

theorem u11922 : Upper (D 7) (R 7) [6,24,96,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m11923_1 : Upper (D 7) (R 7) [6,24,96,129,258,128,1] 13 :=
  permutation_upper _ _ _ [6,24,96,129,258,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1001

theorem m11923_32 : Upper (D 7) (R 7) [6,24,96,129,258,128,32] 13 :=
  permutation_upper _ _ _ [6,24,96,129,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1002

def r11923 : Route 9 := (fun mask => (mask,id))

def c11923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11923 : Upper (D 7) (R 7) [6,24,96,129,258,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,258,128] 13 (by decide) (choices 1) [1,32] r11923 c11923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11923_1
  · exact m11923_32

def b11924 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(1,5),(2,0),(3,5),(4,0)], upper := (rows 7 26 100 137 304 33 194 194 450), lower := (rows 7 26 100 137 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 48 32 67 131 259), good := (rows 454 474 116 456 308 500 64 128 256) },{ target := 5, region := (rows 1 18 4 41 16 0 83 147 275), good := (rows 463 474 76 457 474 457 64 128 256) }] }

theorem u11924 : Upper (D 7) (R 7) [6,24,96,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11925 : Route 9 := (fun mask => (mask,id))

def c11925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11925 : Upper (D 7) (R 7) [6,24,96,129,288,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,2] 13 (by decide) (choices 1) [1,128] r11925 c11925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1003
  · exact u1004

def b11926 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 137 304 96 195 131 387), lower := (rows 7 26 100 137 304 96 64 128 256), losses := [] }

theorem u11926 : Upper (D 7) (R 7) [6,24,96,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11927 : Route 9 := (fun mask => (mask,id))

def c11927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11927 : Upper (D 7) (R 7) [6,24,96,129,288,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,128] 13 (by decide) (choices 1) [1,2] r11927 c11927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1005
  · exact u1006

def r11928 : Route 9 := (fun mask => (mask,id))

def c11928 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11928 : Upper (D 7) (R 7) [6,24,96,129,384,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,384,1] 13 (by decide) (choices 1) [2,32] r11928 c11928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1007
  · exact u1008

theorem m11929_1 : Upper (D 7) (R 7) [6,24,96,129,384,2,1] 13 :=
  permutation_upper _ _ _ [6,24,96,129,384,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1007

def r11929 : Route 9 := (fun mask => (mask,id))

def c11929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11929 : Upper (D 7) (R 7) [6,24,96,129,384,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,384,2] 13 (by decide) (choices 1) [1,32] r11929 c11929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11929_1
  · exact u1009

def b11930 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 137 400 96 99 163 291), lower := (rows 7 26 100 137 400 96 64 128 256), losses := [] }

theorem u11930 : Upper (D 7) (R 7) [6,24,96,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11931 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 196, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(4,1)], upper := (rows 7 26 100 138 273 33 224 224 480), lower := (rows 7 26 100 138 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 36 9 16 32 100 164 292), good := (rows 462 26 484 138 282 492 64 128 256) }] }

theorem u11931 : Upper (D 7) (R 7) [6,24,96,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11932 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 138 273 96 225 161 417), lower := (rows 7 26 100 138 273 96 64 128 256), losses := [] }

theorem u11932 : Upper (D 7) (R 7) [6,24,96,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m11933_1 : Upper (D 7) (R 7) [6,24,96,130,257,128,1] 13 :=
  permutation_upper _ _ _ [6,24,96,130,257,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1010

theorem m11933_32 : Upper (D 7) (R 7) [6,24,96,130,257,128,32] 13 :=
  permutation_upper _ _ _ [6,24,96,130,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1011

def r11933 : Route 9 := (fun mask => (mask,id))

def c11933 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11933 : Upper (D 7) (R 7) [6,24,96,130,257,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,257,128] 13 (by decide) (choices 1) [1,32] r11933 c11933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11933_1
  · exact m11933_32

def b11934 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 26 100 138 304 33 193 193 449), lower := (rows 7 26 100 138 304 33 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 25 16 0 97 161 289), good := (rows 463 26 452 138 474 457 64 128 256) }] }

theorem u11934 : Upper (D 7) (R 7) [6,24,96,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11935 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 138 304 96 193 129 385), lower := (rows 7 26 100 138 304 96 64 128 256), losses := [] }

theorem u11935 : Upper (D 7) (R 7) [6,24,96,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11936 : Route 9 := (fun mask => (mask,id))

def c11936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11936 : Upper (D 7) (R 7) [6,24,96,130,288,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,288,128] 13 (by decide) (choices 1) [1] r11936 c11936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u1012

def b11937 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 7 26 100 168 273 33 194 194 450), lower := (rows 7 26 100 168 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 16 32 67 131 259), good := (rows 454 474 108 172 464 492 64 128 256) },{ target := 5, region := (rows 1 10 4 8 49 0 75 139 267), good := (rows 471 474 84 474 465 465 64 128 256) }] }

theorem u11937 : Upper (D 7) (R 7) [6,24,96,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11938 : Route 9 := (fun mask => (mask,id))

def c11938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11938 : Upper (D 7) (R 7) [6,24,96,160,257,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,257,2] 13 (by decide) (choices 1) [1,128] r11938 c11938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1013
  · exact u1014

def b11939 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 168 273 96 195 131 387), lower := (rows 7 26 100 168 273 96 64 128 256), losses := [] }

theorem u11939 : Upper (D 7) (R 7) [6,24,96,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11939
end Delivery.IrregularNine14.P07
