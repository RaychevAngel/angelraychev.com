import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0042

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12840 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 196 13 304 96 86 150 278), lower := (rows 11 35 196 13 304 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 100 64 128 256), good := (rows 11 35 224 43 304 96 96 128 256) }] }

theorem u12840 : Upper (D 6) (R 6) [10,33,192,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12841 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 13 336 34 116 180 308), lower := (rows 11 35 196 13 336 34 64 128 256), losses := [] }

theorem u12841 : Upper (D 6) (R 6) [10,33,192,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12842 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 196 13 336 36 114 178 306), lower := (rows 11 35 196 13 336 36 64 128 256), losses := [] }

theorem u12842 : Upper (D 6) (R 6) [10,33,192,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12843 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 196 13 336 48 102 166 294), lower := (rows 11 35 196 13 336 48 64 128 256), losses := [] }

theorem u12843 : Upper (D 6) (R 6) [10,33,192,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12843 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12844 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 25 276 34 100 228 356), lower := (rows 11 35 196 25 276 34 64 128 256), losses := [] }

theorem u12844 : Upper (D 6) (R 6) [10,33,192,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12845 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 196 25 276 36 98 226 354), lower := (rows 11 35 196 25 276 36 64 128 256), losses := [] }

theorem u12845 : Upper (D 6) (R 6) [10,33,192,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12846 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 196 25 276 96 102 166 294), lower := (rows 11 35 196 25 276 96 64 128 256), losses := [{ target := 2, region := (rows 25 18 0 24 16 100 64 128 256), good := (rows 11 35 224 27 315 96 96 128 256) }] }

theorem u12846 : Upper (D 6) (R 6) [10,33,192,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12847 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 25 336 34 100 164 292), lower := (rows 11 35 196 25 336 34 64 128 256), losses := [] }

theorem u12847 : Upper (D 6) (R 6) [10,33,192,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12848 : Route 9 := (fun mask => (mask,id))

def c12848 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12848 : Upper (D 6) (R 6) [10,33,192,17,320,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,17,320,4] 13 (by decide) (choices 1) [2,4,32] r12848 c12848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2550
  · exact u2551
  · exact u2552

def b12849 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 28 273 34 100 228 356), lower := (rows 11 35 196 28 273 34 64 128 256), losses := [] }

theorem u12849 : Upper (D 6) (R 6) [10,33,192,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12850 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 228, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 11 35 196 28 273 36 98 226 354), lower := (rows 11 35 196 28 273 36 64 128 256), losses := [] }

theorem u12850 : Upper (D 6) (R 6) [10,33,192,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12851 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(0,2),(2,0),(3,0)], upper := (rows 11 35 196 28 273 96 102 166 294), lower := (rows 11 35 196 28 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 119 67 131 259), good := (rows 494 486 228 60 508 96 96 128 256) },{ target := 2, region := (rows 9 10 0 8 16 100 64 128 256), good := (rows 11 35 224 59 273 96 96 128 256) }] }

theorem u12851 : Upper (D 6) (R 6) [10,33,192,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12852 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 28 274 33 100 228 356), lower := (rows 11 35 196 28 274 33 64 128 256), losses := [] }

theorem u12852 : Upper (D 6) (R 6) [10,33,192,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12853 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 35 196 28 274 36 97 225 353), lower := (rows 11 35 196 28 274 36 64 128 256), losses := [] }

theorem u12853 : Upper (D 6) (R 6) [10,33,192,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12854 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 35 196 28 274 96 101 165 293), lower := (rows 11 35 196 28 274 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 119 67 131 259), good := (rows 493 485 228 60 508 96 96 128 256) },{ target := 2, region := (rows 9 10 0 8 16 100 64 128 256), good := (rows 11 35 224 59 274 96 96 128 256) }] }

theorem u12854 : Upper (D 6) (R 6) [10,33,192,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12855 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 28 304 33 70 198 326), lower := (rows 11 35 196 28 304 33 64 128 256), losses := [] }

theorem u12855 : Upper (D 6) (R 6) [10,33,192,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12856 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 28 304 34 69 197 325), lower := (rows 11 35 196 28 304 34 64 128 256), losses := [] }

theorem u12856 : Upper (D 6) (R 6) [10,33,192,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12857 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 35 196 28 304 36 67 195 323), lower := (rows 11 35 196 28 304 36 64 128 256), losses := [] }

theorem u12857 : Upper (D 6) (R 6) [10,33,192,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12858 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(1,2),(2,5)], upper := (rows 11 35 196 28 304 96 71 135 263), lower := (rows 11 35 196 28 304 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 100 64 128 256), good := (rows 11 35 224 59 304 96 96 128 256) }] }

theorem u12858 : Upper (D 6) (R 6) [10,33,192,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12859 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 196 28 336 33 102 166 294), lower := (rows 11 35 196 28 336 33 64 128 256), losses := [] }

theorem u12859 : Upper (D 6) (R 6) [10,33,192,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12860 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 196 28 336 34 101 165 293), lower := (rows 11 35 196 28 336 34 64 128 256), losses := [] }

theorem u12860 : Upper (D 6) (R 6) [10,33,192,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12861 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 196 28 336 36 99 163 291), lower := (rows 11 35 196 28 336 36 64 128 256), losses := [] }

theorem u12861 : Upper (D 6) (R 6) [10,33,192,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12862 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 73 52 34 340 404 276), lower := (rows 11 35 196 73 52 34 64 128 256), losses := [] }

theorem u12862 : Upper (D 6) (R 6) [10,33,192,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12863 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 196 73 52 36 338 402 274), lower := (rows 11 35 196 73 52 36 64 128 256), losses := [] }

theorem u12863 : Upper (D 6) (R 6) [10,33,192,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12864 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 196 73 52 48 326 390 262), lower := (rows 11 35 196 73 52 48 64 128 256), losses := [] }

theorem u12864 : Upper (D 6) (R 6) [10,33,192,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12864 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12865 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 196 73 52 288 86 150 278), lower := (rows 11 35 196 73 52 288 64 128 256), losses := [] }

theorem u12865 : Upper (D 6) (R 6) [10,33,192,65,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12865 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12866 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 73 276 34 116 180 308), lower := (rows 11 35 196 73 276 34 64 128 256), losses := [] }

theorem u12866 : Upper (D 6) (R 6) [10,33,192,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12867 : Route 9 := (fun mask => (mask,id))

def c12867 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12867 : Upper (D 6) (R 6) [10,33,192,65,260,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,65,260,4] 13 (by decide) (choices 1) [2,16,32] r12867 c12867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2553
  · exact u2554
  · exact u2555

def b12868 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 196 73 276 48 102 166 294), lower := (rows 11 35 196 73 276 48 64 128 256), losses := [] }

theorem u12868 : Upper (D 6) (R 6) [10,33,192,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12868 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12869 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 73 304 34 84 148 276), lower := (rows 11 35 196 73 304 34 64 128 256), losses := [] }

theorem u12869 : Upper (D 6) (R 6) [10,33,192,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12870 : Route 9 := (fun mask => (mask,id))

def c12870 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12870 : Upper (D 6) (R 6) [10,33,192,65,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,65,288,4] 13 (by decide) (choices 1) [2,4,16] r12870 c12870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2556
  · exact u2557
  · exact u2558

def b12871 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 196 73 304 48 70 134 262), lower := (rows 11 35 196 73 304 48 64 128 256), losses := [] }

theorem u12871 : Upper (D 6) (R 6) [10,33,192,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12871 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12872 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 88 22 33 356 420 292), lower := (rows 11 35 196 88 22 33 64 128 256), losses := [] }

theorem u12872 : Upper (D 6) (R 6) [10,33,192,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12873 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 35 196 88 22 36 353 417 289), lower := (rows 11 35 196 88 22 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 63 67 131 259), good := (rows 493 485 228 124 508 36 64 128 256) },{ target := 2, region := (rows 17 2 0 24 16 32 66 130 258), good := (rows 459 483 192 89 475 32 64 128 256) }] }

theorem u12873 : Upper (D 6) (R 6) [10,33,192,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12874 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 196 88 22 288 101 165 293), lower := (rows 11 35 196 88 22 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 307 67 131 259), good := (rows 493 485 196 124 508 288 64 128 288) }] }

theorem u12874 : Upper (D 6) (R 6) [10,33,192,80,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12874 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12875 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 88 52 33 326 390 262), lower := (rows 11 35 196 88 52 33 64 128 256), losses := [] }

theorem u12875 : Upper (D 6) (R 6) [10,33,192,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12876 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 88 52 34 325 389 261), lower := (rows 11 35 196 88 52 34 64 128 256), losses := [] }

theorem u12876 : Upper (D 6) (R 6) [10,33,192,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12877 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 196 88 52 36 323 387 259), lower := (rows 11 35 196 88 52 36 64 128 256), losses := [] }

theorem u12877 : Upper (D 6) (R 6) [10,33,192,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12878 : Route 9 := (fun mask => (mask,id))

def c12878 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12878 : Upper (D 6) (R 6) [10,33,192,80,36,256] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,36,256] 13 (by decide) (choices 1) [1,2,4] r12878 c12878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2559
  · exact u2560
  · exact u2561

def b12879 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 88 273 34 100 164 292), lower := (rows 11 35 196 88 273 34 64 128 256), losses := [] }

theorem u12879 : Upper (D 6) (R 6) [10,33,192,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12880 : Route 9 := (fun mask => (mask,id))

def c12880 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12880 : Upper (D 6) (R 6) [10,33,192,80,257,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,257,4] 13 (by decide) (choices 1) [2,4,32] r12880 c12880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2562
  · exact u2563
  · exact u2564

def b12881 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 88 274 33 100 164 292), lower := (rows 11 35 196 88 274 33 64 128 256), losses := [] }

theorem u12881 : Upper (D 6) (R 6) [10,33,192,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12882 : Route 9 := (fun mask => (mask,id))

def c12882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12882 : Upper (D 6) (R 6) [10,33,192,80,258,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,258,4] 13 (by decide) (choices 1) [1,4,32] r12882 c12882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2565
  · exact u2566
  · exact u2567

def b12883 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 88 276 33 102 166 294), lower := (rows 11 35 196 88 276 33 64 128 256), losses := [] }

theorem u12883 : Upper (D 6) (R 6) [10,33,192,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12884 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 88 276 34 101 165 293), lower := (rows 11 35 196 88 276 34 64 128 256), losses := [] }

theorem u12884 : Upper (D 6) (R 6) [10,33,192,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12885 : Route 9 := (fun mask => (mask,id))

def c12885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12885 : Upper (D 6) (R 6) [10,33,192,80,260,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,260,4] 13 (by decide) (choices 1) [1,2,32] r12885 c12885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2568
  · exact u2569
  · exact u2570

def b12886 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 88 304 33 70 134 262), lower := (rows 11 35 196 88 304 33 64 128 256), losses := [] }

theorem u12886 : Upper (D 6) (R 6) [10,33,192,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12887 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 88 304 34 69 133 261), lower := (rows 11 35 196 88 304 34 64 128 256), losses := [] }

theorem u12887 : Upper (D 6) (R 6) [10,33,192,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12888 : Route 9 := (fun mask => (mask,id))

def c12888 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12888 : Upper (D 6) (R 6) [10,33,192,80,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,80,288,4] 13 (by decide) (choices 1) [1,2,4] r12888 c12888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2571
  · exact u2572
  · exact u2573

def b12889 : PairBound 9 := { available := 84, camps := [{ cop := 8, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 265 52 34 84 212 340), lower := (rows 11 35 196 265 52 34 64 128 256), losses := [] }

theorem u12889 : Upper (D 6) (R 6) [10,33,192,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12890 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 196 265 52 36 82 210 338), lower := (rows 11 35 196 265 52 36 64 128 256), losses := [] }

theorem u12890 : Upper (D 6) (R 6) [10,33,192,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12891 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 196 265 52 48 70 198 326), lower := (rows 11 35 196 265 52 48 64 128 256), losses := [] }

theorem u12891 : Upper (D 6) (R 6) [10,33,192,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12891 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12892 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 267, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 196 265 52 96 86 150 278), lower := (rows 11 35 196 265 52 96 64 128 256), losses := [] }

theorem u12892 : Upper (D 6) (R 6) [10,33,192,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12893 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 265 112 34 84 148 276), lower := (rows 11 35 196 265 112 34 64 128 256), losses := [] }

theorem u12893 : Upper (D 6) (R 6) [10,33,192,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12894 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 244, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 35 196 265 112 36 86 150 278), lower := (rows 11 35 196 265 112 36 64 128 256), losses := [] }

theorem u12894 : Upper (D 6) (R 6) [10,33,192,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12895 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 196 265 112 48 70 134 262), lower := (rows 11 35 196 265 112 48 64 128 256), losses := [] }

theorem u12895 : Upper (D 6) (R 6) [10,33,192,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12895 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12896 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 196 268 21 34 112 240 368), lower := (rows 11 35 196 268 21 34 64 128 256), losses := [] }

theorem u12896 : Upper (D 6) (R 6) [10,33,192,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12897 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 196 268 21 48 98 226 354), lower := (rows 11 35 196 268 21 48 64 128 256), losses := [] }

theorem u12897 : Upper (D 6) (R 6) [10,33,192,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12897 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12898 : Route 9 := (fun mask => (mask,id))

def c12898 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12898 : Upper (D 6) (R 6) [10,33,192,260,5,64] 13 := by
  apply FastRouting.sound _ _ [10,33,192,260,5,64] 13 (by decide) (choices 1) [2,16,32] r12898 c12898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2574
  · exact u2575
  · exact u2576

def b12899 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 196 268 22 33 112 240 368), lower := (rows 11 35 196 268 22 33 64 128 256), losses := [] }

theorem u12899 : Upper (D 6) (R 6) [10,33,192,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12899
end Delivery.IrregularNine14.P06
