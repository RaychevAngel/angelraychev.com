import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0042
import IrregularNine14P06C0043

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12900 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 196 268 22 48 97 225 353), lower := (rows 11 35 196 268 22 48 64 128 256), losses := [] }

theorem u12900 : Upper (D 6) (R 6) [10,33,192,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12900 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12901 : Route 9 := (fun mask => (mask,id))

def c12901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12901 : Upper (D 6) (R 6) [10,33,192,260,6,64] 13 := by
  apply FastRouting.sound _ _ [10,33,192,260,6,64] 13 (by decide) (choices 1) [1,16,32] r12901 c12901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2577
  · exact u2578
  · exact u2579

def b12902 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 196 268 52 33 82 210 338), lower := (rows 11 35 196 268 52 33 64 128 256), losses := [] }

theorem u12902 : Upper (D 6) (R 6) [10,33,192,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12903 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 196 268 52 34 81 209 337), lower := (rows 11 35 196 268 52 34 64 128 256), losses := [] }

theorem u12903 : Upper (D 6) (R 6) [10,33,192,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12904 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 196 268 52 48 67 195 323), lower := (rows 11 35 196 268 52 48 64 128 256), losses := [] }

theorem u12904 : Upper (D 6) (R 6) [10,33,192,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12904 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12905 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 267, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 196 268 52 96 83 147 275), lower := (rows 11 35 196 268 52 96 64 128 256), losses := [] }

theorem u12905 : Upper (D 6) (R 6) [10,33,192,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12906 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 268 81 34 116 180 308), lower := (rows 11 35 196 268 81 34 64 128 256), losses := [] }

theorem u12906 : Upper (D 6) (R 6) [10,33,192,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12907 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 196 268 81 36 114 178 306), lower := (rows 11 35 196 268 81 36 64 128 256), losses := [] }

theorem u12907 : Upper (D 6) (R 6) [10,33,192,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12908 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 196 268 81 48 102 166 294), lower := (rows 11 35 196 268 81 48 64 128 256), losses := [] }

theorem u12908 : Upper (D 6) (R 6) [10,33,192,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12908 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12909 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 268 82 33 116 180 308), lower := (rows 11 35 196 268 82 33 64 128 256), losses := [] }

theorem u12909 : Upper (D 6) (R 6) [10,33,192,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12910 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 196 268 82 36 113 177 305), lower := (rows 11 35 196 268 82 36 64 128 256), losses := [] }

theorem u12910 : Upper (D 6) (R 6) [10,33,192,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12911 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 196 268 82 48 101 165 293), lower := (rows 11 35 196 268 82 48 64 128 256), losses := [] }

theorem u12911 : Upper (D 6) (R 6) [10,33,192,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12911 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12912 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 268 112 33 86 150 278), lower := (rows 11 35 196 268 112 33 64 128 256), losses := [] }

theorem u12912 : Upper (D 6) (R 6) [10,33,192,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12913 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 268 112 34 85 149 277), lower := (rows 11 35 196 268 112 34 64 128 256), losses := [] }

theorem u12913 : Upper (D 6) (R 6) [10,33,192,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12914 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 11 35 196 268 112 36 83 147 275), lower := (rows 11 35 196 268 112 36 64 128 256), losses := [] }

theorem u12914 : Upper (D 6) (R 6) [10,33,192,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12915 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 196 268 112 48 71 135 263), lower := (rows 11 35 196 268 112 48 64 128 256), losses := [] }

theorem u12915 : Upper (D 6) (R 6) [10,33,192,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12915 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12916 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 280 21 34 100 228 356), lower := (rows 11 35 196 280 21 34 64 128 256), losses := [] }

theorem u12916 : Upper (D 6) (R 6) [10,33,192,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12917 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 228, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 11 35 196 280 21 36 98 226 354), lower := (rows 11 35 196 280 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 63 67 131 259), good := (rows 494 486 228 316 508 36 64 128 256) }] }

theorem u12917 : Upper (D 6) (R 6) [10,33,192,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12918 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(0,2),(2,0),(3,0)], upper := (rows 11 35 196 280 21 96 102 166 294), lower := (rows 11 35 196 280 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 119 67 131 259), good := (rows 494 486 228 316 508 96 96 128 256) },{ target := 2, region := (rows 9 18 0 8 16 100 64 128 256), good := (rows 11 35 224 283 51 96 96 128 256) }] }

theorem u12918 : Upper (D 6) (R 6) [10,33,192,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12919 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 280 22 33 100 228 356), lower := (rows 11 35 196 280 22 33 64 128 256), losses := [] }

theorem u12919 : Upper (D 6) (R 6) [10,33,192,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12920 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 35 196 280 22 36 97 225 353), lower := (rows 11 35 196 280 22 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 63 67 131 259), good := (rows 493 485 228 316 508 36 64 128 256) },{ target := 2, region := (rows 17 2 0 24 16 32 66 130 258), good := (rows 459 483 192 281 475 32 64 128 256) }] }

theorem u12920 : Upper (D 6) (R 6) [10,33,192,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12921 : Route 9 := (fun mask => (mask,id))

def c12921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12921 : Upper (D 6) (R 6) [10,33,192,272,6,64] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272,6,64] 13 (by decide) (choices 1) [1,4,32] r12921 c12921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2580
  · exact u2581
  · exact u2582

def b12922 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 280 52 33 70 198 326), lower := (rows 11 35 196 280 52 33 64 128 256), losses := [] }

theorem u12922 : Upper (D 6) (R 6) [10,33,192,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12923 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 280 52 34 69 197 325), lower := (rows 11 35 196 280 52 34 64 128 256), losses := [] }

theorem u12923 : Upper (D 6) (R 6) [10,33,192,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12924 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 196 280 52 36 67 195 323), lower := (rows 11 35 196 280 52 36 64 128 256), losses := [] }

theorem u12924 : Upper (D 6) (R 6) [10,33,192,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12925 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 267, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 196 280 52 96 71 135 263), lower := (rows 11 35 196 280 52 96 64 128 256), losses := [] }

theorem u12925 : Upper (D 6) (R 6) [10,33,192,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12926 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 280 81 34 100 164 292), lower := (rows 11 35 196 280 81 34 64 128 256), losses := [] }

theorem u12926 : Upper (D 6) (R 6) [10,33,192,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12927 : Route 9 := (fun mask => (mask,id))

def c12927 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12927 : Upper (D 6) (R 6) [10,33,192,272,65,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272,65,4] 13 (by decide) (choices 1) [2,4,32] r12927 c12927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2583
  · exact u2584
  · exact u2585

def b12928 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 280 82 33 100 164 292), lower := (rows 11 35 196 280 82 33 64 128 256), losses := [] }

theorem u12928 : Upper (D 6) (R 6) [10,33,192,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12929 : Route 9 := (fun mask => (mask,id))

def c12929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12929 : Upper (D 6) (R 6) [10,33,192,272,66,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,272,66,4] 13 (by decide) (choices 1) [1,4,32] r12929 c12929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2586
  · exact u2587
  · exact u2588

def b12930 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 280 112 33 70 134 262), lower := (rows 11 35 196 280 112 33 64 128 256), losses := [] }

theorem u12930 : Upper (D 6) (R 6) [10,33,192,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12931 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 280 112 34 69 133 261), lower := (rows 11 35 196 280 112 34 64 128 256), losses := [] }

theorem u12931 : Upper (D 6) (R 6) [10,33,192,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12932 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 35 196 280 112 36 71 135 263), lower := (rows 11 35 196 280 112 36 64 128 256), losses := [] }

theorem u12932 : Upper (D 6) (R 6) [10,33,192,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12933 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 328 21 34 116 180 308), lower := (rows 11 35 196 328 21 34 64 128 256), losses := [] }

theorem u12933 : Upper (D 6) (R 6) [10,33,192,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12934 : Route 9 := (fun mask => (mask,id))

def c12934 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12934 : Upper (D 6) (R 6) [10,33,192,320,5,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,320,5,4] 13 (by decide) (choices 1) [2,16,32] r12934 c12934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2589
  · exact u2590
  · exact u2591

def b12935 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 196 328 21 48 102 166 294), lower := (rows 11 35 196 328 21 48 64 128 256), losses := [] }

theorem u12935 : Upper (D 6) (R 6) [10,33,192,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12935 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12936 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 328 22 33 116 180 308), lower := (rows 11 35 196 328 22 33 64 128 256), losses := [] }

theorem u12936 : Upper (D 6) (R 6) [10,33,192,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12937 : Route 9 := (fun mask => (mask,id))

def c12937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12937 : Upper (D 6) (R 6) [10,33,192,320,6,4] 13 := by
  apply FastRouting.sound _ _ [10,33,192,320,6,4] 13 (by decide) (choices 1) [1,16,32] r12937 c12937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2592
  · exact u2593
  · exact u2594

def b12938 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 196 328 22 48 101 165 293), lower := (rows 11 35 196 328 22 48 64 128 256), losses := [] }

theorem u12938 : Upper (D 6) (R 6) [10,33,192,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12938 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12939 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 328 52 33 86 150 278), lower := (rows 11 35 196 328 52 33 64 128 256), losses := [] }

theorem u12939 : Upper (D 6) (R 6) [10,33,192,320,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12940 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 196 328 52 34 85 149 277), lower := (rows 11 35 196 328 52 34 64 128 256), losses := [] }

theorem u12940 : Upper (D 6) (R 6) [10,33,192,320,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12941 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 196 328 52 36 83 147 275), lower := (rows 11 35 196 328 52 36 64 128 256), losses := [] }

theorem u12941 : Upper (D 6) (R 6) [10,33,192,320,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12942 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 196 328 52 48 71 135 263), lower := (rows 11 35 196 328 52 48 64 128 256), losses := [] }

theorem u12942 : Upper (D 6) (R 6) [10,33,192,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12942 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12943 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 13 84 34 112 240 368), lower := (rows 11 35 388 13 84 34 64 128 256), losses := [] }

theorem u12943 : Upper (D 6) (R 6) [10,33,384,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12944 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 388 13 84 48 98 226 354), lower := (rows 11 35 388 13 84 48 64 128 256), losses := [] }

theorem u12944 : Upper (D 6) (R 6) [10,33,384,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12944 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12945 : Route 9 := (fun mask => (mask,id))

def c12945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12945 : Upper (D 6) (R 6) [10,33,384,5,68,64] 13 := by
  apply FastRouting.sound _ _ [10,33,384,5,68,64] 13 (by decide) (choices 1) [2,16,32] r12945 c12945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2595
  · exact u2596
  · exact u2597

def b12946 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 13 112 34 84 212 340), lower := (rows 11 35 388 13 112 34 64 128 256), losses := [] }

theorem u12946 : Upper (D 6) (R 6) [10,33,384,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12947 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 388 13 112 36 82 210 338), lower := (rows 11 35 388 13 112 36 64 128 256), losses := [] }

theorem u12947 : Upper (D 6) (R 6) [10,33,384,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12948 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 388 13 112 48 70 198 326), lower := (rows 11 35 388 13 112 48 64 128 256), losses := [] }

theorem u12948 : Upper (D 6) (R 6) [10,33,384,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12948 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12949 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 388 13 112 96 86 150 278), lower := (rows 11 35 388 13 112 96 64 128 256), losses := [] }

theorem u12949 : Upper (D 6) (R 6) [10,33,384,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12950 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 25 84 34 100 228 356), lower := (rows 11 35 388 25 84 34 64 128 256), losses := [] }

theorem u12950 : Upper (D 6) (R 6) [10,33,384,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12951 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 388 25 84 36 98 226 354), lower := (rows 11 35 388 25 84 36 64 128 256), losses := [] }

theorem u12951 : Upper (D 6) (R 6) [10,33,384,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12952 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 388 25 84 96 102 166 294), lower := (rows 11 35 388 25 84 96 64 128 256), losses := [] }

theorem u12952 : Upper (D 6) (R 6) [10,33,384,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12953 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 28 81 34 100 228 356), lower := (rows 11 35 388 28 81 34 64 128 256), losses := [] }

theorem u12953 : Upper (D 6) (R 6) [10,33,384,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12954 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 484, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 11 35 388 28 81 36 98 226 354), lower := (rows 11 35 388 28 81 36 64 128 256), losses := [] }

theorem u12954 : Upper (D 6) (R 6) [10,33,384,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12955 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 1, region := 388, targets := 64 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(2,6)], upper := (rows 11 35 388 28 81 96 102 166 294), lower := (rows 11 35 388 28 81 96 64 128 256), losses := [] }

theorem u12955 : Upper (D 6) (R 6) [10,33,384,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12956 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 28 82 33 100 228 356), lower := (rows 11 35 388 28 82 33 64 128 256), losses := [] }

theorem u12956 : Upper (D 6) (R 6) [10,33,384,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12957 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 35 388 28 82 36 97 225 353), lower := (rows 11 35 388 28 82 36 64 128 256), losses := [] }

theorem u12957 : Upper (D 6) (R 6) [10,33,384,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12958 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 1, region := 388, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 35 388 28 82 96 101 165 293), lower := (rows 11 35 388 28 82 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 115 67 131 259), good := (rows 493 485 388 60 508 96 96 128 256) }] }

theorem u12958 : Upper (D 6) (R 6) [10,33,384,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12959 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 28 112 33 70 198 326), lower := (rows 11 35 388 28 112 33 64 128 256), losses := [] }

theorem u12959 : Upper (D 6) (R 6) [10,33,384,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12959
end Delivery.IrregularNine14.P06
