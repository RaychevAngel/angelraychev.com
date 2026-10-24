import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0025
import IrregularNine14P07C0026

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12900 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 52 265 82 33 192 192 448), lower := (rows 7 42 52 265 82 33 64 128 256), losses := [] }

theorem u12900 : Upper (D 7) (R 7) [6,40,48,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12901 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,6),(1,6),(3,5),(3,6)], upper := (rows 7 42 52 265 82 96 193 129 385), lower := (rows 7 42 52 265 82 96 64 128 256), losses := [] }

theorem u12901 : Upper (D 7) (R 7) [6,40,48,257,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12902 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 456, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(4,5)], upper := (rows 7 42 52 265 82 160 193 193 449), lower := (rows 7 42 52 265 82 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 9 16 171 73 137 265), good := (rows 493 488 52 489 116 160 64 160 256) }] }

theorem u12902 : Upper (D 7) (R 7) [6,40,48,257,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12903 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 52 265 208 33 194 194 450), lower := (rows 7 42 52 265 208 33 64 128 256), losses := [] }

theorem u12903 : Upper (D 7) (R 7) [6,40,48,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12904 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 265 208 34 193 193 449), lower := (rows 7 42 52 265 208 34 64 128 256), losses := [] }

theorem u12904 : Upper (D 7) (R 7) [6,40,48,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12905 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 42 52 265 208 96 195 131 387), lower := (rows 7 42 52 265 208 96 64 128 256), losses := [] }

theorem u12905 : Upper (D 7) (R 7) [6,40,48,257,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12906 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 52 328 81 33 194 130 386), lower := (rows 7 42 52 328 81 33 64 128 256), losses := [] }

theorem u12906 : Upper (D 7) (R 7) [6,40,48,320,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12907 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 328 81 34 193 129 385), lower := (rows 7 42 52 328 81 34 64 128 256), losses := [] }

theorem u12907 : Upper (D 7) (R 7) [6,40,48,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12908 : Route 9 := (fun mask => (mask,id))

def c12908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12908 : Upper (D 7) (R 7) [6,40,48,320,65,128] 13 := by
  apply FastRouting.sound _ _ [6,40,48,320,65,128] 13 (by decide) (choices 1) [1,2,128] r12908 c12908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1537
  · exact u1538
  · exact u1539

def b12909 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 42 52 328 145 33 194 194 450), lower := (rows 7 42 52 328 145 33 64 128 256), losses := [] }

theorem u12909 : Upper (D 7) (R 7) [6,40,48,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12910 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 328 145 34 193 193 449), lower := (rows 7 42 52 328 145 34 64 128 256), losses := [] }

theorem u12910 : Upper (D 7) (R 7) [6,40,48,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12911 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 149, targets := 64 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 52 328 145 96 195 131 387), lower := (rows 7 42 52 328 145 96 64 128 256), losses := [] }

theorem u12911 : Upper (D 7) (R 7) [6,40,48,320,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12912 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 52 328 145 160 67 195 323), lower := (rows 7 42 52 328 145 160 64 128 256), losses := [] }

theorem u12912 : Upper (D 7) (R 7) [6,40,48,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12913 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 52 328 146 33 193 193 449), lower := (rows 7 42 52 328 146 33 64 128 256), losses := [] }

theorem u12913 : Upper (D 7) (R 7) [6,40,48,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12914 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 149, targets := 64 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 52 328 146 96 193 129 385), lower := (rows 7 42 52 328 146 96 64 128 256), losses := [] }

theorem u12914 : Upper (D 7) (R 7) [6,40,48,320,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12915 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 0, region := 328, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7)], upper := (rows 7 42 52 328 146 160 65 193 321), lower := (rows 7 42 52 328 146 160 64 128 256), losses := [] }

theorem u12915 : Upper (D 7) (R 7) [6,40,48,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12916 : Route 9 := (fun mask => (mask,id))

def c12916 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12916 : Upper (D 7) (R 7) [6,40,48,320,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,48,320,192,1] 13 (by decide) (choices 1) [1,2,128] r12916 c12916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1540
  · exact u1541
  · exact u1542

def b12917 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 328 208 34 193 129 385), lower := (rows 7 42 52 328 208 34 64 128 256), losses := [] }

theorem u12917 : Upper (D 7) (R 7) [6,40,48,320,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12918 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 52 328 208 160 67 131 259), lower := (rows 7 42 52 328 208 160 64 128 256), losses := [] }

theorem u12918 : Upper (D 7) (R 7) [6,40,48,320,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12919 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 0, region := 484, targets := 2 },{ cop := 1, region := 400, targets := 64 }], pairs := [(1,0),(2,1),(4,0),(4,6)], upper := (rows 7 42 69 25 146 96 480 416 416), lower := (rows 7 42 69 25 146 96 64 128 256), losses := [] }

theorem u12919 : Upper (D 7) (R 7) [6,40,65,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12920 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 42 69 25 146 160 352 480 352), lower := (rows 7 42 69 25 146 160 64 128 256), losses := [] }

theorem u12920 : Upper (D 7) (R 7) [6,40,65,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12921 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 42 69 25 146 288 224 224 480), lower := (rows 7 42 69 25 146 288 64 128 256), losses := [] }

theorem u12921 : Upper (D 7) (R 7) [6,40,65,17,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12921 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12922 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 25 208 34 480 416 416), lower := (rows 7 42 69 25 208 34 64 128 256), losses := [] }

theorem u12922 : Upper (D 7) (R 7) [6,40,65,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12923 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 42 69 25 208 160 354 418 290), lower := (rows 7 42 69 25 208 160 64 128 256), losses := [] }

theorem u12923 : Upper (D 7) (R 7) [6,40,65,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12924 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 69 25 208 288 226 162 418), lower := (rows 7 42 69 25 208 288 64 128 256), losses := [] }

theorem u12924 : Upper (D 7) (R 7) [6,40,65,17,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12924 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12925 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 0, region := 228, targets := 2 },{ cop := 1, region := 400, targets := 64 }], pairs := [(1,0),(2,1),(4,0),(4,6)], upper := (rows 7 42 69 25 274 96 224 160 416), lower := (rows 7 42 69 25 274 96 64 128 256), losses := [] }

theorem u12925 : Upper (D 7) (R 7) [6,40,65,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12926 : Route 9 := (fun mask => (mask,id))

def c12926 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12926 : Upper (D 7) (R 7) [6,40,65,17,258,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17,258,128] 13 (by decide) (choices 1) [32,128] r12926 c12926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1543
  · exact u1544

def b12927 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 25 336 34 224 160 416), lower := (rows 7 42 69 25 336 34 64 128 256), losses := [] }

theorem u12927 : Upper (D 7) (R 7) [6,40,65,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12928 : Route 9 := (fun mask => (mask,id))

def c12928 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12928 : Upper (D 7) (R 7) [6,40,65,17,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17,320,128] 13 (by decide) (choices 1) [2,32,128] r12928 c12928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1545
  · exact u1546
  · exact u1547

def b12929 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 25 400 34 224 224 480), lower := (rows 7 42 69 25 400 34 64 128 256), losses := [] }

theorem u12929 : Upper (D 7) (R 7) [6,40,65,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12930 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 64 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 7 42 69 25 400 96 226 162 418), lower := (rows 7 42 69 25 400 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 13 19 32 0 130 258), good := (rows 415 442 29 25 400 32 0 128 256) }] }

theorem u12930 : Upper (D 7) (R 7) [6,40,65,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12931 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 42 69 25 400 160 98 226 354), lower := (rows 7 42 69 25 400 160 64 128 256), losses := [] }

theorem u12931 : Upper (D 7) (R 7) [6,40,65,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12932 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 26 208 33 480 416 416), lower := (rows 7 42 69 26 208 33 64 128 256), losses := [] }

theorem u12932 : Upper (D 7) (R 7) [6,40,65,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12933 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 26 208 160 353 417 289), lower := (rows 7 42 69 26 208 160 64 128 256), losses := [] }

theorem u12933 : Upper (D 7) (R 7) [6,40,65,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12934 : Route 9 := (fun mask => (mask,id))

def c12934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12934 : Upper (D 7) (R 7) [6,40,65,18,192,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,192,256] 13 (by decide) (choices 1) [1,32,128] r12934 c12934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1548
  · exact u1549
  · exact u1550

def b12935 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 26 336 33 224 160 416), lower := (rows 7 42 69 26 336 33 64 128 256), losses := [] }

theorem u12935 : Upper (D 7) (R 7) [6,40,65,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12936 : Route 9 := (fun mask => (mask,id))

def c12936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12936 : Upper (D 7) (R 7) [6,40,65,18,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,320,128] 13 (by decide) (choices 1) [1,32,128] r12936 c12936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1551
  · exact u1552
  · exact u1553

def b12937 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 69 26 400 33 224 224 480), lower := (rows 7 42 69 26 400 33 64 128 256), losses := [] }

theorem u12937 : Upper (D 7) (R 7) [6,40,65,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12938 : Route 9 := (fun mask => (mask,id))

def c12938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12938 : Upper (D 7) (R 7) [6,40,65,18,384,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,384,64] 13 (by decide) (choices 1) [1,32,128] r12938 c12938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1554
  · exact u1555
  · exact u1556

def b12939 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 26 400 160 97 225 353), lower := (rows 7 42 69 26 400 160 64 128 256), losses := [] }

theorem u12939 : Upper (D 7) (R 7) [6,40,65,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12940 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 88 146 33 480 416 416), lower := (rows 7 42 69 88 146 33 64 128 256), losses := [] }

theorem u12940 : Upper (D 7) (R 7) [6,40,65,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12941 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,7),(2,1),(2,7),(4,6)], upper := (rows 7 42 69 88 146 160 353 417 289), lower := (rows 7 42 69 88 146 160 64 128 256), losses := [] }

theorem u12941 : Upper (D 7) (R 7) [6,40,65,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12942 : Route 9 := (fun mask => (mask,id))

def c12942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12942 : Upper (D 7) (R 7) [6,40,65,80,130,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,80,130,256] 13 (by decide) (choices 1) [1,32,128] r12942 c12942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1557
  · exact u1558
  · exact u1559

def b12943 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 88 176 33 450 386 386), lower := (rows 7 42 69 88 176 33 64 128 256), losses := [] }

theorem u12943 : Upper (D 7) (R 7) [6,40,65,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12944 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 452, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 7 42 69 88 176 34 449 385 385), lower := (rows 7 42 69 88 176 34 64 128 256), losses := [] }

theorem u12944 : Upper (D 7) (R 7) [6,40,65,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12945 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 88 176 160 323 387 259), lower := (rows 7 42 69 88 176 160 64 128 256), losses := [] }

theorem u12945 : Upper (D 7) (R 7) [6,40,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12946 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 42 69 88 176 288 195 131 387), lower := (rows 7 42 69 88 176 288 64 128 256), losses := [] }

theorem u12946 : Upper (D 7) (R 7) [6,40,65,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12946 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12947 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 88 274 33 224 160 416), lower := (rows 7 42 69 88 274 33 64 128 256), losses := [] }

theorem u12947 : Upper (D 7) (R 7) [6,40,65,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12948 : Route 9 := (fun mask => (mask,id))

def c12948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12948 : Upper (D 7) (R 7) [6,40,65,80,258,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,80,258,128] 13 (by decide) (choices 1) [1,32,128] r12948 c12948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1560
  · exact u1561
  · exact u1562

def b12949 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 88 304 33 194 130 386), lower := (rows 7 42 69 88 304 33 64 128 256), losses := [] }

theorem u12949 : Upper (D 7) (R 7) [6,40,65,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12950 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 7 42 69 88 304 34 193 129 385), lower := (rows 7 42 69 88 304 34 64 128 256), losses := [] }

theorem u12950 : Upper (D 7) (R 7) [6,40,65,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12951 : Route 9 := (fun mask => (mask,id))

def c12951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12951 : Upper (D 7) (R 7) [6,40,65,80,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,80,288,128] 13 (by decide) (choices 1) [1,2,128] r12951 c12951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1563
  · exact u1564
  · exact u1565

def b12952 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 88 400 33 226 162 418), lower := (rows 7 42 69 88 400 33 64 128 256), losses := [] }

theorem u12952 : Upper (D 7) (R 7) [6,40,65,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12953 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 88 400 34 225 161 417), lower := (rows 7 42 69 88 400 34 64 128 256), losses := [] }

theorem u12953 : Upper (D 7) (R 7) [6,40,65,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12954 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,7),(1,0),(2,7),(4,6)], upper := (rows 7 42 69 88 400 160 99 163 291), lower := (rows 7 42 69 88 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 6 42 68 122 432 160 64 160 256) }] }

theorem u12954 : Upper (D 7) (R 7) [6,40,65,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12955 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 69 137 112 34 464 400 400), lower := (rows 7 42 69 137 112 34 64 128 256), losses := [] }

theorem u12955 : Upper (D 7) (R 7) [6,40,65,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12956 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 69 137 112 48 450 386 386), lower := (rows 7 42 69 137 112 48 64 128 256), losses := [] }

theorem u12956 : Upper (D 7) (R 7) [6,40,65,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12956 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12957 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 69 137 112 160 338 402 274), lower := (rows 7 42 69 137 112 160 64 128 256), losses := [] }

theorem u12957 : Upper (D 7) (R 7) [6,40,65,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12958 : Route 9 := (fun mask => (mask,id))

def c12958 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12958 : Upper (D 7) (R 7) [6,40,65,129,96,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,96,256] 13 (by decide) (choices 1) [2,16,128] r12958 c12958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1566
  · exact u1567
  · exact u1568

def b12959 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 3, region := 50, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 42 69 137 176 34 336 464 336), lower := (rows 7 42 69 137 176 34 64 128 256), losses := [] }

theorem u12959 : Upper (D 7) (R 7) [6,40,65,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12959
end Delivery.IrregularNine14.P07
