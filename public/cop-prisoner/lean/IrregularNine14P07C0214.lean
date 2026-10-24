import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0025

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12840 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 21 200 112 33 450 386 386), lower := (rows 7 42 21 200 112 33 64 128 256), losses := [] }

theorem u12840 : Upper (D 7) (R 7) [6,40,17,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12841 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 21 200 112 34 449 385 385), lower := (rows 7 42 21 200 112 34 64 128 256), losses := [] }

theorem u12841 : Upper (D 7) (R 7) [6,40,17,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12842 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 21 200 112 160 323 387 259), lower := (rows 7 42 21 200 112 160 64 128 256), losses := [] }

theorem u12842 : Upper (D 7) (R 7) [6,40,17,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12843 : Route 9 := (fun mask => (mask,id))

def c12843 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12843 : Upper (D 7) (R 7) [6,40,17,192,96,256] 13 := by
  apply FastRouting.sound _ _ [6,40,17,192,96,256] 13 (by decide) (choices 1) [1,2,128] r12843 c12843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1500
  · exact u1501
  · exact u1502

def b12844 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 7 42 21 200 304 33 194 194 450), lower := (rows 7 42 21 200 304 33 64 128 256), losses := [] }

theorem u12844 : Upper (D 7) (R 7) [6,40,17,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12845 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 7 42 21 200 304 34 193 193 449), lower := (rows 7 42 21 200 304 34 64 128 256), losses := [] }

theorem u12845 : Upper (D 7) (R 7) [6,40,17,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12846 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 21 200 304 96 195 131 387), lower := (rows 7 42 21 200 304 96 64 128 256), losses := [] }

theorem u12846 : Upper (D 7) (R 7) [6,40,17,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12847 : Route 9 := (fun mask => (mask,id))

def c12847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12847 : Upper (D 7) (R 7) [6,40,17,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,17,192,320,1] 13 (by decide) (choices 1) [2,32,128] r12847 c12847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1503
  · exact u1504
  · exact u1505

def r12848 : Route 9 := (fun mask => (mask,id))

def c12848 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12848 : Upper (D 7) (R 7) [6,40,17,192,320,2] 13 := by
  apply FastRouting.sound _ _ [6,40,17,192,320,2] 13 (by decide) (choices 1) [1,32,128] r12848 c12848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1506
  · exact u1507
  · exact u1508

def b12849 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 21 200 336 160 99 163 291), lower := (rows 7 42 21 200 336 160 64 128 256), losses := [] }

theorem u12849 : Upper (D 7) (R 7) [6,40,17,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12850 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 456, targets := 34 },{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(4,0)], upper := (rows 7 42 21 265 112 34 192 192 448), lower := (rows 7 42 21 265 112 34 64 128 256), losses := [] }

theorem u12850 : Upper (D 7) (R 7) [6,40,17,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12851 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 42 21 265 112 96 194 130 386), lower := (rows 7 42 21 265 112 96 64 128 256), losses := [] }

theorem u12851 : Upper (D 7) (R 7) [6,40,17,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12852 : Route 9 := (fun mask => (mask,id))

def c12852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12852 : Upper (D 7) (R 7) [6,40,17,257,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,257,96,128] 13 (by decide) (choices 1) [2,128] r12852 c12852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1509
  · exact u1510

def b12853 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 21 265 208 34 224 224 480), lower := (rows 7 42 21 265 208 34 64 128 256), losses := [] }

theorem u12853 : Upper (D 7) (R 7) [6,40,17,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12854 : Route 9 := (fun mask => (mask,id))

def c12854 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12854 : Upper (D 7) (R 7) [6,40,17,257,192,64] 13 := by
  apply FastRouting.sound _ _ [6,40,17,257,192,64] 13 (by decide) (choices 1) [2,32,128] r12854 c12854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1511
  · exact u1512
  · exact u1513

def b12855 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 21 266 112 33 192 192 448), lower := (rows 7 42 21 266 112 33 64 128 256), losses := [] }

theorem u12855 : Upper (D 7) (R 7) [6,40,17,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12856 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 42 21 266 112 96 193 129 385), lower := (rows 7 42 21 266 112 96 64 128 256), losses := [] }

theorem u12856 : Upper (D 7) (R 7) [6,40,17,258,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12857 : Route 9 := (fun mask => (mask,id))

def c12857 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12857 : Upper (D 7) (R 7) [6,40,17,258,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,258,96,128] 13 (by decide) (choices 1) [1,128] r12857 c12857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1514
  · exact u1515

def b12858 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 21 266 208 33 224 224 480), lower := (rows 7 42 21 266 208 33 64 128 256), losses := [] }

theorem u12858 : Upper (D 7) (R 7) [6,40,17,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12859 : Route 9 := (fun mask => (mask,id))

def c12859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12859 : Upper (D 7) (R 7) [6,40,17,258,192,64] 13 := by
  apply FastRouting.sound _ _ [6,40,17,258,192,64] 13 (by decide) (choices 1) [1,32,128] r12859 c12859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1516
  · exact u1517
  · exact u1518

def b12860 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 21 328 112 33 194 130 386), lower := (rows 7 42 21 328 112 33 64 128 256), losses := [] }

theorem u12860 : Upper (D 7) (R 7) [6,40,17,320,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12861 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 21 328 112 34 193 129 385), lower := (rows 7 42 21 328 112 34 64 128 256), losses := [] }

theorem u12861 : Upper (D 7) (R 7) [6,40,17,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12862 : Route 9 := (fun mask => (mask,id))

def c12862 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12862 : Upper (D 7) (R 7) [6,40,17,320,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,96,128] 13 (by decide) (choices 1) [1,2,128] r12862 c12862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1519
  · exact u1520
  · exact u1521

def b12863 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 456, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 7 42 21 328 176 33 194 194 450), lower := (rows 7 42 21 328 176 33 64 128 256), losses := [] }

theorem u12863 : Upper (D 7) (R 7) [6,40,17,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12864 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 456, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 7 42 21 328 176 34 193 193 449), lower := (rows 7 42 21 328 176 34 64 128 256), losses := [] }

theorem u12864 : Upper (D 7) (R 7) [6,40,17,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12865 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 149, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 21 328 176 96 195 131 387), lower := (rows 7 42 21 328 176 96 64 128 256), losses := [] }

theorem u12865 : Upper (D 7) (R 7) [6,40,17,320,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12866 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 328 176 160 67 195 323), lower := (rows 7 42 21 328 176 160 64 128 256), losses := [] }

theorem u12866 : Upper (D 7) (R 7) [6,40,17,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12867 : Route 9 := (fun mask => (mask,id))

def c12867 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12867 : Upper (D 7) (R 7) [6,40,17,320,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,192,1] 13 (by decide) (choices 1) [2,32,128] r12867 c12867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1522
  · exact u1523
  · exact u1524

def r12868 : Route 9 := (fun mask => (mask,id))

def c12868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12868 : Upper (D 7) (R 7) [6,40,17,320,192,2] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,192,2] 13 (by decide) (choices 1) [1,32,128] r12868 c12868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1525
  · exact u1526
  · exact u1527

def r12869 : Route 9 := (fun mask => (mask,id))

def c12869 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12869 : Upper (D 7) (R 7) [6,40,17,320,192,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,192,128] 13 (by decide) (choices 1) [1,2,32] r12869 c12869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1528
  · exact u1529
  · exact u1530

def b12870 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 52 73 146 33 448 448 448), lower := (rows 7 42 52 73 146 33 64 128 256), losses := [] }

theorem u12870 : Upper (D 7) (R 7) [6,40,48,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12871 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 52 73 146 96 449 385 385), lower := (rows 7 42 52 73 146 96 64 128 256), losses := [] }

theorem u12871 : Upper (D 7) (R 7) [6,40,48,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12872 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 0, region := 328, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7)], upper := (rows 7 42 52 73 146 160 321 449 321), lower := (rows 7 42 52 73 146 160 64 128 256), losses := [] }

theorem u12872 : Upper (D 7) (R 7) [6,40,48,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12873 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 42 52 73 146 288 193 193 449), lower := (rows 7 42 52 73 146 288 64 128 256), losses := [] }

theorem u12873 : Upper (D 7) (R 7) [6,40,48,65,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12873 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12874 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 52 73 208 33 450 386 386), lower := (rows 7 42 52 73 208 33 64 128 256), losses := [] }

theorem u12874 : Upper (D 7) (R 7) [6,40,48,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12875 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 73 208 34 449 385 385), lower := (rows 7 42 52 73 208 34 64 128 256), losses := [] }

theorem u12875 : Upper (D 7) (R 7) [6,40,48,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12876 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 52 73 208 160 323 387 259), lower := (rows 7 42 52 73 208 160 64 128 256), losses := [] }

theorem u12876 : Upper (D 7) (R 7) [6,40,48,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12877 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(3,5),(4,5)], upper := (rows 7 42 52 73 208 288 195 131 387), lower := (rows 7 42 52 73 208 288 64 128 256), losses := [] }

theorem u12877 : Upper (D 7) (R 7) [6,40,48,65,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12877 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12878 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 52 73 274 33 192 192 448), lower := (rows 7 42 52 73 274 33 64 128 256), losses := [] }

theorem u12878 : Upper (D 7) (R 7) [6,40,48,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12879 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 52 73 274 96 193 129 385), lower := (rows 7 42 52 73 274 96 64 128 256), losses := [] }

theorem u12879 : Upper (D 7) (R 7) [6,40,48,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12880 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(4,5)], upper := (rows 7 42 52 73 274 160 193 193 449), lower := (rows 7 42 52 73 274 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 9 16 171 73 137 265), good := (rows 493 488 52 489 308 160 64 160 256) }] }

theorem u12880 : Upper (D 7) (R 7) [6,40,48,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12881 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 52 73 336 33 194 130 386), lower := (rows 7 42 52 73 336 33 64 128 256), losses := [] }

theorem u12881 : Upper (D 7) (R 7) [6,40,48,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12882 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 73 336 34 193 129 385), lower := (rows 7 42 52 73 336 34 64 128 256), losses := [] }

theorem u12882 : Upper (D 7) (R 7) [6,40,48,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12883 : Route 9 := (fun mask => (mask,id))

def c12883 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12883 : Upper (D 7) (R 7) [6,40,48,65,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,320,128] 13 (by decide) (choices 1) [1,2,128] r12883 c12883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1531
  · exact u1532
  · exact u1533

def b12884 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 52 73 400 33 194 194 450), lower := (rows 7 42 52 73 400 33 64 128 256), losses := [] }

theorem u12884 : Upper (D 7) (R 7) [6,40,48,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12885 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 73 400 34 193 193 449), lower := (rows 7 42 52 73 400 34 64 128 256), losses := [] }

theorem u12885 : Upper (D 7) (R 7) [6,40,48,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12886 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 52 73 400 96 195 131 387), lower := (rows 7 42 52 73 400 96 64 128 256), losses := [] }

theorem u12886 : Upper (D 7) (R 7) [6,40,48,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12887 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 52 73 400 160 67 195 323), lower := (rows 7 42 52 73 400 160 64 128 256), losses := [] }

theorem u12887 : Upper (D 7) (R 7) [6,40,48,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12888 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 52 200 81 33 450 386 386), lower := (rows 7 42 52 200 81 33 64 128 256), losses := [] }

theorem u12888 : Upper (D 7) (R 7) [6,40,48,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12889 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 200 81 34 449 385 385), lower := (rows 7 42 52 200 81 34 64 128 256), losses := [] }

theorem u12889 : Upper (D 7) (R 7) [6,40,48,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12890 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 52 200 81 160 323 387 259), lower := (rows 7 42 52 200 81 160 64 128 256), losses := [] }

theorem u12890 : Upper (D 7) (R 7) [6,40,48,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12891 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 7 42 52 200 81 288 195 131 387), lower := (rows 7 42 52 200 81 288 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 8 16 305 0 129 257), good := (rows 423 42 52 136 437 288 0 128 288) }] }

theorem u12891 : Upper (D 7) (R 7) [6,40,48,192,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12891 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12892 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 42 52 200 273 33 194 194 450), lower := (rows 7 42 52 200 273 33 64 128 256), losses := [] }

theorem u12892 : Upper (D 7) (R 7) [6,40,48,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12893 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 200 273 34 193 193 449), lower := (rows 7 42 52 200 273 34 64 128 256), losses := [] }

theorem u12893 : Upper (D 7) (R 7) [6,40,48,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12894 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 52 200 273 96 195 131 387), lower := (rows 7 42 52 200 273 96 64 128 256), losses := [] }

theorem u12894 : Upper (D 7) (R 7) [6,40,48,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12895 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 52 200 274 33 193 193 449), lower := (rows 7 42 52 200 274 33 64 128 256), losses := [] }

theorem u12895 : Upper (D 7) (R 7) [6,40,48,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12896 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 52 200 274 96 193 129 385), lower := (rows 7 42 52 200 274 96 64 128 256), losses := [] }

theorem u12896 : Upper (D 7) (R 7) [6,40,48,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12897 : Route 9 := (fun mask => (mask,id))

def c12897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12897 : Upper (D 7) (R 7) [6,40,48,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320,1] 13 (by decide) (choices 1) [1,2,128] r12897 c12897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1534
  · exact u1535
  · exact u1536

def b12898 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 200 336 34 193 129 385), lower := (rows 7 42 52 200 336 34 64 128 256), losses := [] }

theorem u12898 : Upper (D 7) (R 7) [6,40,48,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12899 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 52 200 336 160 67 131 259), lower := (rows 7 42 52 200 336 160 64 128 256), losses := [] }

theorem u12899 : Upper (D 7) (R 7) [6,40,48,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12899
end Delivery.IrregularNine14.P07
