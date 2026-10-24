import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0002
import IrregularNine14P06C0003

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2700 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 1, region := 201, targets := 32 }], pairs := [(0,5),(4,0),(4,6)], upper := (rows 11 38 84 200 304 33 65 134 262), lower := (rows 11 38 84 200 304 33 65 128 256), losses := [] }

theorem u2700 : Upper (D 6) (R 6) [10,36,80,192,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2701 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 201, targets := 32 },{ cop := 4, region := 70, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 84 200 304 33 66 133 261), lower := (rows 11 38 84 200 304 33 66 128 256), losses := [] }

theorem u2701 : Upper (D 6) (R 6) [10,36,80,192,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2702 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 304, targets := 68 },{ cop := 1, region := 201, targets := 32 }], pairs := [(0,5),(4,2),(4,6)], upper := (rows 11 38 84 200 304 33 68 131 259), lower := (rows 11 38 84 200 304 33 68 128 256), losses := [] }

theorem u2702 : Upper (D 6) (R 6) [10,36,80,192,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2703 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 38 133 25 276 96 66 224 352), lower := (rows 11 38 133 25 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 18 96 64 224 352), good := (rows 25 436 141 25 276 480 496 128 256) }] }

theorem u2703 : Upper (D 6) (R 6) [10,36,129,17,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2704 : Route 9 := (fun mask => (mask,id))

def c2704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2704 : Upper (D 6) (R 6) [10,36,129,17,260,64,32] 13 := by
  apply FastRouting.sound _ _ [10,36,129,17,260,64,32] 13 (by decide) (choices 1) [2,64] r2704 c2704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u176
  · exact u177

def r2705 : Route 9 := (fun mask => (mask,id))

def c2705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2705 : Upper (D 6) (R 6) [10,36,129,20,257,64,2] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,257,64,2] 13 (by decide) (choices 1) [32,64] r2705 c2705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u178
  · exact u179

def r2706 : Route 9 := (fun mask => (mask,id))

def c2706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2706 : Upper (D 6) (R 6) [10,36,129,20,257,64,32] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,257,64,32] 13 (by decide) (choices 1) [2,64] r2706 c2706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u180
  · exact u181

def b2707 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,0),(4,2)], upper := (rows 11 38 133 28 274 96 65 224 352), lower := (rows 11 38 133 28 274 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 96 64 224 352), good := (rows 26 446 132 28 282 480 480 128 256) }] }

theorem u2707 : Upper (D 6) (R 6) [10,36,129,20,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2708 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,1),(4,2)], upper := (rows 11 38 133 28 274 96 96 193 321), lower := (rows 11 38 133 28 274 96 96 128 256), losses := [] }

theorem u2708 : Upper (D 6) (R 6) [10,36,129,20,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2709 : Route 9 := (fun mask => (mask,id))

def c2709 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2709 : Upper (D 6) (R 6) [10,36,129,20,288,64,1] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,288,64,1] 13 (by decide) (choices 1) [2,64] r2709 c2709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u182
  · exact u183

def b2710 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 196, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(4,2)], upper := (rows 11 38 133 28 304 96 66 193 321), lower := (rows 11 38 133 28 304 96 66 128 256), losses := [] }

theorem u2710 : Upper (D 6) (R 6) [10,36,129,20,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2711 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(2,6),(4,2)], upper := (rows 11 38 133 28 336 96 65 162 290), lower := (rows 11 38 133 28 336 96 65 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 112 64 138 266), good := (rows 394 422 132 446 368 96 96 128 256) },{ target := 6, region := (rows 1 2 5 8 16 32 0 130 258), good := (rows 399 422 133 28 272 32 5 128 256) }] }

theorem u2711 : Upper (D 6) (R 6) [10,36,129,20,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2712 : Route 9 := (fun mask => (mask,id))

def c2712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2712 : Upper (D 6) (R 6) [10,36,129,20,320,64,2] 13 := by
  apply FastRouting.sound _ _ [10,36,129,20,320,64,2] 13 (by decide) (choices 1) [1,32] r2712 c2712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u184
  · exact u185

def b2713 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 38 133 28 336 96 96 131 259), lower := (rows 11 38 133 28 336 96 96 128 256), losses := [] }

theorem u2713 : Upper (D 6) (R 6) [10,36,129,20,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2714 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 133 76 49 288 66 208 336), lower := (rows 11 38 133 76 49 288 66 128 256), losses := [] }

theorem u2714 : Upper (D 6) (R 6) [10,36,129,68,33,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2714 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2715 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(4,2)], upper := (rows 11 38 133 76 49 288 80 194 322), lower := (rows 11 38 133 76 49 288 80 128 256), losses := [] }

theorem u2715 : Upper (D 6) (R 6) [10,36,129,68,33,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2715 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2716 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 133 76 82 288 65 176 304), lower := (rows 11 38 133 76 82 288 65 128 256), losses := [] }

theorem u2716 : Upper (D 6) (R 6) [10,36,129,68,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2716 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2717 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5)], upper := (rows 11 38 133 76 82 288 80 161 289), lower := (rows 11 38 133 76 82 288 80 128 256), losses := [] }

theorem u2717 : Upper (D 6) (R 6) [10,36,129,68,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2717 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2718 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 133 76 82 288 96 145 273), lower := (rows 11 38 133 76 82 288 96 128 256), losses := [] }

theorem u2718 : Upper (D 6) (R 6) [10,36,129,68,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2718 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2719 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 133 76 112 288 65 146 274), lower := (rows 11 38 133 76 112 288 65 128 256), losses := [] }

theorem u2719 : Upper (D 6) (R 6) [10,36,129,68,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2719 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2720 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 88, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 11 38 133 76 112 288 66 145 273), lower := (rows 11 38 133 76 112 288 66 128 256), losses := [] }

theorem u2720 : Upper (D 6) (R 6) [10,36,129,68,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2720 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2721 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 11 38 133 76 112 288 80 131 259), lower := (rows 11 38 133 76 112 288 80 128 256), losses := [] }

theorem u2721 : Upper (D 6) (R 6) [10,36,129,68,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2721 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2722 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 133 76 273 96 66 176 304), lower := (rows 11 38 133 76 273 96 66 128 256), losses := [] }

theorem u2722 : Upper (D 6) (R 6) [10,36,129,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2723 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(4,2)], upper := (rows 11 38 133 76 273 96 80 162 290), lower := (rows 11 38 133 76 273 96 80 128 256), losses := [] }

theorem u2723 : Upper (D 6) (R 6) [10,36,129,68,257,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2723 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2724 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 133 76 273 96 96 146 274), lower := (rows 11 38 133 76 273 96 96 128 256), losses := [] }

theorem u2724 : Upper (D 6) (R 6) [10,36,129,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2725 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 133 76 274 48 65 224 352), lower := (rows 11 38 133 76 274 48 65 128 256), losses := [] }

theorem u2725 : Upper (D 6) (R 6) [10,36,129,68,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2725 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2726 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0),(4,2)], upper := (rows 11 38 133 76 274 48 96 193 321), lower := (rows 11 38 133 76 274 48 96 128 256), losses := [] }

theorem u2726 : Upper (D 6) (R 6) [10,36,129,68,258,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2726 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2727 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 133 76 274 96 65 176 304), lower := (rows 11 38 133 76 274 96 65 128 256), losses := [] }

theorem u2727 : Upper (D 6) (R 6) [10,36,129,68,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2728 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(4,2)], upper := (rows 11 38 133 76 274 96 80 161 289), lower := (rows 11 38 133 76 274 96 80 128 256), losses := [] }

theorem u2728 : Upper (D 6) (R 6) [10,36,129,68,258,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2728 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2729 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 133 76 274 96 96 145 273), lower := (rows 11 38 133 76 274 96 96 128 256), losses := [] }

theorem u2729 : Upper (D 6) (R 6) [10,36,129,68,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2730 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 133 76 304 96 65 146 274), lower := (rows 11 38 133 76 304 96 65 128 256), losses := [] }

theorem u2730 : Upper (D 6) (R 6) [10,36,129,68,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2731 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 133 76 304 96 66 145 273), lower := (rows 11 38 133 76 304 96 66 128 256), losses := [] }

theorem u2731 : Upper (D 6) (R 6) [10,36,129,68,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2732 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 133 76 304 96 80 131 259), lower := (rows 11 38 133 76 304 96 80 128 256), losses := [] }

theorem u2732 : Upper (D 6) (R 6) [10,36,129,68,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2732 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2733 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 133 76 336 48 65 162 290), lower := (rows 11 38 133 76 336 48 65 128 256), losses := [] }

theorem u2733 : Upper (D 6) (R 6) [10,36,129,68,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2733 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2734 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 133 76 336 48 66 161 289), lower := (rows 11 38 133 76 336 48 66 128 256), losses := [] }

theorem u2734 : Upper (D 6) (R 6) [10,36,129,68,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2734 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2735 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 133 76 336 48 96 131 259), lower := (rows 11 38 133 76 336 48 96 128 256), losses := [] }

theorem u2735 : Upper (D 6) (R 6) [10,36,129,68,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2735 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2736 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 133 88 274 96 65 164 292), lower := (rows 11 38 133 88 274 96 65 128 256), losses := [] }

theorem u2736 : Upper (D 6) (R 6) [10,36,129,80,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2737 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 38 133 88 274 96 68 161 289), lower := (rows 11 38 133 88 274 96 68 128 256), losses := [{ target := 0, region := (rows 0 70 4 24 16 127 70 128 256), good := (rows 106 102 230 122 378 98 102 128 256) }] }

theorem u2737 : Upper (D 6) (R 6) [10,36,129,80,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2738 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 133 88 274 96 96 133 261), lower := (rows 11 38 133 88 274 96 96 128 256), losses := [] }

theorem u2738 : Upper (D 6) (R 6) [10,36,129,80,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2739 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 65 }], pairs := [(3,1),(4,0),(4,6)], upper := (rows 11 38 133 88 276 96 65 162 290), lower := (rows 11 38 133 88 276 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 127 69 128 256), good := (rows 105 100 229 120 380 96 97 128 256) }] }

theorem u2739 : Upper (D 6) (R 6) [10,36,129,80,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2740 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 38 133 88 276 96 66 161 289), lower := (rows 11 38 133 88 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 21 104 64 129 257), good := (rows 445 52 405 120 276 96 96 128 256) }] }

theorem u2740 : Upper (D 6) (R 6) [10,36,129,80,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2741 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 133 88 276 96 96 131 259), lower := (rows 11 38 133 88 276 96 96 128 256), losses := [] }

theorem u2741 : Upper (D 6) (R 6) [10,36,129,80,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2742 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 0, region := 132, targets := 32 }], pairs := [(2,5),(4,0),(4,6)], upper := (rows 11 38 133 88 304 96 65 134 262), lower := (rows 11 38 133 88 304 96 65 128 256), losses := [] }

theorem u2742 : Upper (D 6) (R 6) [10,36,129,80,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2743 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 66 },{ cop := 0, region := 132, targets := 32 }], pairs := [(2,1),(2,5),(2,6)], upper := (rows 11 38 133 88 304 96 66 133 261), lower := (rows 11 38 133 88 304 96 66 128 256), losses := [] }

theorem u2743 : Upper (D 6) (R 6) [10,36,129,80,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2744 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 132, targets := 32 },{ cop := 0, region := 132, targets := 64 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(2,6)], upper := (rows 11 38 133 88 304 96 68 131 259), lower := (rows 11 38 133 88 304 96 68 128 256), losses := [] }

theorem u2744 : Upper (D 6) (R 6) [10,36,129,80,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2745 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 4, region := 297, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 11 38 133 265 82 96 68 176 304), lower := (rows 11 38 133 265 82 96 68 128 256), losses := [] }

theorem u2745 : Upper (D 6) (R 6) [10,36,129,257,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2746 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 265 82 96 80 164 292), lower := (rows 11 38 133 265 82 96 80 128 256), losses := [] }

theorem u2746 : Upper (D 6) (R 6) [10,36,129,257,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2746 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2747 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 11 38 133 265 82 96 96 148 276), lower := (rows 11 38 133 265 82 96 96 128 256), losses := [] }

theorem u2747 : Upper (D 6) (R 6) [10,36,129,257,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2748 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 1, region := 80, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 11 38 133 265 84 96 66 176 304), lower := (rows 11 38 133 265 84 96 66 128 256), losses := [] }

theorem u2748 : Upper (D 6) (R 6) [10,36,129,257,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2749 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 265 84 96 80 162 290), lower := (rows 11 38 133 265 84 96 80 128 256), losses := [] }

theorem u2749 : Upper (D 6) (R 6) [10,36,129,257,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2749 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2750 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 265 84 96 96 146 274), lower := (rows 11 38 133 265 84 96 96 128 256), losses := [] }

theorem u2750 : Upper (D 6) (R 6) [10,36,129,257,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2751 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 112, targets := 4 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(4,2)], upper := (rows 11 38 133 268 49 96 66 208 336), lower := (rows 11 38 133 268 49 96 66 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 144 272), good := (rows 75 70 197 268 477 64 66 128 256) }] }

theorem u2751 : Upper (D 6) (R 6) [10,36,129,260,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2752 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 112, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 133 268 49 96 80 194 322), lower := (rows 11 38 133 268 49 96 80 128 256), losses := [] }

theorem u2752 : Upper (D 6) (R 6) [10,36,129,260,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2752 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2753 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 38 133 268 81 96 66 176 304), lower := (rows 11 38 133 268 81 96 66 128 256), losses := [] }

theorem u2753 : Upper (D 6) (R 6) [10,36,129,260,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2754 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 268 81 96 80 162 290), lower := (rows 11 38 133 268 81 96 80 128 256), losses := [] }

theorem u2754 : Upper (D 6) (R 6) [10,36,129,260,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2754 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2755 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 112, targets := 2 },{ cop := 0, region := 112, targets := 4 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 133 268 81 96 96 146 274), lower := (rows 11 38 133 268 81 96 96 128 256), losses := [] }

theorem u2755 : Upper (D 6) (R 6) [10,36,129,260,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2756 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,2),(4,5)], upper := (rows 11 38 133 268 82 48 65 224 352), lower := (rows 11 38 133 268 82 48 65 128 256), losses := [] }

theorem u2756 : Upper (D 6) (R 6) [10,36,129,260,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2756 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2757 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 133 268 82 48 96 193 321), lower := (rows 11 38 133 268 82 48 96 128 256), losses := [] }

theorem u2757 : Upper (D 6) (R 6) [10,36,129,260,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2757 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2758 : Route 9 := (fun mask => (mask,id))

def c2758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2758 : Upper (D 6) (R 6) [10,36,129,260,66,64,1] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260,66,64,1] 13 (by decide) (choices 1) [16,32] r2758 c2758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u186
  · exact u187

def b2759 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 268 82 96 80 161 289), lower := (rows 11 38 133 268 82 96 80 128 256), losses := [] }

theorem u2759 : Upper (D 6) (R 6) [10,36,129,260,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2759 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2759
end Delivery.IrregularNine14.P06
