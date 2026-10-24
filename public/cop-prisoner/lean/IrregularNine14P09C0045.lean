import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0002

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2700 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 76 392 145 33 66 400 272), lower := (rows 97 38 76 392 145 33 66 128 256), losses := [] }

theorem u2700 : Upper (D 9) (R 9) [96,36,72,384,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2700 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2701 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 38 76 392 145 33 80 386 258), lower := (rows 97 38 76 392 145 33 80 128 256), losses := [] }

theorem u2701 : Upper (D 9) (R 9) [96,36,72,384,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2701 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2702 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,8)], upper := (rows 97 38 76 392 145 33 320 146 274), lower := (rows 97 38 76 392 145 33 320 128 256), losses := [] }

theorem u2702 : Upper (D 9) (R 9) [96,36,72,384,129,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2702 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2703 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 38 76 392 145 48 65 386 258), lower := (rows 97 38 76 392 145 48 65 128 256), losses := [] }

theorem u2703 : Upper (D 9) (R 9) [96,36,72,384,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2703 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2704 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 38 76 392 145 48 66 385 257), lower := (rows 97 38 76 392 145 48 66 128 256), losses := [] }

theorem u2704 : Upper (D 9) (R 9) [96,36,72,384,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2704 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2705 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(4,8)], upper := (rows 97 38 76 392 145 48 320 131 259), lower := (rows 97 38 76 392 145 48 320 128 256), losses := [] }

theorem u2705 : Upper (D 9) (R 9) [96,36,72,384,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2705 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2706 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 408, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0),(4,5)], upper := (rows 97 38 76 392 146 33 65 400 272), lower := (rows 97 38 76 392 146 33 65 128 256), losses := [] }

theorem u2706 : Upper (D 9) (R 9) [96,36,72,384,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2706 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2707 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 38 76 392 146 33 80 385 257), lower := (rows 97 38 76 392 146 33 80 128 256), losses := [] }

theorem u2707 : Upper (D 9) (R 9) [96,36,72,384,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2707 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2708 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,8)], upper := (rows 97 38 76 392 146 33 320 145 273), lower := (rows 97 38 76 392 146 33 320 128 256), losses := [] }

theorem u2708 : Upper (D 9) (R 9) [96,36,72,384,130,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2708 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2709 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(3,7),(4,5)], upper := (rows 97 38 133 88 146 288 65 392 264), lower := (rows 97 38 133 88 146 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 69 154 282), good := (rows 65 478 197 472 410 256 65 128 256) }] }

theorem u2709 : Upper (D 9) (R 9) [96,36,129,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2709 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2710 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 4, region := 72, targets := 1 }], pairs := [(1,6),(2,6),(3,0),(4,6)], upper := (rows 97 38 133 88 146 288 72 385 257), lower := (rows 97 38 133 88 146 288 72 128 256), losses := [] }

theorem u2710 : Upper (D 9) (R 9) [96,36,129,80,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2710 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2711 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 38 133 88 146 288 320 137 265), lower := (rows 97 38 133 88 146 288 320 128 256), losses := [] }

theorem u2711 : Upper (D 9) (R 9) [96,36,129,80,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2711 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2712 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 88, targets := 288 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(3,5),(3,8),(4,5),(4,8)], upper := (rows 97 38 133 88 152 288 65 386 258), lower := (rows 97 38 133 88 152 288 65 128 256), losses := [] }

theorem u2712 : Upper (D 9) (R 9) [96,36,129,80,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2712 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2713 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 88 152 288 66 385 257), lower := (rows 97 38 133 88 152 288 66 128 256), losses := [] }

theorem u2713 : Upper (D 9) (R 9) [96,36,129,80,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2713 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2714 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 38 133 88 152 288 320 131 259), lower := (rows 97 38 133 88 152 288 320 128 256), losses := [] }

theorem u2714 : Upper (D 9) (R 9) [96,36,129,80,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2714 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2715 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 6, region := 39, targets := 256 }], pairs := [(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 88 273 34 192 392 264), lower := (rows 97 38 133 88 273 34 192 128 256), losses := [] }

theorem u2715 : Upper (D 9) (R 9) [96,36,129,80,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2715 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2716 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 38 133 88 273 40 192 386 258), lower := (rows 97 38 133 88 273 40 192 128 256), losses := [] }

theorem u2716 : Upper (D 9) (R 9) [96,36,129,80,257,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2716 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2717 : Route 9 := (fun mask => (mask,id))

def c2717 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2717 : Upper (D 9) (R 9) [96,36,129,80,257,256,128] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,257,256,128] 13 (by decide) (choices 1) [2,8] r2717 c2717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u169
  · exact u170

def b2718 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(3,7),(4,5)], upper := (rows 97 38 133 88 274 288 65 136 392), lower := (rows 97 38 133 88 274 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 69 154 282), good := (rows 65 478 197 472 410 256 65 128 256) }] }

theorem u2718 : Upper (D 9) (R 9) [96,36,129,80,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2718 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2719 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 0, region := 134, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(4,6)], upper := (rows 97 38 133 88 274 288 72 129 385), lower := (rows 97 38 133 88 274 288 72 128 256), losses := [] }

theorem u2719 : Upper (D 9) (R 9) [96,36,129,80,258,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2719 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2720 : Route 9 := (fun mask => (mask,id))

def c2720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2720 : Upper (D 9) (R 9) [96,36,129,80,258,256,128] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,258,256,128] 13 (by decide) (choices 1) [1,8] r2720 c2720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u171
  · exact u172

def b2721 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(3,7),(4,5)], upper := (rows 97 38 133 88 400 288 65 138 266), lower := (rows 97 38 133 88 400 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 69 130 258), good := (rows 65 478 197 88 400 256 65 128 256) }] }

theorem u2721 : Upper (D 9) (R 9) [96,36,129,80,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2721 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2722 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 88 400 288 66 137 265), lower := (rows 97 38 133 88 400 288 66 128 256), losses := [] }

theorem u2722 : Upper (D 9) (R 9) [96,36,129,80,384,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2722 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2723 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 0, region := 134, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(4,6)], upper := (rows 97 38 133 88 400 288 72 131 259), lower := (rows 97 38 133 88 400 288 72 128 256), losses := [] }

theorem u2723 : Upper (D 9) (R 9) [96,36,129,80,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2723 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2724 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(2,5),(4,5),(4,7)], upper := (rows 97 38 133 138 273 288 72 208 336), lower := (rows 97 38 133 138 273 288 72 128 256), losses := [] }

theorem u2724 : Upper (D 9) (R 9) [96,36,129,130,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2724 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2725 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 133 138 273 288 80 200 328), lower := (rows 97 38 133 138 273 288 80 128 256), losses := [] }

theorem u2725 : Upper (D 9) (R 9) [96,36,129,130,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2725 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2726 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,7)], upper := (rows 97 38 133 138 280 288 65 208 336), lower := (rows 97 38 133 138 280 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 26 0 69 130 258), good := (rows 65 478 197 410 280 256 65 128 256) }] }

theorem u2726 : Upper (D 9) (R 9) [96,36,129,130,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2726 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2727 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 133 138 280 288 80 193 321), lower := (rows 97 38 133 138 280 288 80 128 256), losses := [] }

theorem u2727 : Upper (D 9) (R 9) [96,36,129,130,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2727 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2728 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,7)], upper := (rows 97 38 133 138 336 288 65 152 280), lower := (rows 97 38 133 138 336 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 69 138 266), good := (rows 65 478 197 410 336 256 65 128 256) }] }

theorem u2728 : Upper (D 9) (R 9) [96,36,129,130,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2728 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2729 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(2,5),(4,5),(4,7)], upper := (rows 97 38 133 138 336 288 72 145 273), lower := (rows 97 38 133 138 336 288 72 128 256), losses := [] }

theorem u2729 : Upper (D 9) (R 9) [96,36,129,130,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2729 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2730 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 38 133 138 336 288 80 137 265), lower := (rows 97 38 133 138 336 288 80 128 256), losses := [] }

theorem u2730 : Upper (D 9) (R 9) [96,36,129,130,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2730 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2731 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 133 152 273 40 66 448 320), lower := (rows 97 38 133 152 273 40 66 128 256), losses := [] }

theorem u2731 : Upper (D 9) (R 9) [96,36,129,144,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2731 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2732 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(4,7)], upper := (rows 97 38 133 152 273 40 320 194 322), lower := (rows 97 38 133 152 273 40 320 128 256), losses := [] }

theorem u2732 : Upper (D 9) (R 9) [96,36,129,144,257,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2732 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2733 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 152 273 288 66 200 328), lower := (rows 97 38 133 152 273 288 66 128 256), losses := [] }

theorem u2733 : Upper (D 9) (R 9) [96,36,129,144,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2733 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2734 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 133 152 273 288 72 194 322), lower := (rows 97 38 133 152 273 288 72 128 256), losses := [{ target := 7, region := (rows 9 2 4 8 16 304 72 0 256), good := (rows 97 38 5 121 305 288 73 0 288) },{ target := 8, region := (rows 1 3 21 24 16 32 88 145 0), good := (rows 231 38 135 220 223 32 72 128 0) }] }

theorem u2734 : Upper (D 9) (R 9) [96,36,129,144,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2734 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2735 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 65, targets := 384 }], pairs := [(0,7),(0,8),(2,8),(3,5),(4,5)], upper := (rows 97 38 133 152 274 288 65 200 328), lower := (rows 97 38 133 152 274 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 26 18 0 69 130 258), good := (rows 65 478 197 152 410 256 65 128 256) },{ target := 8, region := (rows 35 2 20 24 16 32 119 152 0), good := (rows 97 103 197 220 223 97 65 128 0) }] }

theorem u2735 : Upper (D 9) (R 9) [96,36,129,144,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2735 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2736 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 0, region := 132, targets := 32 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,5),(2,8)], upper := (rows 97 38 133 152 274 288 72 193 321), lower := (rows 97 38 133 152 274 288 72 128 256), losses := [] }

theorem u2736 : Upper (D 9) (R 9) [96,36,129,144,258,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2736 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2737 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 5, region := 81, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,7)], upper := (rows 97 38 133 152 336 288 65 138 266), lower := (rows 97 38 133 152 336 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 69 130 258), good := (rows 65 478 197 152 336 256 65 128 256) }] }

theorem u2737 : Upper (D 9) (R 9) [96,36,129,144,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2737 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2738 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 152 336 288 66 137 265), lower := (rows 97 38 133 152 336 288 66 128 256), losses := [] }

theorem u2738 : Upper (D 9) (R 9) [96,36,129,144,320,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2738 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2739 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 134, targets := 64 },{ cop := 0, region := 134, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 38 133 152 336 288 72 131 259), lower := (rows 97 38 133 152 336 288 72 128 256), losses := [] }

theorem u2739 : Upper (D 9) (R 9) [96,36,129,144,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2739 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2740 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 133 200 273 48 66 392 264), lower := (rows 97 38 133 200 273 48 66 128 256), losses := [] }

theorem u2740 : Upper (D 9) (R 9) [96,36,129,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2740 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2741 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 38 133 200 273 48 72 386 258), lower := (rows 97 38 133 200 273 48 72 128 256), losses := [] }

theorem u2741 : Upper (D 9) (R 9) [96,36,129,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2741 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2742 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 456, targets := 1 }], pairs := [(1,8),(2,8),(3,0),(3,8)], upper := (rows 97 38 133 200 273 48 320 138 266), lower := (rows 97 38 133 200 273 48 320 128 256), losses := [] }

theorem u2742 : Upper (D 9) (R 9) [96,36,129,192,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2742 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2743 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 200 273 288 66 152 280), lower := (rows 97 38 133 200 273 288 66 128 256), losses := [] }

theorem u2743 : Upper (D 9) (R 9) [96,36,129,192,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2743 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2744 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 2, region := 72, targets := 1 }], pairs := [(1,6),(2,6),(3,0),(4,6)], upper := (rows 97 38 133 200 273 288 72 146 274), lower := (rows 97 38 133 200 273 288 72 128 256), losses := [] }

theorem u2744 : Upper (D 9) (R 9) [96,36,129,192,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2744 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2745 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 5, region := 81, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 133 200 273 288 80 138 266), lower := (rows 97 38 133 200 273 288 80 128 256), losses := [] }

theorem u2745 : Upper (D 9) (R 9) [96,36,129,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2745 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2746 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 1, region := 65, targets := 384 }], pairs := [(0,7),(0,8),(2,5),(3,5)], upper := (rows 97 38 133 200 274 48 65 392 264), lower := (rows 97 38 133 200 274 48 65 128 256), losses := [] }

theorem u2746 : Upper (D 9) (R 9) [96,36,129,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2746 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2747 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 38 133 200 274 48 72 385 257), lower := (rows 97 38 133 200 274 48 72 128 256), losses := [] }

theorem u2747 : Upper (D 9) (R 9) [96,36,129,192,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2747 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2748 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 140, targets := 32 }], pairs := [(1,8),(2,5),(2,8),(3,8)], upper := (rows 97 38 133 200 274 48 320 137 265), lower := (rows 97 38 133 200 274 48 320 128 256), losses := [] }

theorem u2748 : Upper (D 9) (R 9) [96,36,129,192,258,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2748 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2749 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 2, region := 72, targets := 288 }], pairs := [(0,7),(0,8),(3,5),(3,8),(4,5)], upper := (rows 97 38 133 200 274 288 65 152 280), lower := (rows 97 38 133 200 274 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 14 18 0 69 146 274), good := (rows 65 478 205 200 410 256 65 128 256) }] }

theorem u2749 : Upper (D 9) (R 9) [96,36,129,192,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2749 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2750 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 2, region := 72, targets := 1 }], pairs := [(1,6),(2,6),(3,0),(4,6)], upper := (rows 97 38 133 200 274 288 72 145 273), lower := (rows 97 38 133 200 274 288 72 128 256), losses := [] }

theorem u2750 : Upper (D 9) (R 9) [96,36,129,192,258,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2750 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2751 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 140, targets := 32 }], pairs := [(1,8),(2,5),(2,8),(3,8)], upper := (rows 97 38 133 200 274 288 80 137 265), lower := (rows 97 38 133 200 274 288 80 128 256), losses := [] }

theorem u2751 : Upper (D 9) (R 9) [96,36,129,192,258,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2751 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2752 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 72, targets := 288 }], pairs := [(1,6),(2,6),(3,5),(3,8)], upper := (rows 97 38 133 200 280 48 65 386 258), lower := (rows 97 38 133 200 280 48 65 128 256), losses := [] }

theorem u2752 : Upper (D 9) (R 9) [96,36,129,192,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2752 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2753 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 133 200 280 48 66 385 257), lower := (rows 97 38 133 200 280 48 66 128 256), losses := [] }

theorem u2753 : Upper (D 9) (R 9) [96,36,129,192,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2753 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2754 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(1,8),(2,8),(3,8)], upper := (rows 97 38 133 200 280 48 320 131 259), lower := (rows 97 38 133 200 280 48 320 128 256), losses := [] }

theorem u2754 : Upper (D 9) (R 9) [96,36,129,192,264,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2754 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2755 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 2, region := 72, targets := 288 }], pairs := [(0,7),(0,8),(3,5),(3,8),(4,5)], upper := (rows 97 38 133 200 280 288 65 146 274), lower := (rows 97 38 133 200 280 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 14 18 0 69 130 258), good := (rows 65 478 205 200 280 256 65 128 256) }] }

theorem u2755 : Upper (D 9) (R 9) [96,36,129,192,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2755 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2756 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 97 38 133 200 280 288 66 145 273), lower := (rows 97 38 133 200 280 288 66 128 256), losses := [] }

theorem u2756 : Upper (D 9) (R 9) [96,36,129,192,264,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2756 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2757 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(1,8),(2,8),(3,8)], upper := (rows 97 38 133 200 280 288 80 131 259), lower := (rows 97 38 133 200 280 288 80 128 256), losses := [] }

theorem u2757 : Upper (D 9) (R 9) [96,36,129,192,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2757 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2758 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8),(2,5),(3,5)], upper := (rows 97 38 133 265 274 40 80 192 448), lower := (rows 97 38 133 265 274 40 80 128 256), losses := [] }

theorem u2758 : Upper (D 9) (R 9) [96,36,129,257,258,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2758 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2759 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 464, targets := 33 }], pairs := [(0,8),(2,8),(4,0),(4,5)], upper := (rows 97 38 133 265 274 40 192 208 336), lower := (rows 97 38 133 265 274 40 192 128 256), losses := [{ target := 8, region := (rows 3 2 20 8 16 40 212 144 0), good := (rows 97 103 197 41 215 40 192 192 0) }] }

theorem u2759 : Upper (D 9) (R 9) [96,36,129,257,258,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2759 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2759
end Delivery.IrregularNine14.P09
