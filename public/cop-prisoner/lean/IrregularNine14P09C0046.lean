import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0002
import IrregularNine14P09C0003

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2760 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 133 265 400 40 66 208 336), lower := (rows 97 38 133 265 400 40 66 128 256), losses := [] }

theorem u2760 : Upper (D 9) (R 9) [96,36,129,257,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2760 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2761 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 464, targets := 1 }], pairs := [(1,8),(2,8),(4,0)], upper := (rows 97 38 133 265 400 40 80 194 322), lower := (rows 97 38 133 265 400 40 80 128 256), losses := [] }

theorem u2761 : Upper (D 9) (R 9) [96,36,129,257,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2761 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2762 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 133 265 400 48 66 200 328), lower := (rows 97 38 133 265 400 48 66 128 256), losses := [] }

theorem u2762 : Upper (D 9) (R 9) [96,36,129,257,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2762 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2763 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 329, targets := 128 }], pairs := [(0,7),(1,8),(2,8)], upper := (rows 97 38 133 265 400 48 72 194 322), lower := (rows 97 38 133 265 400 48 72 128 256), losses := [] }

theorem u2763 : Upper (D 9) (R 9) [96,36,129,257,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2763 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2764 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 1, region := 65, targets := 384 }], pairs := [(0,7),(0,8),(2,5),(4,5)], upper := (rows 97 38 133 266 336 40 65 144 400), lower := (rows 97 38 133 266 336 40 65 128 256), losses := [] }

theorem u2764 : Upper (D 9) (R 9) [96,36,129,258,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2764 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2765 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 38 133 266 336 40 80 129 385), lower := (rows 97 38 133 266 336 40 80 128 256), losses := [] }

theorem u2765 : Upper (D 9) (R 9) [96,36,129,258,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2765 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2766 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 272, targets := 128 }], pairs := [(2,5),(3,5),(4,5),(4,7)], upper := (rows 97 38 133 266 336 40 192 145 273), lower := (rows 97 38 133 266 336 40 192 128 256), losses := [{ target := 5, region := (rows 1 2 5 10 31 0 199 133 261), good := (rows 469 478 469 346 336 24 192 192 256) }] }

theorem u2766 : Upper (D 9) (R 9) [96,36,129,258,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2766 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2767 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 1, region := 65, targets := 384 }], pairs := [(0,7),(0,8),(2,5),(4,5)], upper := (rows 97 38 133 266 400 40 65 208 336), lower := (rows 97 38 133 266 400 40 65 128 256), losses := [] }

theorem u2767 : Upper (D 9) (R 9) [96,36,129,258,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2767 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2768 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8),(2,5),(4,5)], upper := (rows 97 38 133 266 400 40 80 193 321), lower := (rows 97 38 133 266 400 40 80 128 256), losses := [] }

theorem u2768 : Upper (D 9) (R 9) [96,36,129,258,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2768 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2769 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 103, targets := 256 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 97 38 133 266 400 48 65 200 328), lower := (rows 97 38 133 266 400 48 65 128 256), losses := [] }

theorem u2769 : Upper (D 9) (R 9) [96,36,129,258,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2769 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2770 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8),(2,5),(4,5)], upper := (rows 97 38 133 266 400 48 72 193 321), lower := (rows 97 38 133 266 400 48 72 128 256), losses := [] }

theorem u2770 : Upper (D 9) (R 9) [96,36,129,258,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2770 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2771 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 103, targets := 256 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 97 38 133 328 400 48 65 138 266), lower := (rows 97 38 133 328 400 48 65 128 256), losses := [] }

theorem u2771 : Upper (D 9) (R 9) [96,36,129,320,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2771 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2772 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 133 328 400 48 66 137 265), lower := (rows 97 38 133 328 400 48 66 128 256), losses := [] }

theorem u2772 : Upper (D 9) (R 9) [96,36,129,320,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2772 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2773 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 38 133 328 400 48 72 131 259), lower := (rows 97 38 133 328 400 48 72 128 256), losses := [] }

theorem u2773 : Upper (D 9) (R 9) [96,36,129,320,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2773 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2774 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 1, region := 65, targets := 384 },{ cop := 3, region := 336, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 137 280 288 65 208 336), lower := (rows 97 38 134 137 280 288 65 128 256), losses := [] }

theorem u2774 : Upper (D 9) (R 9) [96,36,130,129,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2774 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2775 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 38 134 137 280 288 80 193 321), lower := (rows 97 38 134 137 280 288 80 128 256), losses := [] }

theorem u2775 : Upper (D 9) (R 9) [96,36,130,129,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2775 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2776 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 1, region := 65, targets := 384 },{ cop := 3, region := 336, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 137 336 288 65 152 280), lower := (rows 97 38 134 137 336 288 65 128 256), losses := [] }

theorem u2776 : Upper (D 9) (R 9) [96,36,130,129,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2776 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2777 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 137 336 288 72 145 273), lower := (rows 97 38 134 137 336 288 72 128 256), losses := [] }

theorem u2777 : Upper (D 9) (R 9) [96,36,130,129,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2777 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2778 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 38 134 137 336 288 80 137 265), lower := (rows 97 38 134 137 336 288 80 128 256), losses := [] }

theorem u2778 : Upper (D 9) (R 9) [96,36,130,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2778 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2779 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 1, region := 65, targets := 384 },{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 200 280 288 65 145 273), lower := (rows 97 38 134 200 280 288 65 128 256), losses := [] }

theorem u2779 : Upper (D 9) (R 9) [96,36,130,192,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2779 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2780 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 38 134 200 280 288 80 129 257), lower := (rows 97 38 134 200 280 288 80 128 256), losses := [] }

theorem u2780 : Upper (D 9) (R 9) [96,36,130,192,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2780 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2781 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 33, targets := 256 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(2,5),(3,7)], upper := (rows 97 38 140 88 146 33 320 385 257), lower := (rows 97 38 140 88 146 33 320 128 256), losses := [{ target := 5, region := (rows 1 2 22 26 18 0 355 161 289), good := (rows 449 478 140 92 222 449 320 128 320) }] }

theorem u2781 : Upper (D 9) (R 9) [96,36,136,80,130,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2781 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2782 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 38 140 88 146 288 320 129 257), lower := (rows 97 38 140 88 146 288 320 128 256), losses := [] }

theorem u2782 : Upper (D 9) (R 9) [96,36,136,80,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2782 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2783 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,5),(3,5)], upper := (rows 97 38 140 88 274 33 192 385 257), lower := (rows 97 38 140 88 274 33 192 128 256), losses := [{ target := 5, region := (rows 1 2 6 26 18 0 231 161 289), good := (rows 449 478 204 88 350 449 192 192 256) }] }

theorem u2783 : Upper (D 9) (R 9) [96,36,136,80,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2783 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2784 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 193, targets := 256 },{ cop := 3, region := 289, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(2,8),(4,7)], upper := (rows 97 38 140 88 274 288 192 129 257), lower := (rows 97 38 140 88 274 288 192 128 256), losses := [{ target := 7, region := (rows 73 6 4 8 22 383 64 0 333), good := (rows 353 310 319 377 306 288 353 0 288) },{ target := 8, region := (rows 35 2 28 24 16 32 255 179 0), good := (rows 225 231 204 220 223 225 192 192 0) }] }

theorem u2784 : Upper (D 9) (R 9) [96,36,136,80,258,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2784 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2785 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 38 140 88 400 33 65 386 258), lower := (rows 97 38 140 88 400 33 65 128 256), losses := [] }

theorem u2785 : Upper (D 9) (R 9) [96,36,136,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2785 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2786 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 38 140 88 400 33 66 385 257), lower := (rows 97 38 140 88 400 33 66 128 256), losses := [] }

theorem u2786 : Upper (D 9) (R 9) [96,36,136,80,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2786 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2787 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 76, targets := 33 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,8),(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 38 140 88 400 33 320 131 259), lower := (rows 97 38 140 88 400 33 320 128 256), losses := [] }

theorem u2787 : Upper (D 9) (R 9) [96,36,136,80,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2787 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2788 : Route 9 := (fun mask => (mask,id))

def c2788 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2788 : Upper (D 9) (R 9) [96,36,136,80,384,256,1] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,384,256,1] 13 (by decide) (choices 1) [1,2] r2788 c2788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u173
  · exact u174

def b2789 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 4, region := 110, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 88 400 288 66 129 257), lower := (rows 97 38 140 88 400 288 66 128 256), losses := [] }

theorem u2789 : Upper (D 9) (R 9) [96,36,136,80,384,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2789 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2790 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 140 265 145 48 66 448 320), lower := (rows 97 38 140 265 145 48 66 128 256), losses := [] }

theorem u2790 : Upper (D 9) (R 9) [96,36,136,257,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2790 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2791 : Route 9 := (fun mask => (mask,id))

def c2791 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2791 : Upper (D 9) (R 9) [96,36,136,257,129,16,256] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,129,16,256] 13 (by decide) (choices 1) [2,64] r2791 c2791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u175
  · exact u176

def r2792 : Route 9 := (fun mask => (mask,id))

def c2792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2792 : Upper (D 9) (R 9) [96,36,136,257,384,16,1] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,384,16,1] 13 (by decide) (choices 1) [2,64] r2792 c2792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u177
  · exact u178

def b2793 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 140 265 400 48 66 193 321), lower := (rows 97 38 140 265 400 48 66 128 256), losses := [] }

theorem u2793 : Upper (D 9) (R 9) [96,36,136,257,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2793 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2794 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 2, region := 113, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0)], upper := (rows 97 38 140 266 145 48 65 448 320), lower := (rows 97 38 140 266 145 48 65 128 256), losses := [] }

theorem u2794 : Upper (D 9) (R 9) [96,36,136,258,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2794 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2795 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 329, targets := 128 },{ cop := 6, region := 177, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,8)], upper := (rows 97 38 140 266 145 48 320 193 321), lower := (rows 97 38 140 266 145 48 320 128 256), losses := [] }

theorem u2795 : Upper (D 9) (R 9) [96,36,136,258,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2795 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2796 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0)], upper := (rows 97 38 140 266 273 48 65 192 448), lower := (rows 97 38 140 266 273 48 65 128 256), losses := [] }

theorem u2796 : Upper (D 9) (R 9) [96,36,136,258,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2796 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2797 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 305, targets := 128 },{ cop := 0, region := 272, targets := 32 },{ cop := 1, region := 193, targets := 256 }], pairs := [(0,7),(0,8),(4,5),(4,7)], upper := (rows 97 38 140 266 273 48 192 193 321), lower := (rows 97 38 140 266 273 48 192 128 256), losses := [] }

theorem u2797 : Upper (D 9) (R 9) [96,36,136,258,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2797 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2798 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 280 145 33 66 448 320), lower := (rows 97 38 140 280 145 33 66 128 256), losses := [] }

theorem u2798 : Upper (D 9) (R 9) [96,36,136,272,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2798 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2799 : Route 9 := (fun mask => (mask,id))

def c2799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2799 : Upper (D 9) (R 9) [96,36,136,272,129,1,256] 13 := by
  apply FastRouting.sound _ _ [96,36,136,272,129,1,256] 13 (by decide) (choices 1) [2,64] r2799 c2799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u179
  · exact u180

def b2800 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 2, region := 97, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 38 140 280 208 33 65 386 258), lower := (rows 97 38 140 280 208 33 65 128 256), losses := [] }

theorem u2800 : Upper (D 9) (R 9) [96,36,136,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2800 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2801 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 140 280 208 33 66 385 257), lower := (rows 97 38 140 280 208 33 66 128 256), losses := [] }

theorem u2801 : Upper (D 9) (R 9) [96,36,136,272,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2801 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2802 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,0),(4,5)], upper := (rows 97 38 140 280 208 33 320 131 259), lower := (rows 97 38 140 280 208 33 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 328 128 256), good := (rows 96 54 220 344 208 32 320 128 320) },{ target := 5, region := (rows 1 2 4 8 20 0 328 128 256), good := (rows 65 22 220 344 208 1 320 128 320) }] }

theorem u2802 : Upper (D 9) (R 9) [96,36,136,272,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2802 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2803 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 2, region := 113, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0)], upper := (rows 97 38 140 328 145 48 65 386 258), lower := (rows 97 38 140 328 145 48 65 128 256), losses := [] }

theorem u2803 : Upper (D 9) (R 9) [96,36,136,320,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2803 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2804 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 140 328 145 48 66 385 257), lower := (rows 97 38 140 328 145 48 66 128 256), losses := [] }

theorem u2804 : Upper (D 9) (R 9) [96,36,136,320,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2804 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2805 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 183, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 38 140 328 145 48 320 131 259), lower := (rows 97 38 140 328 145 48 320 128 256), losses := [] }

theorem u2805 : Upper (D 9) (R 9) [96,36,136,320,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2805 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2806 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 38 140 328 274 33 65 144 400), lower := (rows 97 38 140 328 274 33 65 128 256), losses := [] }

theorem u2806 : Upper (D 9) (R 9) [96,36,136,320,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2806 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2807 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 0, region := 396, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8)], upper := (rows 97 38 140 328 274 33 80 129 385), lower := (rows 97 38 140 328 274 33 80 128 256), losses := [] }

theorem u2807 : Upper (D 9) (R 9) [96,36,136,320,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2807 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2808 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 97 38 140 328 274 33 192 145 273), lower := (rows 97 38 140 328 274 33 192 128 256), losses := [{ target := 7, region := (rows 73 6 4 8 22 109 64 0 260), good := (rows 97 310 319 361 274 33 97 0 256) }] }

theorem u2808 : Upper (D 9) (R 9) [96,36,136,320,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2808 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2809 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(3,7)], upper := (rows 97 38 140 328 274 48 65 129 385), lower := (rows 97 38 140 328 274 48 65 128 256), losses := [] }

theorem u2809 : Upper (D 9) (R 9) [96,36,136,320,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2809 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2810 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 0, region := 264, targets := 128 },{ cop := 1, region := 193, targets := 256 }], pairs := [(0,8),(2,5),(3,5),(3,7)], upper := (rows 97 38 140 328 274 48 192 129 257), lower := (rows 97 38 140 328 274 48 192 128 256), losses := [] }

theorem u2810 : Upper (D 9) (R 9) [96,36,136,320,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2810 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2811 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 38 140 328 400 33 65 146 274), lower := (rows 97 38 140 328 400 33 65 128 256), losses := [] }

theorem u2811 : Upper (D 9) (R 9) [96,36,136,320,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2811 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2812 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 140 328 400 33 66 145 273), lower := (rows 97 38 140 328 400 33 66 128 256), losses := [] }

theorem u2812 : Upper (D 9) (R 9) [96,36,136,320,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2812 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2813 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 38 140 328 400 33 80 131 259), lower := (rows 97 38 140 328 400 33 80 128 256), losses := [] }

theorem u2813 : Upper (D 9) (R 9) [96,36,136,320,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2813 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2814 : Route 9 := (fun mask => (mask,id))

def c2814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2814 : Upper (D 9) (R 9) [96,36,136,320,384,16,1] 13 := by
  apply FastRouting.sound _ _ [96,36,136,320,384,16,1] 13 (by decide) (choices 1) [1,2] r2814 c2814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u181
  · exact u182

def b2815 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 140 328 400 48 66 129 257), lower := (rows 97 38 140 328 400 48 66 128 256), losses := [] }

theorem u2815 : Upper (D 9) (R 9) [96,36,136,320,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2815 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2816 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 196 137 273 48 66 392 264), lower := (rows 97 38 196 137 273 48 66 128 256), losses := [] }

theorem u2816 : Upper (D 9) (R 9) [96,36,192,129,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2816 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2817 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 97 38 196 137 273 48 72 386 258), lower := (rows 97 38 196 137 273 48 72 128 256), losses := [] }

theorem u2817 : Upper (D 9) (R 9) [96,36,192,129,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2817 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2818 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 6, region := 49, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 137 273 48 320 138 266), lower := (rows 97 38 196 137 273 48 320 128 256), losses := [] }

theorem u2818 : Upper (D 9) (R 9) [96,36,192,129,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2818 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2819 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(2,5),(3,5),(3,6),(4,5)], upper := (rows 97 38 196 137 273 288 66 152 280), lower := (rows 97 38 196 137 273 288 66 128 256), losses := [] }

theorem u2819 : Upper (D 9) (R 9) [96,36,192,129,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2819 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2819
end Delivery.IrregularNine14.P09
