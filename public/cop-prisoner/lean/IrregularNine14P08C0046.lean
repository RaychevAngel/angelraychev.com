import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0005
import IrregularNine14P08C0006

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2760 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 7 164 200 304 48 105 169 297), lower := (rows 67 7 164 200 304 48 64 128 256), losses := [] }

theorem u2760 : Upper (D 8) (R 8) [66,5,160,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2760 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2761 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 56 208 33 224 160 416), lower := (rows 67 7 268 56 208 33 64 128 256), losses := [] }

theorem u2761 : Upper (D 8) (R 8) [66,5,264,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2762 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 268 56 208 160 97 161 289), lower := (rows 67 7 268 56 208 160 64 128 256), losses := [] }

theorem u2762 : Upper (D 8) (R 8) [66,5,264,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2763 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 152 112 33 224 160 416), lower := (rows 67 7 268 152 112 33 64 128 256), losses := [] }

theorem u2763 : Upper (D 8) (R 8) [66,5,264,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2764 : Route 9 := (fun mask => (mask,id))

def c2764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2764 : Upper (D 8) (R 8) [66,5,264,144,96,128] 13 := by
  apply FastRouting.sound _ _ [66,5,264,144,96,128] 13 (by decide) (choices 1) [1,32] r2764 c2764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u349
  · exact u350

def b2765 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 168 112 33 240 176 432), lower := (rows 67 7 268 168 112 33 64 128 256), losses := [] }

theorem u2765 : Upper (D 8) (R 8) [66,5,264,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2766 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 268 168 112 48 225 161 417), lower := (rows 67 7 268 168 112 48 64 128 256), losses := [] }

theorem u2766 : Upper (D 8) (R 8) [66,5,264,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2766 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2767 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 268 168 112 160 113 177 305), lower := (rows 67 7 268 168 112 160 64 128 256), losses := [] }

theorem u2767 : Upper (D 8) (R 8) [66,5,264,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2768 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 268 168 208 33 112 176 304), lower := (rows 67 7 268 168 208 33 64 128 256), losses := [] }

theorem u2768 : Upper (D 8) (R 8) [66,5,264,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2769 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 268 168 208 48 97 161 289), lower := (rows 67 7 268 168 208 48 64 128 256), losses := [] }

theorem u2769 : Upper (D 8) (R 8) [66,5,264,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2769 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2770 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 56 152 33 224 224 480), lower := (rows 67 7 292 56 152 33 64 128 256), losses := [] }

theorem u2770 : Upper (D 8) (R 8) [66,5,288,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2771 : Route 9 := (fun mask => (mask,id))

def c2771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2771 : Upper (D 8) (R 8) [66,5,288,48,136,64] 13 := by
  apply FastRouting.sound _ _ [66,5,288,48,136,64] 13 (by decide) (choices 1) [1,32,128] r2771 c2771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u351
  · exact u352
  · exact u353

def b2772 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 292 56 152 160 97 225 353), lower := (rows 67 7 292 56 152 160 64 128 256), losses := [] }

theorem u2772 : Upper (D 8) (R 8) [66,5,288,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2773 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 56 208 33 232 168 424), lower := (rows 67 7 292 56 208 33 64 128 256), losses := [] }

theorem u2773 : Upper (D 8) (R 8) [66,5,288,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2774 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 292 56 208 40 225 161 417), lower := (rows 67 7 292 56 208 40 64 128 256), losses := [] }

theorem u2774 : Upper (D 8) (R 8) [66,5,288,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2774 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2775 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 292 56 208 160 105 169 297), lower := (rows 67 7 292 56 208 160 64 128 256), losses := [] }

theorem u2775 : Upper (D 8) (R 8) [66,5,288,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2776 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 88 176 33 232 168 424), lower := (rows 67 7 292 88 176 33 64 128 256), losses := [] }

theorem u2776 : Upper (D 8) (R 8) [66,5,288,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2777 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 292 88 176 40 225 161 417), lower := (rows 67 7 292 88 176 40 64 128 256), losses := [] }

theorem u2777 : Upper (D 8) (R 8) [66,5,288,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2777 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2778 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 292 88 176 160 105 169 297), lower := (rows 67 7 292 88 176 160 64 128 256), losses := [] }

theorem u2778 : Upper (D 8) (R 8) [66,5,288,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2779 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 104 152 33 240 176 432), lower := (rows 67 7 292 104 152 33 64 128 256), losses := [] }

theorem u2779 : Upper (D 8) (R 8) [66,5,288,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2780 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 292 104 152 48 225 161 417), lower := (rows 67 7 292 104 152 48 64 128 256), losses := [] }

theorem u2780 : Upper (D 8) (R 8) [66,5,288,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2780 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2781 : Route 9 := (fun mask => (mask,id))

def c2781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2781 : Upper (D 8) (R 8) [66,5,288,96,136,128] 13 := by
  apply FastRouting.sound _ _ [66,5,288,96,136,128] 13 (by decide) (choices 1) [1,16,32] r2781 c2781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u354
  · exact u355
  · exact u356

def b2782 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 104 176 33 216 152 408), lower := (rows 67 7 292 104 176 33 64 128 256), losses := [] }

theorem u2782 : Upper (D 8) (R 8) [66,5,288,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2783 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 7 292 104 176 40 209 145 401), lower := (rows 67 7 292 104 176 40 64 128 256), losses := [] }

theorem u2783 : Upper (D 8) (R 8) [66,5,288,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2783 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2784 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 7 292 104 176 48 201 137 393), lower := (rows 67 7 292 104 176 48 64 128 256), losses := [] }

theorem u2784 : Upper (D 8) (R 8) [66,5,288,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2784 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2785 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 292 104 176 160 89 153 281), lower := (rows 67 7 292 104 176 160 64 128 256), losses := [] }

theorem u2785 : Upper (D 8) (R 8) [66,5,288,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2786 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 168 208 33 120 184 312), lower := (rows 67 7 292 168 208 33 64 128 256), losses := [] }

theorem u2786 : Upper (D 8) (R 8) [66,5,288,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2787 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 7 292 168 208 40 113 177 305), lower := (rows 67 7 292 168 208 40 64 128 256), losses := [] }

theorem u2787 : Upper (D 8) (R 8) [66,5,288,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2787 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2788 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 7 292 168 208 48 105 169 297), lower := (rows 67 7 292 168 208 48 64 128 256), losses := [] }

theorem u2788 : Upper (D 8) (R 8) [66,5,288,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2788 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2789 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 56 208 33 104 168 296), lower := (rows 67 7 388 56 208 33 64 128 256), losses := [] }

theorem u2789 : Upper (D 8) (R 8) [66,5,384,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2790 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 388 56 208 40 97 161 289), lower := (rows 67 7 388 56 208 40 64 128 256), losses := [] }

theorem u2790 : Upper (D 8) (R 8) [66,5,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2790 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2791 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 88 176 33 104 168 296), lower := (rows 67 7 388 88 176 33 64 128 256), losses := [] }

theorem u2791 : Upper (D 8) (R 8) [66,5,384,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2792 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 388 88 176 40 97 161 289), lower := (rows 67 7 388 88 176 40 64 128 256), losses := [] }

theorem u2792 : Upper (D 8) (R 8) [66,5,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2792 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2793 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 104 152 33 112 176 304), lower := (rows 67 7 388 104 152 33 64 128 256), losses := [] }

theorem u2793 : Upper (D 8) (R 8) [66,5,384,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2794 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 388 104 152 48 97 161 289), lower := (rows 67 7 388 104 152 48 64 128 256), losses := [] }

theorem u2794 : Upper (D 8) (R 8) [66,5,384,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2794 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2795 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 388 104 176 33 120 184 312), lower := (rows 67 7 388 104 176 33 64 128 256), losses := [] }

theorem u2795 : Upper (D 8) (R 8) [66,5,384,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2796 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 7 388 104 176 40 113 177 305), lower := (rows 67 7 388 104 176 40 64 128 256), losses := [] }

theorem u2796 : Upper (D 8) (R 8) [66,5,384,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2796 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2797 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 7 388 104 176 48 105 169 297), lower := (rows 67 7 388 104 176 48 64 128 256), losses := [] }

theorem u2797 : Upper (D 8) (R 8) [66,5,384,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2797 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2798 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 21 168 304 33 224 224 480), lower := (rows 67 14 21 168 304 33 64 128 256), losses := [] }

theorem u2798 : Upper (D 8) (R 8) [66,12,17,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2799 : Route 9 := (fun mask => (mask,id))

def c2799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2799 : Upper (D 8) (R 8) [66,12,17,160,288,64] 13 := by
  apply FastRouting.sound _ _ [66,12,17,160,288,64] 13 (by decide) (choices 1) [1,32,128] r2799 c2799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u357
  · exact u358
  · exact u359

def b2800 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 21 168 304 160 97 225 353), lower := (rows 67 14 21 168 304 160 64 128 256), losses := [] }

theorem u2800 : Upper (D 8) (R 8) [66,12,17,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2801 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 21 296 176 33 224 224 480), lower := (rows 67 14 21 296 176 33 64 128 256), losses := [] }

theorem u2801 : Upper (D 8) (R 8) [66,12,17,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2802 : Route 9 := (fun mask => (mask,id))

def c2802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2802 : Upper (D 8) (R 8) [66,12,17,288,160,64] 13 := by
  apply FastRouting.sound _ _ [66,12,17,288,160,64] 13 (by decide) (choices 1) [1,32,128] r2802 c2802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u360
  · exact u361
  · exact u362

def b2803 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 21 296 176 160 97 225 353), lower := (rows 67 14 21 296 176 160 64 128 256), losses := [] }

theorem u2803 : Upper (D 8) (R 8) [66,12,17,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2804 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 56 400 33 224 224 480), lower := (rows 67 14 37 56 400 33 64 128 256), losses := [] }

theorem u2804 : Upper (D 8) (R 8) [66,12,33,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2805 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 56 400 96 225 161 417), lower := (rows 67 14 37 56 400 96 64 128 256), losses := [] }

theorem u2805 : Upper (D 8) (R 8) [66,12,33,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2806 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 56 400 160 97 225 353), lower := (rows 67 14 37 56 400 160 64 128 256), losses := [] }

theorem u2806 : Upper (D 8) (R 8) [66,12,33,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2807 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 152 304 33 224 224 480), lower := (rows 67 14 37 152 304 33 64 128 256), losses := [] }

theorem u2807 : Upper (D 8) (R 8) [66,12,33,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2808 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 152 304 96 225 161 417), lower := (rows 67 14 37 152 304 96 64 128 256), losses := [] }

theorem u2808 : Upper (D 8) (R 8) [66,12,33,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2809 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 67 14 37 152 304 160 97 225 353), lower := (rows 67 14 37 152 304 160 64 128 256), losses := [] }

theorem u2809 : Upper (D 8) (R 8) [66,12,33,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2810 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 168 112 33 464 400 400), lower := (rows 67 14 37 168 112 33 64 128 256), losses := [] }

theorem u2810 : Upper (D 8) (R 8) [66,12,33,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2811 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 67 14 37 168 112 48 449 385 385), lower := (rows 67 14 37 168 112 48 64 128 256), losses := [] }

theorem u2811 : Upper (D 8) (R 8) [66,12,33,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2811 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2812 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 168 112 160 337 401 273), lower := (rows 67 14 37 168 112 160 64 128 256), losses := [] }

theorem u2812 : Upper (D 8) (R 8) [66,12,33,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2813 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 14 37 168 112 288 209 145 401), lower := (rows 67 14 37 168 112 288 64 128 256), losses := [] }

theorem u2813 : Upper (D 8) (R 8) [66,12,33,160,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2813 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2814 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 168 208 33 368 432 304), lower := (rows 67 14 37 168 208 33 64 128 256), losses := [] }

theorem u2814 : Upper (D 8) (R 8) [66,12,33,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2815 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 14 37 168 208 48 353 417 289), lower := (rows 67 14 37 168 208 48 64 128 256), losses := [] }

theorem u2815 : Upper (D 8) (R 8) [66,12,33,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2815 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2816 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 14 37 168 208 288 113 177 305), lower := (rows 67 14 37 168 208 288 64 128 256), losses := [] }

theorem u2816 : Upper (D 8) (R 8) [66,12,33,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2816 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2817 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 168 304 33 208 208 464), lower := (rows 67 14 37 168 304 33 64 128 256), losses := [] }

theorem u2817 : Upper (D 8) (R 8) [66,12,33,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2818 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 14 37 168 304 48 193 193 449), lower := (rows 67 14 37 168 304 48 64 128 256), losses := [] }

theorem u2818 : Upper (D 8) (R 8) [66,12,33,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2818 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2819 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 168 304 96 209 145 401), lower := (rows 67 14 37 168 304 96 64 128 256), losses := [] }

theorem u2819 : Upper (D 8) (R 8) [66,12,33,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2819
end Delivery.IrregularNine14.P08
