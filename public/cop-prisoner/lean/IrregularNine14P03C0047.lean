import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0014
import IrregularNine14P03C0015

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2820 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 56 81 169 201 137 393), lower := (rows 35 7 324 56 81 32 64 128 256), losses := [] }

theorem u2820 : Upper (D 3) (R 3) [34,5,320,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2820
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2821 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 56 88 161 193 129 385), lower := (rows 35 7 324 56 88 32 64 128 256), losses := [] }

theorem u2821 : Upper (D 3) (R 3) [34,5,320,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2821
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2822 : Route 9 := (fun mask => (mask,id))

def c2822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2822 : Upper (D 3) (R 3) [34,5,320,48,129] 13 := by
  apply FastRouting.sound _ _ [34,5,320,48,129] 13 (by decide) (choices 1) [1,8,64,128] r2822 c2822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u865
  · exact u866
  · exact u867
  · exact u868

def b2823 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 56 152 225 193 193 449), lower := (rows 35 7 324 56 152 32 64 128 256), losses := [] }

theorem u2823 : Upper (D 3) (R 3) [34,5,320,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2823
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2824 : Route 9 := (fun mask => (mask,id))

def c2824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2824 : Upper (D 3) (R 3) [34,5,320,48,192] 13 := by
  apply FastRouting.sound _ _ [34,5,320,48,192] 13 (by decide) (choices 1) [1,8,128] r2824 c2824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u869
  · exact u870
  · exact u871

def b2825 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 324 73 145 184 248 184 440), lower := (rows 35 7 324 73 145 32 64 128 256), losses := [] }

theorem u2825 : Upper (D 3) (R 3) [34,5,320,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2825
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2826 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 324 73 152 177 241 177 433), lower := (rows 35 7 324 73 152 32 64 128 256), losses := [] }

theorem u2826 : Upper (D 3) (R 3) [34,5,320,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2826
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2827 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 324 73 176 185 217 153 409), lower := (rows 35 7 324 73 176 32 64 128 256), losses := [] }

theorem u2827 : Upper (D 3) (R 3) [34,5,320,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2827
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2828 : Route 9 := (fun mask => (mask,id))

def c2828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2828 : Upper (D 3) (R 3) [34,5,320,80,129] 13 := by
  apply FastRouting.sound _ _ [34,5,320,80,129] 13 (by decide) (choices 1) [1,8,128] r2828 c2828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u872
  · exact u873
  · exact u874

def b2829 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 88 152 161 225 161 417), lower := (rows 35 7 324 88 152 32 64 128 256), losses := [] }

theorem u2829 : Upper (D 3) (R 3) [34,5,320,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2829
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2830 : Route 9 := (fun mask => (mask,id))

def c2830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2830 : Upper (D 3) (R 3) [34,5,320,80,160] 13 := by
  apply FastRouting.sound _ _ [34,5,320,80,160] 13 (by decide) (choices 1) [1,8,128] r2830 c2830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u875
  · exact u876
  · exact u877

def r2831 : Route 9 := (fun mask => (mask,id))

def c2831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2831 : Upper (D 3) (R 3) [34,5,320,96,129] 13 := by
  apply FastRouting.sound _ _ [34,5,320,96,129] 13 (by decide) (choices 1) [1,8,16,128] r2831 c2831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u878
  · exact u879
  · exact u880
  · exact u881

def r2832 : Route 9 := (fun mask => (mask,id))

def c2832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2832 : Upper (D 3) (R 3) [34,5,320,96,136] 13 := by
  apply FastRouting.sound _ _ [34,5,320,96,136] 13 (by decide) (choices 1) [1,16,128] r2832 c2832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u882
  · exact u883
  · exact u884

def b2833 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 324 137 145 120 120 248 376), lower := (rows 35 7 324 137 145 32 64 128 256), losses := [] }

theorem u2833 : Upper (D 3) (R 3) [34,5,320,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2833
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2834 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 324 137 152 113 113 241 369), lower := (rows 35 7 324 137 152 32 64 128 256), losses := [] }

theorem u2834 : Upper (D 3) (R 3) [34,5,320,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2834
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2835 : Route 9 := (fun mask => (mask,id))

def c2835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2835 : Upper (D 3) (R 3) [34,5,320,129,160] 13 := by
  apply FastRouting.sound _ _ [34,5,320,129,160] 13 (by decide) (choices 1) [1,8,16,64] r2835 c2835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u885
  · exact u886
  · exact u887
  · exact u888

def r2836 : Route 9 := (fun mask => (mask,id))

def c2836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2836 : Upper (D 3) (R 3) [34,5,320,129,192] 13 := by
  apply FastRouting.sound _ _ [34,5,320,129,192] 13 (by decide) (choices 1) [1,8,16] r2836 c2836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u889
  · exact u890
  · exact u891

def b2837 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 324 152 152 97 97 225 353), lower := (rows 35 7 324 152 152 32 64 128 256), losses := [] }

theorem u2837 : Upper (D 3) (R 3) [34,5,320,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2837
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2838 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 152 176 105 73 201 329), lower := (rows 35 7 324 152 176 32 64 128 256), losses := [] }

theorem u2838 : Upper (D 3) (R 3) [34,5,320,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2838
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2839 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 152 208 41 105 169 297), lower := (rows 35 7 324 152 208 32 64 128 256), losses := [] }

theorem u2839 : Upper (D 3) (R 3) [34,5,320,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2839
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2840 : Route 9 := (fun mask => (mask,id))

def c2840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2840 : Upper (D 3) (R 3) [34,5,320,160,192] 13 := by
  apply FastRouting.sound _ _ [34,5,320,160,192] 13 (by decide) (choices 1) [1,8,16] r2840 c2840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u892
  · exact u893
  · exact u894

def b2841 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 21 73 49 480 448 448 448), lower := (rows 35 14 21 73 49 32 64 128 256), losses := [] }

theorem u2841 : Upper (D 3) (R 3) [34,12,17,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2841
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2842 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 21 73 81 416 480 416 416), lower := (rows 35 14 21 73 81 32 64 128 256), losses := [] }

theorem u2842 : Upper (D 3) (R 3) [34,12,17,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2842
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2843 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 21 73 112 417 449 385 385), lower := (rows 35 14 21 73 112 32 64 128 256), losses := [] }

theorem u2843 : Upper (D 3) (R 3) [34,12,17,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2843
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2844 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 73 145 480 480 480 480), lower := (rows 35 14 21 73 145 32 64 128 256), losses := [] }

theorem u2844 : Upper (D 3) (R 3) [34,12,17,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2844
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2845 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 21 73 176 481 449 449 449), lower := (rows 35 14 21 73 176 32 64 128 256), losses := [] }

theorem u2845 : Upper (D 3) (R 3) [34,12,17,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2845
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2846 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 73 208 417 481 417 417), lower := (rows 35 14 21 73 208 32 64 128 256), losses := [] }

theorem u2846 : Upper (D 3) (R 3) [34,12,17,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2846
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2847 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 73 273 224 224 224 480), lower := (rows 35 14 21 73 273 32 64 128 256), losses := [] }

theorem u2847 : Upper (D 3) (R 3) [34,12,17,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2847
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2848 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 21 73 304 225 193 193 449), lower := (rows 35 14 21 73 304 32 64 128 256), losses := [] }

theorem u2848 : Upper (D 3) (R 3) [34,12,17,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2848
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2849 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 73 336 161 225 161 417), lower := (rows 35 14 21 73 336 32 64 128 256), losses := [] }

theorem u2849 : Upper (D 3) (R 3) [34,12,17,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2849
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2850 : Route 9 := (fun mask => (mask,id))

def c2850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2850 : Upper (D 3) (R 3) [34,12,17,65,384] 13 := by
  apply FastRouting.sound _ _ [34,12,17,65,384] 13 (by decide) (choices 1) [1,64,128] r2850 c2850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u895
  · exact u896
  · exact u897

def b2851 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 21 200 49 481 449 449 449), lower := (rows 35 14 21 200 49 32 64 128 256), losses := [] }

theorem u2851 : Upper (D 3) (R 3) [34,12,17,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2851
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2852 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 200 81 417 481 417 417), lower := (rows 35 14 21 200 81 32 64 128 256), losses := [] }

theorem u2852 : Upper (D 3) (R 3) [34,12,17,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2852
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2853 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 21 200 112 417 449 385 385), lower := (rows 35 14 21 200 112 32 64 128 256), losses := [] }

theorem u2853 : Upper (D 3) (R 3) [34,12,17,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2853
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2854 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 21 200 208 289 353 417 289), lower := (rows 35 14 21 200 208 32 64 128 256), losses := [] }

theorem u2854 : Upper (D 3) (R 3) [34,12,17,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2854
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2855 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 200 273 225 225 225 481), lower := (rows 35 14 21 200 273 32 64 128 256), losses := [] }

theorem u2855 : Upper (D 3) (R 3) [34,12,17,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2855
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2856 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 21 200 304 225 193 193 449), lower := (rows 35 14 21 200 304 32 64 128 256), losses := [] }

theorem u2856 : Upper (D 3) (R 3) [34,12,17,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2856
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2857 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 200 336 161 225 161 417), lower := (rows 35 14 21 200 336 32 64 128 256), losses := [] }

theorem u2857 : Upper (D 3) (R 3) [34,12,17,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2857
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2858 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 21 265 49 224 192 192 448), lower := (rows 35 14 21 265 49 32 64 128 256), losses := [] }

theorem u2858 : Upper (D 3) (R 3) [34,12,17,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2858
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2859 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 265 81 224 224 224 480), lower := (rows 35 14 21 265 81 32 64 128 256), losses := [] }

theorem u2859 : Upper (D 3) (R 3) [34,12,17,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2859
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2860 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 21 265 112 225 193 193 449), lower := (rows 35 14 21 265 112 32 64 128 256), losses := [] }

theorem u2860 : Upper (D 3) (R 3) [34,12,17,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2860
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2861 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2861 : Upper (D 3) (R 3) [34,12,17,257,192] 13 := by
  apply FastRouting.sound _ _ [34,12,17,257,192] 13 (by decide) (choices 1) [1,64] r2861 c2861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u898
  · exact u899

def b2862 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 21 328 49 225 193 193 449), lower := (rows 35 14 21 328 49 32 64 128 256), losses := [] }

theorem u2862 : Upper (D 3) (R 3) [34,12,17,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2862
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2863 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 328 81 161 225 161 417), lower := (rows 35 14 21 328 81 32 64 128 256), losses := [] }

theorem u2863 : Upper (D 3) (R 3) [34,12,17,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2863
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2864 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 21 328 112 161 193 129 385), lower := (rows 35 14 21 328 112 32 64 128 256), losses := [] }

theorem u2864 : Upper (D 3) (R 3) [34,12,17,320,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2864
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2865 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 21 328 145 225 225 225 481), lower := (rows 35 14 21 328 145 32 64 128 256), losses := [] }

theorem u2865 : Upper (D 3) (R 3) [34,12,17,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2865
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2866 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 21 328 176 225 193 193 449), lower := (rows 35 14 21 328 176 32 64 128 256), losses := [] }

theorem u2866 : Upper (D 3) (R 3) [34,12,17,320,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2866
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2867 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 328 208 161 225 161 417), lower := (rows 35 14 21 328 208 32 64 128 256), losses := [] }

theorem u2867 : Upper (D 3) (R 3) [34,12,17,320,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2867
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2868 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 137 49 496 464 464 464), lower := (rows 35 14 69 137 49 32 64 128 256), losses := [] }

theorem u2868 : Upper (D 3) (R 3) [34,12,65,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2868
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2869 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 137 81 432 496 432 432), lower := (rows 35 14 69 137 81 32 64 128 256), losses := [] }

theorem u2869 : Upper (D 3) (R 3) [34,12,65,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2869
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2870 : Route 9 := (fun mask => (mask,id))

def c2870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2870 : Upper (D 3) (R 3) [34,12,65,129,96] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,96] 13 (by decide) (choices 1) [1,16,128,256] r2870 c2870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u900
  · exact u901
  · exact u902
  · exact u903

def r2871 : Route 9 := (fun mask => (mask,id))

def c2871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2871 : Upper (D 3) (R 3) [34,12,65,129,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,192] 13 (by decide) (choices 1) [1,16,256] r2871 c2871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u904
  · exact u905
  · exact u906

theorem m2872_128 : Upper (D 3) (R 3) [34,12,65,129,257,128] 13 :=
  permutation_upper _ _ _ [34,12,65,129,257,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u908

def r2872 : Route 9 := (fun mask => (mask,id))

def c2872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2872 : Upper (D 3) (R 3) [34,12,65,129,257] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,257] 13 (by decide) (choices 1) [16,64,128] r2872 c2872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u907
  · exact u908
  · exact m2872_128

theorem m2873_128 : Upper (D 3) (R 3) [34,12,65,129,288,128] 13 :=
  permutation_upper _ _ _ [34,12,65,129,288,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u911

def r2873 : Route 9 := (fun mask => (mask,id))

def c2873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2873 : Upper (D 3) (R 3) [34,12,65,129,288] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,288] 13 (by decide) (choices 1) [1,16,64,128] r2873 c2873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u909
  · exact u910
  · exact u911
  · exact m2873_128

def r2874 : Route 9 := (fun mask => (mask,id))

def c2874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2874 : Upper (D 3) (R 3) [34,12,65,129,320] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,320] 13 (by decide) (choices 1) [1,16,128] r2874 c2874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u912
  · exact u913
  · exact u914

def b2875 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 152 49 481 449 449 449), lower := (rows 35 14 69 152 49 32 64 128 256), losses := [] }

theorem u2875 : Upper (D 3) (R 3) [34,12,65,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2875
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2876 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 152 81 417 481 417 417), lower := (rows 35 14 69 152 81 32 64 128 256), losses := [] }

theorem u2876 : Upper (D 3) (R 3) [34,12,65,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2876
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2877 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 69 152 112 417 449 385 385), lower := (rows 35 14 69 152 112 32 64 128 256), losses := [] }

theorem u2877 : Upper (D 3) (R 3) [34,12,65,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2877
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2878 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 152 145 353 353 481 353), lower := (rows 35 14 69 152 145 32 64 128 256), losses := [] }

theorem u2878 : Upper (D 3) (R 3) [34,12,65,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2878
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2879 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 152 176 353 321 449 321), lower := (rows 35 14 69 152 176 32 64 128 256), losses := [] }

theorem u2879 : Upper (D 3) (R 3) [34,12,65,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2879
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2879
end Delivery.IrregularNine14.P03
