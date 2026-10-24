import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0015

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2880 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 152 208 289 353 417 289), lower := (rows 35 14 69 152 208 32 64 128 256), losses := [] }

theorem u2880 : Upper (D 3) (R 3) [34,12,65,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2880
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2881 : Route 9 := (fun mask => (mask,id))

def c2881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2881 : Upper (D 3) (R 3) [34,12,65,144,257] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,257] 13 (by decide) (choices 1) [1,64,128] r2881 c2881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u915
  · exact u916
  · exact u917

def b2882 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 69 152 304 225 193 193 449), lower := (rows 35 14 69 152 304 32 64 128 256), losses := [] }

theorem u2882 : Upper (D 3) (R 3) [34,12,65,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2882
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2883 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 152 336 161 225 161 417), lower := (rows 35 14 69 152 336 32 64 128 256), losses := [] }

theorem u2883 : Upper (D 3) (R 3) [34,12,65,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2883
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2884 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 152 400 97 97 225 353), lower := (rows 35 14 69 152 400 32 64 128 256), losses := [] }

theorem u2884 : Upper (D 3) (R 3) [34,12,65,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2884
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2885 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 265 49 240 208 208 464), lower := (rows 35 14 69 265 49 32 64 128 256), losses := [] }

theorem u2885 : Upper (D 3) (R 3) [34,12,65,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2885
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2886 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 265 81 176 240 176 432), lower := (rows 35 14 69 265 81 32 64 128 256), losses := [] }

theorem u2886 : Upper (D 3) (R 3) [34,12,65,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2886
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2887 : Route 9 := (fun mask => (mask,id))

def c2887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2887 : Upper (D 3) (R 3) [34,12,65,257,96] 13 := by
  apply FastRouting.sound _ _ [34,12,65,257,96] 13 (by decide) (choices 1) [1,16,128] r2887 c2887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u918
  · exact u919
  · exact u920

def r2888 : Route 9 := (fun mask => (mask,id))

def c2888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2888 : Upper (D 3) (R 3) [34,12,65,257,129] 13 := by
  apply FastRouting.sound _ _ [34,12,65,257,129] 13 (by decide) (choices 1) [16,64,128] r2888 c2888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u921
  · exact u922
  · exact u923

def r2889 : Route 9 := (fun mask => (mask,id))

def c2889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2889 : Upper (D 3) (R 3) [34,12,65,257,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,257,160] 13 (by decide) (choices 1) [1,16,64,128] r2889 c2889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u924
  · exact u925
  · exact u926
  · exact u927

def r2890 : Route 9 := (fun mask => (mask,id))

def c2890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2890 : Upper (D 3) (R 3) [34,12,65,257,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,257,192] 13 (by decide) (choices 1) [1,16,128] r2890 c2890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u928
  · exact u929
  · exact u930

def b2891 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 280 49 225 193 193 449), lower := (rows 35 14 69 280 49 32 64 128 256), losses := [] }

theorem u2891 : Upper (D 3) (R 3) [34,12,65,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2891
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2892 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 280 81 161 225 161 417), lower := (rows 35 14 69 280 81 32 64 128 256), losses := [] }

theorem u2892 : Upper (D 3) (R 3) [34,12,65,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2892
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2893 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 69 280 112 161 193 129 385), lower := (rows 35 14 69 280 112 32 64 128 256), losses := [] }

theorem u2893 : Upper (D 3) (R 3) [34,12,65,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2893
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2894 : Route 9 := (fun mask => (mask,id))

def c2894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2894 : Upper (D 3) (R 3) [34,12,65,272,129] 13 := by
  apply FastRouting.sound _ _ [34,12,65,272,129] 13 (by decide) (choices 1) [1,64,128] r2894 c2894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u931
  · exact u932
  · exact u933

def b2895 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 69 280 176 225 193 193 449), lower := (rows 35 14 69 280 176 32 64 128 256), losses := [] }

theorem u2895 : Upper (D 3) (R 3) [34,12,65,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2895
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2896 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 69 280 208 161 225 161 417), lower := (rows 35 14 69 280 208 32 64 128 256), losses := [] }

theorem u2896 : Upper (D 3) (R 3) [34,12,65,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2896
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2897 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 392 49 241 209 209 465), lower := (rows 35 14 69 392 49 32 64 128 256), losses := [] }

theorem u2897 : Upper (D 3) (R 3) [34,12,65,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2897
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2898 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 69 392 81 177 241 177 433), lower := (rows 35 14 69 392 81 32 64 128 256), losses := [] }

theorem u2898 : Upper (D 3) (R 3) [34,12,65,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2898
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2899 : Route 9 := (fun mask => (mask,id))

def c2899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2899 : Upper (D 3) (R 3) [34,12,65,384,96] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,96] 13 (by decide) (choices 1) [1,16,128] r2899 c2899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u934
  · exact u935
  · exact u936

def b2900 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 69 392 145 113 113 241 369), lower := (rows 35 14 69 392 145 32 64 128 256), losses := [] }

theorem u2900 : Upper (D 3) (R 3) [34,12,65,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2900
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2901 : Route 9 := (fun mask => (mask,id))

def c2901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2901 : Upper (D 3) (R 3) [34,12,65,384,160] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,160] 13 (by decide) (choices 1) [1,16,64] r2901 c2901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u937
  · exact u938
  · exact u939

def r2902 : Route 9 := (fun mask => (mask,id))

def c2902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2902 : Upper (D 3) (R 3) [34,12,65,384,192] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,192] 13 (by decide) (choices 1) [1,16] r2902 c2902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u940
  · exact u941

def b2903 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 84 265 49 225 193 193 449), lower := (rows 35 14 84 265 49 32 64 128 256), losses := [] }

theorem u2903 : Upper (D 3) (R 3) [34,12,80,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2903
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2904 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 265 81 161 225 161 417), lower := (rows 35 14 84 265 81 32 64 128 256), losses := [] }

theorem u2904 : Upper (D 3) (R 3) [34,12,80,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2904
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2905 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 265 112 161 193 129 385), lower := (rows 35 14 84 265 112 32 64 128 256), losses := [] }

theorem u2905 : Upper (D 3) (R 3) [34,12,80,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2905
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2906 : Route 9 := (fun mask => (mask,id))

def c2906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2906 : Upper (D 3) (R 3) [34,12,80,257,129] 13 := by
  apply FastRouting.sound _ _ [34,12,80,257,129] 13 (by decide) (choices 1) [1,64,128] r2906 c2906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u942
  · exact u943
  · exact u944

def b2907 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 84 265 176 225 193 193 449), lower := (rows 35 14 84 265 176 32 64 128 256), losses := [] }

theorem u2907 : Upper (D 3) (R 3) [34,12,80,257,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2907
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2908 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 265 208 161 225 161 417), lower := (rows 35 14 84 265 208 32 64 128 256), losses := [] }

theorem u2908 : Upper (D 3) (R 3) [34,12,80,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2908
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2909 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 84 392 49 225 193 193 449), lower := (rows 35 14 84 392 49 32 64 128 256), losses := [] }

theorem u2909 : Upper (D 3) (R 3) [34,12,80,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2909
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2910 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 392 81 161 225 161 417), lower := (rows 35 14 84 392 81 32 64 128 256), losses := [] }

theorem u2910 : Upper (D 3) (R 3) [34,12,80,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2910
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2911 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 392 112 161 193 129 385), lower := (rows 35 14 84 392 112 32 64 128 256), losses := [] }

theorem u2911 : Upper (D 3) (R 3) [34,12,80,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2911
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2912 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 84 392 145 97 97 225 353), lower := (rows 35 14 84 392 145 32 64 128 256), losses := [] }

theorem u2912 : Upper (D 3) (R 3) [34,12,80,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2912
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2913 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 35 14 84 392 176 97 65 193 321), lower := (rows 35 14 84 392 176 32 64 128 256), losses := [] }

theorem u2913 : Upper (D 3) (R 3) [34,12,80,384,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2913
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2914 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 392 208 33 97 161 289), lower := (rows 35 14 84 392 208 32 64 128 256), losses := [] }

theorem u2914 : Upper (D 3) (R 3) [34,12,80,384,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2914
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2915 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 196 265 49 241 209 209 465), lower := (rows 35 14 196 265 49 32 64 128 256), losses := [] }

theorem u2915 : Upper (D 3) (R 3) [34,12,192,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2915
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2916 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 196 265 81 177 241 177 433), lower := (rows 35 14 196 265 81 32 64 128 256), losses := [] }

theorem u2916 : Upper (D 3) (R 3) [34,12,192,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2916
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2917 : Route 9 := (fun mask => (mask,id))

def c2917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2917 : Upper (D 3) (R 3) [34,12,192,257,96] 13 := by
  apply FastRouting.sound _ _ [34,12,192,257,96] 13 (by decide) (choices 1) [1,16,128] r2917 c2917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u945
  · exact u946
  · exact u947

def b2918 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 196 265 208 49 113 177 305), lower := (rows 35 14 196 265 208 32 64 128 256), losses := [] }

theorem u2918 : Upper (D 3) (R 3) [34,12,192,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2918
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2919 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 196 280 49 225 193 193 449), lower := (rows 35 14 196 280 49 32 64 128 256), losses := [] }

theorem u2919 : Upper (D 3) (R 3) [34,12,192,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2919
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2920 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 196 280 81 161 225 161 417), lower := (rows 35 14 196 280 81 32 64 128 256), losses := [] }

theorem u2920 : Upper (D 3) (R 3) [34,12,192,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2920
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2921 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 35 14 196 280 112 161 193 129 385), lower := (rows 35 14 196 280 112 32 64 128 256), losses := [] }

theorem u2921 : Upper (D 3) (R 3) [34,12,192,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2921
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2922 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 196 280 208 33 97 161 289), lower := (rows 35 14 196 280 208 32 64 128 256), losses := [] }

theorem u2922 : Upper (D 3) (R 3) [34,12,192,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2922
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2923 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 13 176 496 464 464 464), lower := (rows 35 67 13 13 176 32 64 128 256), losses := [] }

theorem u2923 : Upper (D 3) (R 3) [34,65,9,5,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2923
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2924 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 13 208 432 496 432 432), lower := (rows 35 67 13 13 208 32 64 128 256), losses := [] }

theorem u2924 : Upper (D 3) (R 3) [34,65,9,5,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2924
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2925 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 13 304 240 208 208 464), lower := (rows 35 67 13 13 304 32 64 128 256), losses := [] }

theorem u2925 : Upper (D 3) (R 3) [34,65,9,5,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2925
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2926 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 13 336 176 240 176 432), lower := (rows 35 67 13 13 336 32 64 128 256), losses := [] }

theorem u2926 : Upper (D 3) (R 3) [34,65,9,5,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2926
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2927 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 13 400 240 240 240 496), lower := (rows 35 67 13 13 400 32 64 128 256), losses := [] }

theorem u2927 : Upper (D 3) (R 3) [34,65,9,5,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2927
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2928 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 25 52 480 448 448 448), lower := (rows 35 67 13 25 52 32 64 128 256), losses := [] }

theorem u2928 : Upper (D 3) (R 3) [34,65,9,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2928
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2929 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 25 84 416 480 416 416), lower := (rows 35 67 13 25 84 32 64 128 256), losses := [] }

theorem u2929 : Upper (D 3) (R 3) [34,65,9,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2929
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2930 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 25 148 480 480 480 480), lower := (rows 35 67 13 25 148 32 64 128 256), losses := [] }

theorem u2930 : Upper (D 3) (R 3) [34,65,9,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2930
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2931 : PairBound 9 := { available := 452, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 25 176 484 452 452 452), lower := (rows 35 67 13 25 176 32 64 128 256), losses := [] }

theorem u2931 : Upper (D 3) (R 3) [34,65,9,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2931
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2932 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 25 208 420 484 420 420), lower := (rows 35 67 13 25 208 32 64 128 256), losses := [] }

theorem u2932 : Upper (D 3) (R 3) [34,65,9,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2932
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2933 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 25 276 224 224 224 480), lower := (rows 35 67 13 25 276 32 64 128 256), losses := [] }

theorem u2933 : Upper (D 3) (R 3) [34,65,9,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2933
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2934 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 25 304 228 196 196 452), lower := (rows 35 67 13 25 304 32 64 128 256), losses := [] }

theorem u2934 : Upper (D 3) (R 3) [34,65,9,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2934
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2935 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 25 336 164 228 164 420), lower := (rows 35 67 13 25 336 32 64 128 256), losses := [] }

theorem u2935 : Upper (D 3) (R 3) [34,65,9,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2935
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2936 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 25 400 228 228 228 484), lower := (rows 35 67 13 25 400 32 64 128 256), losses := [] }

theorem u2936 : Upper (D 3) (R 3) [34,65,9,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2936
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2937 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 28 49 480 448 448 448), lower := (rows 35 67 13 28 49 32 64 128 256), losses := [] }

theorem u2937 : Upper (D 3) (R 3) [34,65,9,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2937
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2938 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 28 81 416 480 416 416), lower := (rows 35 67 13 28 81 32 64 128 256), losses := [] }

theorem u2938 : Upper (D 3) (R 3) [34,65,9,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2938
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2939 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 28 112 417 449 385 385), lower := (rows 35 67 13 28 112 32 64 128 256), losses := [] }

theorem u2939 : Upper (D 3) (R 3) [34,65,9,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2939
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2939
end Delivery.IrregularNine14.P03
