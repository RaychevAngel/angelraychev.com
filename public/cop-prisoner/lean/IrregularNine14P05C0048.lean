import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0011
import IrregularNine14P05C0012

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2880 : Route 9 := (fun mask => (mask,id))

def c2880 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2880 : Upper (D 5) (R 5) [6,65,136,260,40,1] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,40,1] 13 (by decide) (choices 1) [2,16,32] r2880 c2880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u691
  · exact u692
  · exact u693

def r2881 : Route 9 := (fun mask => (mask,id))

def c2881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2881 : Upper (D 5) (R 5) [6,65,136,260,40,2] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,40,2] 13 (by decide) (choices 1) [1,16,32] r2881 c2881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u694
  · exact u695
  · exact u696

def b2882 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 268 56 48 99 163 291), lower := (rows 7 67 140 268 56 48 64 128 256), losses := [] }

theorem u2882 : Upper (D 5) (R 5) [6,65,136,260,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2882
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2883 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 280 49 34 108 172 300), lower := (rows 7 67 140 280 49 34 64 128 256), losses := [] }

theorem u2883 : Upper (D 5) (R 5) [6,65,136,272,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2883
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2884 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 280 49 36 106 170 298), lower := (rows 7 67 140 280 49 36 64 128 256), losses := [] }

theorem u2884 : Upper (D 5) (R 5) [6,65,136,272,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2884
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2885 : PairBound 9 := { available := 38, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 140 280 49 40 102 166 294), lower := (rows 7 67 140 280 49 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 60 65 129 257), good := (rows 486 450 172 316 508 40 64 128 256) }] }

theorem u2885 : Upper (D 5) (R 5) [6,65,136,272,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2885
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2886 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 280 50 33 108 172 300), lower := (rows 7 67 140 280 50 33 64 128 256), losses := [] }

theorem u2886 : Upper (D 5) (R 5) [6,65,136,272,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2886
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2887 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 67 140 280 50 36 105 169 297), lower := (rows 7 67 140 280 50 36 64 128 256), losses := [] }

theorem u2887 : Upper (D 5) (R 5) [6,65,136,272,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2887
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2888 : PairBound 9 := { available := 37, camps := [], pairs := [(4,0),(4,2)], upper := (rows 7 67 140 280 50 40 101 165 293), lower := (rows 7 67 140 280 50 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 44 64 128 256), good := (rows 54 82 172 312 50 40 64 128 256) },{ target := 2, region := (rows 1 2 0 8 17 44 64 128 256), good := (rows 51 83 168 312 50 40 64 128 256) }] }

theorem u2888 : Upper (D 5) (R 5) [6,65,136,272,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2888
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2889 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 280 52 33 106 170 298), lower := (rows 7 67 140 280 52 33 64 128 256), losses := [] }

theorem u2889 : Upper (D 5) (R 5) [6,65,136,272,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2889
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2890 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 67 140 280 52 34 105 169 297), lower := (rows 7 67 140 280 52 34 64 128 256), losses := [] }

theorem u2890 : Upper (D 5) (R 5) [6,65,136,272,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2890
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2891 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 280 52 40 99 163 291), lower := (rows 7 67 140 280 52 40 64 128 256), losses := [] }

theorem u2891 : Upper (D 5) (R 5) [6,65,136,272,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2891
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2892 : PairBound 9 := { available := 52, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 140 296 25 34 116 180 308), lower := (rows 7 67 140 296 25 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 98 140 296 508 34 64 128 256) }] }

theorem u2892 : Upper (D 5) (R 5) [6,65,136,288,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2892
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2893 : Route 9 := (fun mask => (mask,id))

def c2893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2893 : Upper (D 5) (R 5) [6,65,136,288,9,4] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,9,4] 13 (by decide) (choices 1) [2,16,32] r2893 c2893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u697
  · exact u698
  · exact u699

def r2894 : Route 9 := (fun mask => (mask,id))

def c2894 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2894 : Upper (D 5) (R 5) [6,65,136,288,9,16] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,9,16] 13 (by decide) (choices 1) [2,4,32] r2894 c2894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u700
  · exact u701
  · exact u702

def b2895 : PairBound 9 := { available := 52, camps := [], pairs := [(2,1),(3,1)], upper := (rows 7 67 140 296 26 33 116 180 308), lower := (rows 7 67 140 296 26 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 80 144 272), good := (rows 37 97 140 296 508 33 64 128 256) }] }

theorem u2895 : Upper (D 5) (R 5) [6,65,136,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2895
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2896 : Route 9 := (fun mask => (mask,id))

def c2896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2896 : Upper (D 5) (R 5) [6,65,136,288,10,4] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,10,4] 13 (by decide) (choices 1) [1,16,32] r2896 c2896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u703
  · exact u704
  · exact u705

def r2897 : Route 9 := (fun mask => (mask,id))

def c2897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2897 : Upper (D 5) (R 5) [6,65,136,288,10,16] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,10,16] 13 (by decide) (choices 1) [1,4,32] r2897 c2897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u706
  · exact u707
  · exact u708

def b2898 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 296 49 34 92 156 284), lower := (rows 7 67 140 296 49 34 64 128 256), losses := [] }

theorem u2898 : Upper (D 5) (R 5) [6,65,136,288,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2898
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2899 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 296 49 36 90 154 282), lower := (rows 7 67 140 296 49 36 64 128 256), losses := [] }

theorem u2899 : Upper (D 5) (R 5) [6,65,136,288,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2899
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2900 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 140 296 49 40 86 150 278), lower := (rows 7 67 140 296 49 40 64 128 256), losses := [] }

theorem u2900 : Upper (D 5) (R 5) [6,65,136,288,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2900
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2901 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 67 140 296 49 48 78 142 270), lower := (rows 7 67 140 296 49 48 64 128 256), losses := [] }

theorem u2901 : Upper (D 5) (R 5) [6,65,136,288,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2901
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2902 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 296 50 33 92 156 284), lower := (rows 7 67 140 296 50 33 64 128 256), losses := [] }

theorem u2902 : Upper (D 5) (R 5) [6,65,136,288,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2902
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2903 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 67 140 296 50 36 89 153 281), lower := (rows 7 67 140 296 50 36 64 128 256), losses := [] }

theorem u2903 : Upper (D 5) (R 5) [6,65,136,288,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2903
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2904 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 140 296 50 40 85 149 277), lower := (rows 7 67 140 296 50 40 64 128 256), losses := [] }

theorem u2904 : Upper (D 5) (R 5) [6,65,136,288,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2904
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2905 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 296 50 48 77 141 269), lower := (rows 7 67 140 296 50 48 64 128 256), losses := [] }

theorem u2905 : Upper (D 5) (R 5) [6,65,136,288,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2905
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2906 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 296 52 33 90 154 282), lower := (rows 7 67 140 296 52 33 64 128 256), losses := [] }

theorem u2906 : Upper (D 5) (R 5) [6,65,136,288,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2906
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2907 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 67 140 296 52 34 89 153 281), lower := (rows 7 67 140 296 52 34 64 128 256), losses := [] }

theorem u2907 : Upper (D 5) (R 5) [6,65,136,288,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2907
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2908 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 140 296 52 40 83 147 275), lower := (rows 7 67 140 296 52 40 64 128 256), losses := [] }

theorem u2908 : Upper (D 5) (R 5) [6,65,136,288,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2908
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2909 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 296 52 48 75 139 267), lower := (rows 7 67 140 296 52 48 64 128 256), losses := [] }

theorem u2909 : Upper (D 5) (R 5) [6,65,136,288,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2909
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2910 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 41 280 34 108 172 300), lower := (rows 7 67 148 41 280 34 64 128 256), losses := [] }

theorem u2910 : Upper (D 5) (R 5) [6,65,144,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2910
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2911 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 67 148 41 280 36 106 170 298), lower := (rows 7 67 148 41 280 36 64 128 256), losses := [] }

theorem u2911 : Upper (D 5) (R 5) [6,65,144,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2911
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2912 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 148 41 280 40 102 166 294), lower := (rows 7 67 148 41 280 40 64 128 256), losses := [] }

theorem u2912 : Upper (D 5) (R 5) [6,65,144,33,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2912
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2913 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 41 304 34 76 140 268), lower := (rows 7 67 148 41 304 34 64 128 256), losses := [] }

theorem u2913 : Upper (D 5) (R 5) [6,65,144,33,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2913
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2914 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 67 148 41 304 36 74 138 266), lower := (rows 7 67 148 41 304 36 64 128 256), losses := [] }

theorem u2914 : Upper (D 5) (R 5) [6,65,144,33,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2914
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2915 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 148 41 304 40 78 142 270), lower := (rows 7 67 148 41 304 40 64 128 256), losses := [] }

theorem u2915 : Upper (D 5) (R 5) [6,65,144,33,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2915
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2916 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 42 280 33 108 172 300), lower := (rows 7 67 148 42 280 33 64 128 256), losses := [] }

theorem u2916 : Upper (D 5) (R 5) [6,65,144,34,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2916
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2917 : Route 9 := (fun mask => (mask,id))

def c2917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2917 : Upper (D 5) (R 5) [6,65,144,34,264,4] 13 := by
  apply FastRouting.sound _ _ [6,65,144,34,264,4] 13 (by decide) (choices 1) [1,8,32] r2917 c2917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u709
  · exact u710
  · exact u711

def b2918 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 148 42 280 40 101 165 293), lower := (rows 7 67 148 42 280 40 64 128 256), losses := [] }

theorem u2918 : Upper (D 5) (R 5) [6,65,144,34,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2918
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2919 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 42 304 33 76 140 268), lower := (rows 7 67 148 42 304 33 64 128 256), losses := [] }

theorem u2919 : Upper (D 5) (R 5) [6,65,144,34,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2919
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2920 : Route 9 := (fun mask => (mask,id))

def c2920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2920 : Upper (D 5) (R 5) [6,65,144,34,288,4] 13 := by
  apply FastRouting.sound _ _ [6,65,144,34,288,4] 13 (by decide) (choices 1) [1,8] r2920 c2920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u712
  · exact u713

def b2921 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 148 42 304 40 77 141 269), lower := (rows 7 67 148 42 304 40 64 128 256), losses := [] }

theorem u2921 : Upper (D 5) (R 5) [6,65,144,34,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2921
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2922 : Route 9 := (fun mask => (mask,id))

def c2922 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2922 : Upper (D 5) (R 5) [6,65,144,36,264,1] 13 := by
  apply FastRouting.sound _ _ [6,65,144,36,264,1] 13 (by decide) (choices 1) [2,8,32] r2922 c2922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u714
  · exact u715
  · exact u716

def r2923 : Route 9 := (fun mask => (mask,id))

def c2923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2923 : Upper (D 5) (R 5) [6,65,144,36,264,2] 13 := by
  apply FastRouting.sound _ _ [6,65,144,36,264,2] 13 (by decide) (choices 1) [1,8,32] r2923 c2923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u717
  · exact u718
  · exact u719

def b2924 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 148 44 280 40 99 163 291), lower := (rows 7 67 148 44 280 40 64 128 256), losses := [] }

theorem u2924 : Upper (D 5) (R 5) [6,65,144,36,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2924
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2925 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 265 56 34 108 172 300), lower := (rows 7 67 148 265 56 34 64 128 256), losses := [] }

theorem u2925 : Upper (D 5) (R 5) [6,65,144,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2925
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2926 : PairBound 9 := { available := 42, camps := [], pairs := [(4,0),(4,1)], upper := (rows 7 67 148 265 56 36 106 170 298), lower := (rows 7 67 148 265 56 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 37 64 128 256), good := (rows 38 98 180 312 56 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 24 37 64 128 256), good := (rows 37 97 180 313 56 36 64 128 256) }] }

theorem u2926 : Upper (D 5) (R 5) [6,65,144,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2926
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2927 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 148 265 56 40 102 166 294), lower := (rows 7 67 148 265 56 40 64 128 256), losses := [] }

theorem u2927 : Upper (D 5) (R 5) [6,65,144,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2927
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2928 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 266 56 33 108 172 300), lower := (rows 7 67 148 266 56 33 64 128 256), losses := [] }

theorem u2928 : Upper (D 5) (R 5) [6,65,144,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2928
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2929 : Route 9 := (fun mask => (mask,id))

def c2929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2929 : Upper (D 5) (R 5) [6,65,144,258,40,4] 13 := by
  apply FastRouting.sound _ _ [6,65,144,258,40,4] 13 (by decide) (choices 1) [1,8,32] r2929 c2929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u720
  · exact u721
  · exact u722

def b2930 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 148 266 56 40 101 165 293), lower := (rows 7 67 148 266 56 40 64 128 256), losses := [] }

theorem u2930 : Upper (D 5) (R 5) [6,65,144,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2930
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2931 : Route 9 := (fun mask => (mask,id))

def c2931 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2931 : Upper (D 5) (R 5) [6,65,144,260,40,1] 13 := by
  apply FastRouting.sound _ _ [6,65,144,260,40,1] 13 (by decide) (choices 1) [2,8,32] r2931 c2931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u723
  · exact u724
  · exact u725

def r2932 : Route 9 := (fun mask => (mask,id))

def c2932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2932 : Upper (D 5) (R 5) [6,65,144,260,40,2] 13 := by
  apply FastRouting.sound _ _ [6,65,144,260,40,2] 13 (by decide) (choices 1) [1,8,32] r2932 c2932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u726
  · exact u727
  · exact u728

def b2933 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 148 268 56 40 99 163 291), lower := (rows 7 67 148 268 56 40 64 128 256), losses := [] }

theorem u2933 : Upper (D 5) (R 5) [6,65,144,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2933
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2934 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 148 296 26 33 108 172 300), lower := (rows 7 67 148 296 26 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 59 16 35 81 145 273), good := (rows 493 489 476 296 508 489 64 128 256) }] }

theorem u2934 : Upper (D 5) (R 5) [6,65,144,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2934
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2935 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 148 296 26 36 105 169 297), lower := (rows 7 67 148 296 26 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 27 16 53 67 131 259), good := (rows 493 489 188 296 508 36 64 128 256) }] }

theorem u2935 : Upper (D 5) (R 5) [6,65,144,288,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2935
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2936 : PairBound 9 := { available := 37, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 148 296 26 40 101 165 293), lower := (rows 7 67 148 296 26 40 64 128 256), losses := [] }

theorem u2936 : Upper (D 5) (R 5) [6,65,144,288,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2936
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2937 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 296 50 33 76 140 268), lower := (rows 7 67 148 296 50 33 64 128 256), losses := [] }

theorem u2937 : Upper (D 5) (R 5) [6,65,144,288,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2937
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2938 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1),(4,0)], upper := (rows 7 67 148 296 50 36 73 137 265), lower := (rows 7 67 148 296 50 36 64 128 256), losses := [] }

theorem u2938 : Upper (D 5) (R 5) [6,65,144,288,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2938
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2939 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 148 296 50 40 77 141 269), lower := (rows 7 67 148 296 50 40 64 128 256), losses := [] }

theorem u2939 : Upper (D 5) (R 5) [6,65,144,288,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2939
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2939
end Delivery.IrregularNine14.P05
