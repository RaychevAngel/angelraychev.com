import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0010
import IrregularNine14P05C0011

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2820 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 42 304 48 77 141 269), lower := (rows 7 67 140 42 304 48 64 128 256), losses := [] }

theorem u2820 : Upper (D 5) (R 5) [6,65,136,34,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2820
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2821 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 140 44 26 33 368 432 304), lower := (rows 7 67 140 44 26 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 35 80 144 272), good := (rows 45 105 140 44 508 41 64 128 256) }] }

theorem u2821 : Upper (D 5) (R 5) [6,65,136,36,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2821
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2822 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 140 44 26 48 353 417 289), lower := (rows 7 67 140 44 26 48 64 128 256), losses := [] }

theorem u2822 : Upper (D 5) (R 5) [6,65,136,36,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2822
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2823 : Route 9 := (fun mask => (mask,id))

def c2823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2823 : Upper (D 5) (R 5) [6,65,136,36,10,256] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,10,256] 13 (by decide) (choices 1) [1,16,32] r2823 c2823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u656
  · exact u657
  · exact u658

def b2824 : PairBound 9 := { available := 280, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 49 34 344 408 280), lower := (rows 7 67 140 44 49 34 64 128 256), losses := [] }

theorem u2824 : Upper (D 5) (R 5) [6,65,136,36,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2824
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2825 : PairBound 9 := { available := 274, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 49 40 338 402 274), lower := (rows 7 67 140 44 49 40 64 128 256), losses := [] }

theorem u2825 : Upper (D 5) (R 5) [6,65,136,36,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2825
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2826 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 323, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 44 49 48 330 394 266), lower := (rows 7 67 140 44 49 48 64 128 256), losses := [] }

theorem u2826 : Upper (D 5) (R 5) [6,65,136,36,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2826
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2827 : Route 9 := (fun mask => (mask,id))

def c2827 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2827 : Upper (D 5) (R 5) [6,65,136,36,33,256] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,33,256] 13 (by decide) (choices 1) [2,8,16] r2827 c2827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u659
  · exact u660
  · exact u661

def b2828 : PairBound 9 := { available := 280, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 50 33 344 408 280), lower := (rows 7 67 140 44 50 33 64 128 256), losses := [] }

theorem u2828 : Upper (D 5) (R 5) [6,65,136,36,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2828
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2829 : PairBound 9 := { available := 273, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 50 40 337 401 273), lower := (rows 7 67 140 44 50 40 64 128 256), losses := [] }

theorem u2829 : Upper (D 5) (R 5) [6,65,136,36,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2829
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2830 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 44 50 48 329 393 265), lower := (rows 7 67 140 44 50 48 64 128 256), losses := [] }

theorem u2830 : Upper (D 5) (R 5) [6,65,136,36,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2830
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2831 : Route 9 := (fun mask => (mask,id))

def c2831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2831 : Upper (D 5) (R 5) [6,65,136,36,34,256] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,34,256] 13 (by decide) (choices 1) [1,8,16] r2831 c2831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u662
  · exact u663
  · exact u664

def b2832 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 67 140 44 273 34 120 184 312), lower := (rows 7 67 140 44 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 25 16 35 80 144 272), good := (rows 46 106 140 44 508 34 64 128 256) }] }

theorem u2832 : Upper (D 5) (R 5) [6,65,136,36,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2832
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2833 : PairBound 9 := { available := 50, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 273 40 114 178 306), lower := (rows 7 67 140 44 273 40 64 128 256), losses := [] }

theorem u2833 : Upper (D 5) (R 5) [6,65,136,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2833
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2834 : Route 9 := (fun mask => (mask,id))

def c2834 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2834 : Upper (D 5) (R 5) [6,65,136,36,257,16] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,257,16] 13 (by decide) (choices 1) [2,8,32] r2834 c2834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u665
  · exact u666
  · exact u667

def b2835 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 67 140 44 274 33 120 184 312), lower := (rows 7 67 140 44 274 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 35 80 144 272), good := (rows 45 105 140 44 508 41 64 128 256) }] }

theorem u2835 : Upper (D 5) (R 5) [6,65,136,36,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2835
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2836 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 274 40 113 177 305), lower := (rows 7 67 140 44 274 40 64 128 256), losses := [] }

theorem u2836 : Upper (D 5) (R 5) [6,65,136,36,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2836
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2837 : Route 9 := (fun mask => (mask,id))

def c2837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2837 : Upper (D 5) (R 5) [6,65,136,36,258,16] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,258,16] 13 (by decide) (choices 1) [1,8,32] r2837 c2837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u668
  · exact u669
  · exact u670

def b2838 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(1,2),(3,1)], upper := (rows 7 67 140 44 280 33 114 178 306), lower := (rows 7 67 140 44 280 33 64 128 256), losses := [{ target := 2, region := (rows 1 35 0 8 28 35 73 137 265), good := (rows 499 483 472 506 472 483 64 128 256) }] }

theorem u2838 : Upper (D 5) (R 5) [6,65,136,36,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2838
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2839 : Route 9 := (fun mask => (mask,id))

def c2839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2839 : Upper (D 5) (R 5) [6,65,136,36,264,2] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,264,2] 13 (by decide) (choices 1) [1,16,32] r2839 c2839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u671
  · exact u672
  · exact u673

def b2840 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 44 280 48 99 163 291), lower := (rows 7 67 140 44 280 48 64 128 256), losses := [] }

theorem u2840 : Upper (D 5) (R 5) [6,65,136,36,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2840
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2841 : Route 9 := (fun mask => (mask,id))

def c2841 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2841 : Upper (D 5) (R 5) [6,65,136,36,288,1] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,288,1] 13 (by decide) (choices 1) [2,8,16] r2841 c2841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u674
  · exact u675
  · exact u676

def r2842 : Route 9 := (fun mask => (mask,id))

def c2842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2842 : Upper (D 5) (R 5) [6,65,136,36,288,2] 13 := by
  apply FastRouting.sound _ _ [6,65,136,36,288,2] 13 (by decide) (choices 1) [1,8,16] r2842 c2842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u677
  · exact u678
  · exact u679

def b2843 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 304 40 83 147 275), lower := (rows 7 67 140 44 304 40 64 128 256), losses := [] }

theorem u2843 : Upper (D 5) (R 5) [6,65,136,36,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2843
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2844 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 44 304 48 75 139 267), lower := (rows 7 67 140 44 304 48 64 128 256), losses := [] }

theorem u2844 : Upper (D 5) (R 5) [6,65,136,36,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2844
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2845 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 56 273 34 108 172 300), lower := (rows 7 67 140 56 273 34 64 128 256), losses := [] }

theorem u2845 : Upper (D 5) (R 5) [6,65,136,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2845
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2846 : PairBound 9 := { available := 42, camps := [], pairs := [(3,0),(3,1)], upper := (rows 7 67 140 56 273 36 106 170 298), lower := (rows 7 67 140 56 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 37 64 128 256), good := (rows 38 98 172 56 312 36 64 128 256) },{ target := 1, region := (rows 1 0 4 24 16 37 64 128 256), good := (rows 37 97 172 56 313 36 64 128 256) }] }

theorem u2846 : Upper (D 5) (R 5) [6,65,136,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2846
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2847 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 140 56 273 40 102 166 294), lower := (rows 7 67 140 56 273 40 64 128 256), losses := [] }

theorem u2847 : Upper (D 5) (R 5) [6,65,136,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2847
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2848 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 56 274 33 108 172 300), lower := (rows 7 67 140 56 274 33 64 128 256), losses := [] }

theorem u2848 : Upper (D 5) (R 5) [6,65,136,48,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2848
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2849 : Route 9 := (fun mask => (mask,id))

def c2849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2849 : Upper (D 5) (R 5) [6,65,136,48,258,4] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48,258,4] 13 (by decide) (choices 1) [1,8,32] r2849 c2849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u680
  · exact u681
  · exact u682

def b2850 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 140 56 274 40 101 165 293), lower := (rows 7 67 140 56 274 40 64 128 256), losses := [] }

theorem u2850 : Upper (D 5) (R 5) [6,65,136,48,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2850
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2851 : Route 9 := (fun mask => (mask,id))

def c2851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2851 : Upper (D 5) (R 5) [6,65,136,48,260,1] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48,260,1] 13 (by decide) (choices 1) [2,8,32] r2851 c2851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u683
  · exact u684
  · exact u685

def r2852 : Route 9 := (fun mask => (mask,id))

def c2852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2852 : Upper (D 5) (R 5) [6,65,136,48,260,2] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48,260,2] 13 (by decide) (choices 1) [1,8,32] r2852 c2852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u686
  · exact u687
  · exact u688

def b2853 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 140 56 276 40 99 163 291), lower := (rows 7 67 140 56 276 40 64 128 256), losses := [] }

theorem u2853 : Upper (D 5) (R 5) [6,65,136,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2853
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2854 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 67 140 265 50 36 120 184 312), lower := (rows 7 67 140 265 50 36 64 128 256), losses := [] }

theorem u2854 : Upper (D 5) (R 5) [6,65,136,257,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2854
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2855 : PairBound 9 := { available := 52, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 67 140 265 50 40 116 180 308), lower := (rows 7 67 140 265 50 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 8 17 44 89 153 281), good := (rows 502 466 492 508 502 492 64 128 256) }] }

theorem u2855 : Upper (D 5) (R 5) [6,65,136,257,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2855
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2856 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 265 50 48 108 172 300), lower := (rows 7 67 140 265 50 48 64 128 256), losses := [] }

theorem u2856 : Upper (D 5) (R 5) [6,65,136,257,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2856
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2857 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 67 140 265 52 34 120 184 312), lower := (rows 7 67 140 265 52 34 64 128 256), losses := [] }

theorem u2857 : Upper (D 5) (R 5) [6,65,136,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2857
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2858 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 265 52 40 114 178 306), lower := (rows 7 67 140 265 52 40 64 128 256), losses := [] }

theorem u2858 : Upper (D 5) (R 5) [6,65,136,257,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2858
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2859 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 265 52 48 106 170 298), lower := (rows 7 67 140 265 52 48 64 128 256), losses := [] }

theorem u2859 : Upper (D 5) (R 5) [6,65,136,257,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2859
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2860 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 265 56 34 116 180 308), lower := (rows 7 67 140 265 56 34 64 128 256), losses := [] }

theorem u2860 : Upper (D 5) (R 5) [6,65,136,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2860
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2861 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 265 56 36 114 178 306), lower := (rows 7 67 140 265 56 36 64 128 256), losses := [] }

theorem u2861 : Upper (D 5) (R 5) [6,65,136,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2861
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2862 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 265 56 48 102 166 294), lower := (rows 7 67 140 265 56 48 64 128 256), losses := [] }

theorem u2862 : Upper (D 5) (R 5) [6,65,136,257,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2862
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2863 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 266 49 36 120 184 312), lower := (rows 7 67 140 266 49 36 64 128 256), losses := [] }

theorem u2863 : Upper (D 5) (R 5) [6,65,136,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2863
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2864 : PairBound 9 := { available := 52, camps := [], pairs := [(4,1),(4,2)], upper := (rows 7 67 140 266 49 40 116 180 308), lower := (rows 7 67 140 266 49 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 501 465 172 296 497 40 64 128 256) },{ target := 2, region := (rows 1 2 0 8 17 44 64 128 256), good := (rows 51 83 168 298 49 40 64 128 256) }] }

theorem u2864 : Upper (D 5) (R 5) [6,65,136,258,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2864
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2865 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 67 140 266 49 48 108 172 300), lower := (rows 7 67 140 266 49 48 64 128 256), losses := [] }

theorem u2865 : Upper (D 5) (R 5) [6,65,136,258,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2865
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2866 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 266 52 33 120 184 312), lower := (rows 7 67 140 266 52 33 64 128 256), losses := [] }

theorem u2866 : Upper (D 5) (R 5) [6,65,136,258,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2866
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2867 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 266 52 40 113 177 305), lower := (rows 7 67 140 266 52 40 64 128 256), losses := [] }

theorem u2867 : Upper (D 5) (R 5) [6,65,136,258,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2867
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2868 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 266 52 48 105 169 297), lower := (rows 7 67 140 266 52 48 64 128 256), losses := [] }

theorem u2868 : Upper (D 5) (R 5) [6,65,136,258,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2868
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2869 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 266 56 33 116 180 308), lower := (rows 7 67 140 266 56 33 64 128 256), losses := [] }

theorem u2869 : Upper (D 5) (R 5) [6,65,136,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2869
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2870 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 140 266 56 36 113 177 305), lower := (rows 7 67 140 266 56 36 64 128 256), losses := [] }

theorem u2870 : Upper (D 5) (R 5) [6,65,136,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2870
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2871 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 266 56 48 101 165 293), lower := (rows 7 67 140 266 56 48 64 128 256), losses := [] }

theorem u2871 : Upper (D 5) (R 5) [6,65,136,258,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2871
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2872 : PairBound 9 := { available := 48, camps := [], pairs := [(2,1),(3,1)], upper := (rows 7 67 140 268 26 33 112 176 304), lower := (rows 7 67 140 268 26 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 80 144 272), good := (rows 37 97 140 268 508 33 64 128 256) }] }

theorem u2872 : Upper (D 5) (R 5) [6,65,136,260,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2872
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2873 : Route 9 := (fun mask => (mask,id))

def c2873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2873 : Upper (D 5) (R 5) [6,65,136,260,10,16] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,10,16] 13 (by decide) (choices 1) [1,32] r2873 c2873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u689
  · exact u690

def b2874 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 268 49 34 120 184 312), lower := (rows 7 67 140 268 49 34 64 128 256), losses := [] }

theorem u2874 : Upper (D 5) (R 5) [6,65,136,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2874
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2875 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 66, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 268 49 40 114 178 306), lower := (rows 7 67 140 268 49 40 64 128 256), losses := [] }

theorem u2875 : Upper (D 5) (R 5) [6,65,136,260,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2875
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2876 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 67 140 268 49 48 106 170 298), lower := (rows 7 67 140 268 49 48 64 128 256), losses := [] }

theorem u2876 : Upper (D 5) (R 5) [6,65,136,260,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2876
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2877 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 268 50 33 120 184 312), lower := (rows 7 67 140 268 50 33 64 128 256), losses := [] }

theorem u2877 : Upper (D 5) (R 5) [6,65,136,260,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2877
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2878 : PairBound 9 := { available := 49, camps := [], pairs := [(1,2),(4,0)], upper := (rows 7 67 140 268 50 40 113 177 305), lower := (rows 7 67 140 268 50 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 44 64 128 256), good := (rows 54 82 172 300 50 40 64 128 256) },{ target := 2, region := (rows 1 3 0 8 17 44 65 129 257), good := (rows 499 467 168 296 50 40 64 128 256) }] }

theorem u2878 : Upper (D 5) (R 5) [6,65,136,260,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2878
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2879 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 268 50 48 105 169 297), lower := (rows 7 67 140 268 50 48 64 128 256), losses := [] }

theorem u2879 : Upper (D 5) (R 5) [6,65,136,260,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2879
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2879
end Delivery.IrregularNine14.P05
