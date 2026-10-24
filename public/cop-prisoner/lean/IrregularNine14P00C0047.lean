import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0026
import IrregularNine14P00C0027

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2820 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2820 : Upper (D 0) (R 0) [112,5,130,272] 13 := by
  apply FastRouting.sound _ _ [112,5,130,272] 13 (by decide) (choices 1) [1,8,32,128] r2820 c2820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1614
  · exact u1615
  · exact u1616
  · exact u1617

def b2821 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 134 392 121 121 121 249 377), lower := (rows 113 7 134 392 16 32 64 128 256), losses := [] }

theorem u2821 : Upper (D 0) (R 0) [112,5,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2821
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2822 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 140 25 498 482 482 482 482), lower := (rows 113 7 140 25 16 32 64 128 256), losses := [] }

theorem u2822 : Upper (D 0) (R 0) [112,5,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2822
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2823 : PairBound 9 := { available := 481, camps := [], pairs := [(2,4)], upper := (rows 113 7 140 26 497 481 481 481 481), lower := (rows 113 7 140 26 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 12 8 0 35 67 131 259), good := (rows 481 487 140 494 0 32 64 128 256) }] }

theorem u2823 : Upper (D 0) (R 0) [112,5,136,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2823
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2824 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 113 7 140 56 467 483 451 451 451), lower := (rows 113 7 140 56 16 32 64 128 256), losses := [] }

theorem u2824 : Upper (D 0) (R 0) [112,5,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2824
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2825 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 140 137 370 370 370 498 370), lower := (rows 113 7 140 137 16 32 64 128 256), losses := [] }

theorem u2825 : Upper (D 0) (R 0) [112,5,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2825
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2826 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 7 140 138 369 369 369 497 369), lower := (rows 113 7 140 138 16 32 64 128 256), losses := [] }

theorem u2826 : Upper (D 0) (R 0) [112,5,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2826
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2827 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 7 140 152 371 355 355 483 355), lower := (rows 113 7 140 152 16 32 64 128 256), losses := [] }

theorem u2827 : Upper (D 0) (R 0) [112,5,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2827
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2828 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2828 : Upper (D 0) (R 0) [112,5,136,257] 13 := by
  apply FastRouting.sound _ _ [112,5,136,257] 13 (by decide) (choices 1) [2,32,128] r2828 c2828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1618
  · exact u1619
  · exact u1620

def r2829 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2829 : Upper (D 0) (R 0) [112,5,136,258] 13 := by
  apply FastRouting.sound _ _ [112,5,136,258] 13 (by decide) (choices 1) [1,32,128] r2829 c2829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1621
  · exact u1622
  · exact u1623

def r2830 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2830 : Upper (D 0) (R 0) [112,5,136,272] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272] 13 (by decide) (choices 1) [1,2,32,128] r2830 c2830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1624
  · exact u1625
  · exact u1626
  · exact u1627

def b2831 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 7 140 392 115 115 115 243 371), lower := (rows 113 7 140 392 16 32 64 128 256), losses := [] }

theorem u2831 : Upper (D 0) (R 0) [112,5,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2831
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2832 : PairBound 9 := { available := 457, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 42 473 489 457 457 457), lower := (rows 113 7 148 42 16 32 64 128 256), losses := [] }

theorem u2832 : Upper (D 0) (R 0) [112,5,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2832
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2833 : PairBound 9 := { available := 362, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 137 378 362 362 490 362), lower := (rows 113 7 148 137 16 32 64 128 256), losses := [] }

theorem u2833 : Upper (D 0) (R 0) [112,5,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2833
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2834 : PairBound 9 := { available := 361, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 138 377 361 361 489 361), lower := (rows 113 7 148 138 16 32 64 128 256), losses := [] }

theorem u2834 : Upper (D 0) (R 0) [112,5,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2834
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2835 : PairBound 9 := { available := 331, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 168 347 363 331 459 331), lower := (rows 113 7 148 168 16 32 64 128 256), losses := [] }

theorem u2835 : Upper (D 0) (R 0) [112,5,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2835
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2836 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 265 250 234 234 234 490), lower := (rows 113 7 148 265 16 32 64 128 256), losses := [] }

theorem u2836 : Upper (D 0) (R 0) [112,5,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2836
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2837 : PairBound 9 := { available := 233, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 266 249 233 233 233 489), lower := (rows 113 7 148 266 16 32 64 128 256), losses := [] }

theorem u2837 : Upper (D 0) (R 0) [112,5,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2837
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2838 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 296 219 235 203 203 459), lower := (rows 113 7 148 296 16 32 64 128 256), losses := [] }

theorem u2838 : Upper (D 0) (R 0) [112,5,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2838
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2839 : PairBound 9 := { available := 107, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 392 123 107 107 235 363), lower := (rows 113 7 148 392 16 32 64 128 256), losses := [] }

theorem u2839 : Upper (D 0) (R 0) [112,5,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2839
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2840 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 261 26 248 232 232 232 488), lower := (rows 113 7 261 26 16 32 64 128 256), losses := [] }

theorem u2840 : Upper (D 0) (R 0) [112,5,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2840
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2841 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 261 138 248 248 248 248 504), lower := (rows 113 7 261 138 16 32 64 128 256), losses := [] }

theorem u2841 : Upper (D 0) (R 0) [112,5,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2841
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2842 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 261 152 250 234 234 234 490), lower := (rows 113 7 261 152 16 32 64 128 256), losses := [] }

theorem u2842 : Upper (D 0) (R 0) [112,5,257,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2842
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2843 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 262 25 248 232 232 232 488), lower := (rows 113 7 262 25 16 32 64 128 256), losses := [] }

theorem u2843 : Upper (D 0) (R 0) [112,5,258,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2843
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2844 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 113 7 262 56 217 233 201 201 457), lower := (rows 113 7 262 56 16 32 64 128 256), losses := [] }

theorem u2844 : Upper (D 0) (R 0) [112,5,258,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2844
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2845 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2845 : Upper (D 0) (R 0) [112,5,258,129] 13 := by
  apply FastRouting.sound _ _ [112,5,258,129] 13 (by decide) (choices 1) [8,32,128] r2845 c2845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1628
  · exact u1629
  · exact u1630

def r2846 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2846 : Upper (D 0) (R 0) [112,5,258,144] 13 := by
  apply FastRouting.sound _ _ [112,5,258,144] 13 (by decide) (choices 1) [1,8,32,128] r2846 c2846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1631
  · exact u1632
  · exact u1633
  · exact u1634

def b2847 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 268 25 242 226 226 226 482), lower := (rows 113 7 268 25 16 32 64 128 256), losses := [] }

theorem u2847 : Upper (D 0) (R 0) [112,5,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2847
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2848 : PairBound 9 := { available := 225, camps := [], pairs := [(2,4)], upper := (rows 113 7 268 26 241 225 225 225 481), lower := (rows 113 7 268 26 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 12 8 0 35 67 131 259), good := (rows 481 487 268 494 0 32 64 128 256) }] }

theorem u2848 : Upper (D 0) (R 0) [112,5,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2848
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2849 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 113 7 268 56 211 227 195 195 451), lower := (rows 113 7 268 56 16 32 64 128 256), losses := [] }

theorem u2849 : Upper (D 0) (R 0) [112,5,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2849
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2850 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2850 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2850 : Upper (D 0) (R 0) [112,5,264,129] 13 := by
  apply FastRouting.sound _ _ [112,5,264,129] 13 (by decide) (choices 1) [2,32,128] r2850 c2850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1635
  · exact u1636
  · exact u1637

def r2851 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2851 : Upper (D 0) (R 0) [112,5,264,130] 13 := by
  apply FastRouting.sound _ _ [112,5,264,130] 13 (by decide) (choices 1) [1,32,128] r2851 c2851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1638
  · exact u1639
  · exact u1640

def r2852 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2852 : Upper (D 0) (R 0) [112,5,264,144] 13 := by
  apply FastRouting.sound _ _ [112,5,264,144] 13 (by decide) (choices 1) [1,2,32,128] r2852 c2852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1641
  · exact u1642
  · exact u1643
  · exact u1644

def b2853 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 276 42 217 233 201 201 457), lower := (rows 113 7 276 42 16 32 64 128 256), losses := [] }

theorem u2853 : Upper (D 0) (R 0) [112,5,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2853
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2854 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 276 137 250 234 234 234 490), lower := (rows 113 7 276 137 16 32 64 128 256), losses := [] }

theorem u2854 : Upper (D 0) (R 0) [112,5,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2854
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2855 : PairBound 9 := { available := 233, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 276 138 249 233 233 233 489), lower := (rows 113 7 276 138 16 32 64 128 256), losses := [] }

theorem u2855 : Upper (D 0) (R 0) [112,5,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2855
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2856 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 276 168 219 235 203 203 459), lower := (rows 113 7 276 168 16 32 64 128 256), losses := [] }

theorem u2856 : Upper (D 0) (R 0) [112,5,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2856
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2857 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 388 25 250 234 234 234 490), lower := (rows 113 7 388 25 16 32 64 128 256), losses := [] }

theorem u2857 : Upper (D 0) (R 0) [112,5,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2857
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2858 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2858 : Upper (D 0) (R 0) [112,5,384,18] 13 := by
  apply FastRouting.sound _ _ [112,5,384,18] 13 (by decide) (choices 1) [1,8,32,128] r2858 c2858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1645
  · exact u1646
  · exact u1647
  · exact u1648

def b2859 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 113 7 388 56 219 235 203 203 459), lower := (rows 113 7 388 56 16 32 64 128 256), losses := [] }

theorem u2859 : Upper (D 0) (R 0) [112,5,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2859
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2860 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2860 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2860 : Upper (D 0) (R 0) [112,5,384,129] 13 := by
  apply FastRouting.sound _ _ [112,5,384,129] 13 (by decide) (choices 1) [2,8,32] r2860 c2860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1649
  · exact u1650
  · exact u1651

def b2861 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 388 138 121 121 121 249 377), lower := (rows 113 7 388 138 16 32 64 128 256), losses := [] }

theorem u2861 : Upper (D 0) (R 0) [112,5,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2861
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2862 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2862 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2862 : Upper (D 0) (R 0) [112,5,384,144] 13 := by
  apply FastRouting.sound _ _ [112,5,384,144] 13 (by decide) (choices 1) [1,2,8,32] r2862 c2862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1652
  · exact u1653
  · exact u1654
  · exact u1655

def b2863 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 113 14 21 137 498 482 482 482 482), lower := (rows 113 14 21 137 16 32 64 128 256), losses := [] }

theorem u2863 : Upper (D 0) (R 0) [112,12,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2863
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2864 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 113 14 21 138 497 481 481 481 481), lower := (rows 113 14 21 138 16 32 64 128 256), losses := [] }

theorem u2864 : Upper (D 0) (R 0) [112,12,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2864
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2865 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 113 14 21 168 467 483 451 451 451), lower := (rows 113 14 21 168 16 32 64 128 256), losses := [] }

theorem u2865 : Upper (D 0) (R 0) [112,12,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2865
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2866 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 113 14 21 265 242 226 226 226 482), lower := (rows 113 14 21 265 16 32 64 128 256), losses := [] }

theorem u2866 : Upper (D 0) (R 0) [112,12,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2866
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2867 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 113 14 21 266 241 225 225 225 481), lower := (rows 113 14 21 266 16 32 64 128 256), losses := [] }

theorem u2867 : Upper (D 0) (R 0) [112,12,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2867
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2868 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 113 14 21 296 211 227 195 195 451), lower := (rows 113 14 21 296 16 32 64 128 256), losses := [] }

theorem u2868 : Upper (D 0) (R 0) [112,12,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2868
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2869 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 113 14 21 392 243 227 227 227 483), lower := (rows 113 14 21 392 16 32 64 128 256), losses := [] }

theorem u2869 : Upper (D 0) (R 0) [112,12,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2869
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2870 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 14 22 137 497 481 481 481 481), lower := (rows 113 14 22 137 16 32 64 128 256), losses := [] }

theorem u2870 : Upper (D 0) (R 0) [112,12,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2870
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2871 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 14 22 168 465 481 449 449 449), lower := (rows 113 14 22 168 16 32 64 128 256), losses := [] }

theorem u2871 : Upper (D 0) (R 0) [112,12,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2871
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2872 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 14 22 265 241 225 225 225 481), lower := (rows 113 14 22 265 16 32 64 128 256), losses := [] }

theorem u2872 : Upper (D 0) (R 0) [112,12,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2872
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2873 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 14 22 296 209 225 193 193 449), lower := (rows 113 14 22 296 16 32 64 128 256), losses := [] }

theorem u2873 : Upper (D 0) (R 0) [112,12,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2873
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2874 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 14 22 392 241 225 225 225 481), lower := (rows 113 14 22 392 16 32 64 128 256), losses := [] }

theorem u2874 : Upper (D 0) (R 0) [112,12,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2874
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2875 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 113 14 52 137 467 483 451 451 451), lower := (rows 113 14 52 137 16 32 64 128 256), losses := [] }

theorem u2875 : Upper (D 0) (R 0) [112,12,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2875
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2876 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 113 14 52 138 465 481 449 449 449), lower := (rows 113 14 52 138 16 32 64 128 256), losses := [] }

theorem u2876 : Upper (D 0) (R 0) [112,12,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2876
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2877 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 113 14 52 200 403 419 451 387 387), lower := (rows 113 14 52 200 16 32 64 128 256), losses := [] }

theorem u2877 : Upper (D 0) (R 0) [112,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2877
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2878 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 113 14 52 265 211 227 195 195 451), lower := (rows 113 14 52 265 16 32 64 128 256), losses := [] }

theorem u2878 : Upper (D 0) (R 0) [112,12,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2878
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2879 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 113 14 52 266 209 225 193 193 449), lower := (rows 113 14 52 266 16 32 64 128 256), losses := [] }

theorem u2879 : Upper (D 0) (R 0) [112,12,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2879
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u2879
end Delivery.IrregularNine14.P00
