import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0047
import IrregularNine14P01C0048

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6600 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 196 268 59 59 123 187 315), lower := (rows 51 194 196 268 16 32 64 128 256), losses := [] }

theorem u6600 : Upper (D 1) (R 1) [50,192,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6600
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6601 : PairBound 9 := { available := 47, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 196 280 63 47 111 175 303), lower := (rows 51 194 196 280 16 32 64 128 256), losses := [] }

theorem u6601 : Upper (D 1) (R 1) [50,192,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6601
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6602 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 259 14 28 240 224 224 224 480), lower := (rows 51 259 14 28 16 32 64 128 256), losses := [] }

theorem u6602 : Upper (D 1) (R 1) [50,257,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6602
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6603 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 14 76 240 240 240 240 496), lower := (rows 51 259 14 76 16 32 64 128 256), losses := [] }

theorem u6603 : Upper (D 1) (R 1) [50,257,10,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6603
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6604 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 14 88 244 228 228 228 484), lower := (rows 51 259 14 88 16 32 64 128 256), losses := [] }

theorem u6604 : Upper (D 1) (R 1) [50,257,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6604
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6605 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 14 200 244 244 244 244 500), lower := (rows 51 259 14 200 16 32 64 128 256), losses := [] }

theorem u6605 : Upper (D 1) (R 1) [50,257,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6605
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6606 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 259 22 44 216 232 200 200 456), lower := (rows 51 259 22 44 16 32 64 128 256), losses := [] }

theorem u6606 : Upper (D 1) (R 1) [50,257,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6606
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6607 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 259 22 76 248 232 232 232 488), lower := (rows 51 259 22 76 16 32 64 128 256), losses := [] }

theorem u6607 : Upper (D 1) (R 1) [50,257,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6607
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6608 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 259 22 104 220 236 204 204 460), lower := (rows 51 259 22 104 16 32 64 128 256), losses := [] }

theorem u6608 : Upper (D 1) (R 1) [50,257,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6608
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6609 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 259 22 200 252 236 236 236 492), lower := (rows 51 259 22 200 16 32 64 128 256), losses := [] }

theorem u6609 : Upper (D 1) (R 1) [50,257,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6609
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6610 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 28 44 210 226 194 194 450), lower := (rows 51 259 28 44 16 32 64 128 256), losses := [] }

theorem u6610 : Upper (D 1) (R 1) [50,257,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6610
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6611 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 180, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 28 74 244 228 228 228 484), lower := (rows 51 259 28 74 16 32 64 128 256), losses := [] }

theorem u6611 : Upper (D 1) (R 1) [50,257,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6611
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6612 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 259 28 76 242 226 226 226 482), lower := (rows 51 259 28 76 16 32 64 128 256), losses := [] }

theorem u6612 : Upper (D 1) (R 1) [50,257,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6612
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6613 : Route 9 := (fun mask => (mask,id))

def c6613 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6613 : Upper (D 1) (R 1) [50,257,24,96] 13 := by
  apply FastRouting.sound _ _ [50,257,24,96] 13 (by decide) (choices 1) [2,4,64,128] r6613 c6613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2854
  · exact u2855
  · exact u2856
  · exact u2857

def r6614 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6614 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u6614 : Upper (D 1) (R 1) [50,257,24,192] 13 := by
  apply FastRouting.sound _ _ [50,257,24,192] 13 (by decide) (choices 1) [2,4,32,64] r6614 c6614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2858
  · exact u2859
  · exact u2860
  · exact u2861

def b6615 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 52 76 218 234 202 202 458), lower := (rows 51 259 52 76 16 32 64 128 256), losses := [] }

theorem u6615 : Upper (D 1) (R 1) [50,257,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6615
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6616 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 52 200 222 238 206 206 462), lower := (rows 51 259 52 200 16 32 64 128 256), losses := [] }

theorem u6616 : Upper (D 1) (R 1) [50,257,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6616
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6617 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 259 70 76 184 184 248 184 440), lower := (rows 51 259 70 76 16 32 64 128 256), losses := [] }

theorem u6617 : Upper (D 1) (R 1) [50,257,66,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6617
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6618 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 70 88 188 172 236 172 428), lower := (rows 51 259 70 88 16 32 64 128 256), losses := [] }

theorem u6618 : Upper (D 1) (R 1) [50,257,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6618
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6619 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 70 140 248 248 248 248 504), lower := (rows 51 259 70 140 16 32 64 128 256), losses := [] }

theorem u6619 : Upper (D 1) (R 1) [50,257,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6619
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6620 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 70 152 252 236 236 236 492), lower := (rows 51 259 70 152 16 32 64 128 256), losses := [] }

theorem u6620 : Upper (D 1) (R 1) [50,257,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6620
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6621 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 70 200 188 188 252 188 444), lower := (rows 51 259 70 200 16 32 64 128 256), losses := [] }

theorem u6621 : Upper (D 1) (R 1) [50,257,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6621
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6622 : PairBound 9 := { available := 178, camps := [{ cop := 6, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 76 76 178 178 242 178 434), lower := (rows 51 259 76 76 16 32 64 128 256), losses := [] }

theorem u6622 : Upper (D 1) (R 1) [50,257,72,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6622
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6623 : PairBound 9 := { available := 166, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 76 88 182 166 230 166 422), lower := (rows 51 259 76 88 16 32 64 128 256), losses := [] }

theorem u6623 : Upper (D 1) (R 1) [50,257,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6623
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m6624_128 : Upper (D 1) (R 1) [50,257,72,132,128] 13 :=
  permutation_upper _ _ _ [50,257,72,132,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2864

def r6624 : Route 9 := (fun mask => (mask,id))

def c6624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6624 : Upper (D 1) (R 1) [50,257,72,132] 13 := by
  apply FastRouting.sound _ _ [50,257,72,132] 13 (by decide) (choices 1) [2,32,64,128] r6624 c6624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2862
  · exact u2863
  · exact u2864
  · exact m6624_128

def r6625 : Route 9 := (fun mask => (mask,id))

def c6625 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u6625 : Upper (D 1) (R 1) [50,257,72,144] 13 := by
  apply FastRouting.sound _ _ [50,257,72,144] 13 (by decide) (choices 1) [2,4,32,64,128] r6625 c6625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2865
  · exact u2866
  · exact u2867
  · exact u2868
  · exact u2869

def b6626 : PairBound 9 := { available := 182, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 76 200 182 182 246 182 438), lower := (rows 51 259 76 200 16 32 64 128 256), losses := [] }

theorem u6626 : Upper (D 1) (R 1) [50,257,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6626
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6627 : Route 9 := (fun mask => (mask,id))

def c6627 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6627 : Upper (D 1) (R 1) [50,257,80,96] 13 := by
  apply FastRouting.sound _ _ [50,257,80,96] 13 (by decide) (choices 1) [2,4,8,128] r6627 c6627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2870
  · exact u2871
  · exact u2872
  · exact u2873

def r6628 : Route 9 := (fun mask => (mask,id))

def c6628 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u6628 : Upper (D 1) (R 1) [50,257,80,160] 13 := by
  apply FastRouting.sound _ _ [50,257,80,160] 13 (by decide) (choices 1) [2,4,8,64,128] r6628 c6628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2874
  · exact u2875
  · exact u2876
  · exact u2877
  · exact u2878

def r6629 : Route 9 := (fun mask => (mask,id))

def c6629 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u6629 : Upper (D 1) (R 1) [50,257,80,192] 13 := by
  apply FastRouting.sound _ _ [50,257,80,192] 13 (by decide) (choices 1) [2,4,8,32,128] r6629 c6629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2879
  · exact u2880
  · exact u2881
  · exact u2882
  · exact u2883

def b6630 : PairBound 9 := { available := 62, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 196 200 62 62 126 190 318), lower := (rows 51 259 196 200 16 32 64 128 256), losses := [] }

theorem u6630 : Upper (D 1) (R 1) [50,257,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6630
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6631 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 262 13 26 240 224 224 224 480), lower := (rows 51 262 13 26 16 32 64 128 256), losses := [] }

theorem u6631 : Upper (D 1) (R 1) [50,260,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6631
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6632 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 13 56 210 226 194 194 450), lower := (rows 51 262 13 56 16 32 64 128 256), losses := [] }

theorem u6632 : Upper (D 1) (R 1) [50,260,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6632
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6633 : Route 9 := (fun mask => (mask,id))

def c6633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6633 : Upper (D 1) (R 1) [50,260,9,66] 13 := by
  apply FastRouting.sound _ _ [50,260,9,66] 13 (by decide) (choices 1) [32,64,128] r6633 c6633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2884
  · exact u2885
  · exact u2886

def b6634 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 262 13 88 242 226 226 226 482), lower := (rows 51 262 13 88 16 32 64 128 256), losses := [] }

theorem u6634 : Upper (D 1) (R 1) [50,260,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6634
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6635 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6635 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6635 : Upper (D 1) (R 1) [50,260,9,192] 13 := by
  apply FastRouting.sound _ _ [50,260,9,192] 13 (by decide) (choices 1) [2,32,64] r6635 c6635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2887
  · exact u2888
  · exact u2889

def b6636 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 262 69 26 248 232 232 232 488), lower := (rows 51 262 69 26 16 32 64 128 256), losses := [] }

theorem u6636 : Upper (D 1) (R 1) [50,260,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6636
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6637 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 262 69 56 218 234 202 202 458), lower := (rows 51 262 69 56 16 32 64 128 256), losses := [] }

theorem u6637 : Upper (D 1) (R 1) [50,260,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6637
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6638 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 262 69 74 184 184 248 184 440), lower := (rows 51 262 69 74 16 32 64 128 256), losses := [] }

theorem u6638 : Upper (D 1) (R 1) [50,260,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6638
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6639 : Route 9 := (fun mask => (mask,id))

def c6639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6639 : Upper (D 1) (R 1) [50,260,65,80] 13 := by
  apply FastRouting.sound _ _ [50,260,65,80] 13 (by decide) (choices 1) [2,8,32,128] r6639 c6639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2890
  · exact u2891
  · exact u2892
  · exact u2893

def r6640 : Route 9 := (fun mask => (mask,id))

def c6640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u6640 : Upper (D 1) (R 1) [50,260,65,130] 13 := by
  apply FastRouting.sound _ _ [50,260,65,130] 13 (by decide) (choices 1) [8,32,64,128] r6640 c6640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2894
  · exact u2895
  · exact u2896
  · exact u2897

def r6641 : Route 9 := (fun mask => (mask,id))

def c6641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6641 : Upper (D 1) (R 1) [50,260,65,144] 13 := by
  apply FastRouting.sound _ _ [50,260,65,144] 13 (by decide) (choices 1) [2,8,32,64,128] r6641 c6641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2898
  · exact u2899
  · exact u2900
  · exact u2901
  · exact u2902

def r6642 : Route 9 := (fun mask => (mask,id))

def c6642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6642 : Upper (D 1) (R 1) [50,260,65,192] 13 := by
  apply FastRouting.sound _ _ [50,260,65,192] 13 (by decide) (choices 1) [2,8,32,128] r6642 c6642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2903
  · exact u2904
  · exact u2905
  · exact u2906

def b6643 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 262 76 11 240 240 240 240 496), lower := (rows 51 262 76 11 16 32 64 128 256), losses := [] }

theorem u6643 : Upper (D 1) (R 1) [50,260,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6643
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6644 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 262 76 25 242 226 226 226 482), lower := (rows 51 262 76 25 16 32 64 128 256), losses := [] }

theorem u6644 : Upper (D 1) (R 1) [50,260,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6644
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6645 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 262 76 26 241 225 225 225 481), lower := (rows 51 262 76 26 16 32 64 128 256), losses := [] }

theorem u6645 : Upper (D 1) (R 1) [50,260,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6645
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6646 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 262 76 56 211 227 195 195 451), lower := (rows 51 262 76 56 16 32 64 128 256), losses := [] }

theorem u6646 : Upper (D 1) (R 1) [50,260,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6646
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6647 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 76 73 178 178 242 178 434), lower := (rows 51 262 76 73 16 32 64 128 256), losses := [] }

theorem u6647 : Upper (D 1) (R 1) [50,260,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6647
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6648 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 76 74 177 177 241 177 433), lower := (rows 51 262 76 74 16 32 64 128 256), losses := [] }

theorem u6648 : Upper (D 1) (R 1) [50,260,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6648
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6649 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 76 88 179 163 227 163 419), lower := (rows 51 262 76 88 16 32 64 128 256), losses := [] }

theorem u6649 : Upper (D 1) (R 1) [50,260,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6649
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6650 : Route 9 := (fun mask => (mask,id))

def c6650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6650 : Upper (D 1) (R 1) [50,260,72,129] 13 := by
  apply FastRouting.sound _ _ [50,260,72,129] 13 (by decide) (choices 1) [2,32,64,128] r6650 c6650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2907
  · exact u2908
  · exact u2909
  · exact u2910

def r6651 : Route 9 := (fun mask => (mask,id))

def c6651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6651 : Upper (D 1) (R 1) [50,260,72,130] 13 := by
  apply FastRouting.sound _ _ [50,260,72,130] 13 (by decide) (choices 1) [1,32,64,128] r6651 c6651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2911
  · exact u2912
  · exact u2913
  · exact u2914

def r6652 : Route 9 := (fun mask => (mask,id))

def c6652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6652 : Upper (D 1) (R 1) [50,260,72,144] 13 := by
  apply FastRouting.sound _ _ [50,260,72,144] 13 (by decide) (choices 1) [1,2,32,64,128] r6652 c6652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2915
  · exact u2916
  · exact u2917
  · exact u2918
  · exact u2919

def b6653 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 76 200 179 179 243 179 435), lower := (rows 51 262 76 200 16 32 64 128 256), losses := [] }

theorem u6653 : Upper (D 1) (R 1) [50,260,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6653
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6654 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 262 196 11 248 248 248 248 504), lower := (rows 51 262 196 11 16 32 64 128 256), losses := [] }

theorem u6654 : Upper (D 1) (R 1) [50,260,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6654
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6655 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 262 196 25 250 234 234 234 490), lower := (rows 51 262 196 25 16 32 64 128 256), losses := [] }

theorem u6655 : Upper (D 1) (R 1) [50,260,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6655
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6656 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 262 196 26 249 233 233 233 489), lower := (rows 51 262 196 26 16 32 64 128 256), losses := [] }

theorem u6656 : Upper (D 1) (R 1) [50,260,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6656
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6657 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 262 196 56 219 235 203 203 459), lower := (rows 51 262 196 56 16 32 64 128 256), losses := [] }

theorem u6657 : Upper (D 1) (R 1) [50,260,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6657
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6658 : Route 9 := (fun mask => (mask,id))

def c6658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6658 : Upper (D 1) (R 1) [50,260,192,65] 13 := by
  apply FastRouting.sound _ _ [50,260,192,65] 13 (by decide) (choices 1) [2,8,32,128] r6658 c6658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2920
  · exact u2921
  · exact u2922
  · exact u2923

def b6659 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 262 196 74 185 185 249 185 441), lower := (rows 51 262 196 74 16 32 64 128 256), losses := [] }

theorem u6659 : Upper (D 1) (R 1) [50,260,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6659
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6659
end Delivery.IrregularNine14.P01
