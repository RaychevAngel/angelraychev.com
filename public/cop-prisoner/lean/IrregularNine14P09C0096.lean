import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0038

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5760 : Route 9 := (fun mask => (mask,id))

def c5760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5760 : Upper (D 9) (R 9) [96,5,136,288,320,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,320,2] 13 (by decide) (choices 1) [1,16,128] r5760 c5760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2283
  · exact u2284
  · exact u2285

def b5761 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 7 140 296 336 48 195 131 387), lower := (rows 97 7 140 296 336 48 64 128 256), losses := [] }

theorem u5761 : Upper (D 9) (R 9) [96,5,136,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5761 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5762 : Route 9 := (fun mask => (mask,id))

def c5762 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5762 : Upper (D 9) (R 9) [96,5,136,288,320,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,320,128] 13 (by decide) (choices 1) [1,2,16] r5762 c5762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2286
  · exact u2287
  · exact u2288

def r5763 : Route 9 := (fun mask => (mask,id))

def c5763 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5763 : Upper (D 9) (R 9) [96,5,136,288,384,1] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,384,1] 13 (by decide) (choices 1) [2,16] r5763 c5763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2289
  · exact u2290

def r5764 : Route 9 := (fun mask => (mask,id))

def c5764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5764 : Upper (D 9) (R 9) [96,5,136,288,384,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,384,2] 13 (by decide) (choices 1) [1,16] r5764 c5764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2291
  · exact u2292

def b5765 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 7 140 296 400 48 67 195 323), lower := (rows 97 7 140 296 400 48 64 128 256), losses := [] }

theorem u5765 : Upper (D 9) (R 9) [96,5,136,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5765 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5766 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 296 400 96 83 147 275), lower := (rows 97 7 140 296 400 96 64 128 256), losses := [] }

theorem u5766 : Upper (D 9) (R 9) [96,5,136,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5766 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5767 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 164 25 208 34 328 392 264), lower := (rows 97 7 164 25 208 34 64 128 256), losses := [] }

theorem u5767 : Upper (D 9) (R 9) [96,5,160,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5767 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5768 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 164 25 208 40 322 386 258), lower := (rows 97 7 164 25 208 40 64 128 256), losses := [] }

theorem u5768 : Upper (D 9) (R 9) [96,5,160,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5768 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5769_2 : Upper (D 9) (R 9) [96,5,160,17,192,256,2] 13 :=
  permutation_upper _ _ _ [96,5,160,17,192,8,256] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2294

theorem m5769_8 : Upper (D 9) (R 9) [96,5,160,17,192,256,8] 13 :=
  permutation_upper _ _ _ [96,5,160,17,192,2,256] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2293

def r5769 : Route 9 := (fun mask => (mask,id))

def c5769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5769 : Upper (D 9) (R 9) [96,5,160,17,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17,192,256] 13 (by decide) (choices 1) [2,8,256] r5769 c5769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5769_2
  · exact m5769_8
  · exact u2295

def b5770 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 25 336 34 456 392 392), lower := (rows 97 7 164 25 336 34 64 128 256), losses := [] }

theorem u5770 : Upper (D 9) (R 9) [96,5,160,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5770 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5771 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 97 7 164 25 336 40 450 386 386), lower := (rows 97 7 164 25 336 40 64 128 256), losses := [] }

theorem u5771 : Upper (D 9) (R 9) [96,5,160,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5771 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5772 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 25 336 160 330 394 266), lower := (rows 97 7 164 25 336 160 64 128 256), losses := [] }

theorem u5772 : Upper (D 9) (R 9) [96,5,160,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5772 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5773 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 3, region := 422, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 25 336 288 202 138 394), lower := (rows 97 7 164 25 336 288 64 128 256), losses := [] }

theorem u5773 : Upper (D 9) (R 9) [96,5,160,17,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5773 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5774 : Route 9 := (fun mask => (mask,id))

def c5774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5774 : Upper (D 9) (R 9) [96,5,160,17,384,2] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17,384,2] 13 (by decide) (choices 1) [8,256] r5774 c5774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2296
  · exact u2297

def b5775 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 164 25 400 40 322 450 322), lower := (rows 97 7 164 25 400 40 64 128 256), losses := [] }

theorem u5775 : Upper (D 9) (R 9) [96,5,160,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5775 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5776 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 25 400 96 330 394 266), lower := (rows 97 7 164 25 400 96 64 128 256), losses := [] }

theorem u5776 : Upper (D 9) (R 9) [96,5,160,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5776 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5777 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 65 }], pairs := [(1,6),(2,0),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 25 400 288 74 202 330), lower := (rows 97 7 164 25 400 288 64 128 256), losses := [{ target := 6, region := (rows 1 10 20 8 16 304 0 128 256), good := (rows 33 7 164 63 436 288 0 128 288) }] }

theorem u5777 : Upper (D 9) (R 9) [96,5,160,17,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5777 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5778 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 26 88 33 448 384 384), lower := (rows 97 7 164 26 88 33 64 128 256), losses := [] }

theorem u5778 : Upper (D 9) (R 9) [96,5,160,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5778 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5779 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 26 88 160 321 385 257), lower := (rows 97 7 164 26 88 160 64 128 256), losses := [] }

theorem u5779 : Upper (D 9) (R 9) [96,5,160,18,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5779 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5780 : Route 9 := (fun mask => (mask,id))

def c5780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5780 : Upper (D 9) (R 9) [96,5,160,18,72,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,72,256] 13 (by decide) (choices 1) [1,128,256] r5780 c5780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2298
  · exact u2299
  · exact u2300

def b5781 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 46, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 164 26 145 40 320 448 320), lower := (rows 97 7 164 26 145 40 64 128 256), losses := [] }

theorem u5781 : Upper (D 9) (R 9) [96,5,160,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5781 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5782 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 26 145 96 328 392 264), lower := (rows 97 7 164 26 145 96 64 128 256), losses := [] }

theorem u5782 : Upper (D 9) (R 9) [96,5,160,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5782 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5783 : Route 9 := (fun mask => (mask,id))

def c5783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5783 : Upper (D 9) (R 9) [96,5,160,18,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,129,256] 13 (by decide) (choices 1) [8,256] r5783 c5783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2301
  · exact u2302

def b5784 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 26 152 33 320 448 320), lower := (rows 97 7 164 26 152 33 64 128 256), losses := [] }

theorem u5784 : Upper (D 9) (R 9) [96,5,160,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5784 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5785 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 26 152 96 321 385 257), lower := (rows 97 7 164 26 152 96 64 128 256), losses := [] }

theorem u5785 : Upper (D 9) (R 9) [96,5,160,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5785 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5786 : Route 9 := (fun mask => (mask,id))

def c5786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5786 : Upper (D 9) (R 9) [96,5,160,18,136,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,136,256] 13 (by decide) (choices 1) [1,256] r5786 c5786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2303
  · exact u2304

def b5787 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 26 208 33 328 392 264), lower := (rows 97 7 164 26 208 33 64 128 256), losses := [] }

theorem u5787 : Upper (D 9) (R 9) [96,5,160,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5787 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5788 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 164 26 208 40 321 385 257), lower := (rows 97 7 164 26 208 40 64 128 256), losses := [] }

theorem u5788 : Upper (D 9) (R 9) [96,5,160,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5788 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5789 : Route 9 := (fun mask => (mask,id))

def c5789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5789 : Upper (D 9) (R 9) [96,5,160,18,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,192,256] 13 (by decide) (choices 1) [1,8,256] r5789 c5789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2305
  · exact u2306
  · exact u2307

def r5790 : Route 9 := (fun mask => (mask,id))

def c5790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5790 : Upper (D 9) (R 9) [96,5,160,18,257,8] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,257,8] 13 (by decide) (choices 1) [128,256] r5790 c5790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2308
  · exact u2309

def b5791 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 26 273 96 456 392 392), lower := (rows 97 7 164 26 273 96 64 128 256), losses := [] }

theorem u5791 : Upper (D 9) (R 9) [96,5,160,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5791 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5792 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 26 273 160 328 456 328), lower := (rows 97 7 164 26 273 160 64 128 256), losses := [] }

theorem u5792 : Upper (D 9) (R 9) [96,5,160,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5792 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5793 : Route 9 := (fun mask => (mask,id))

def c5793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5793 : Upper (D 9) (R 9) [96,5,160,18,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,257,256] 13 (by decide) (choices 1) [8,128] r5793 c5793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2310
  · exact u2311

def b5794 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 26 280 33 448 448 448), lower := (rows 97 7 164 26 280 33 64 128 256), losses := [] }

theorem u5794 : Upper (D 9) (R 9) [96,5,160,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5794 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5795 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 26 280 96 449 385 385), lower := (rows 97 7 164 26 280 96 64 128 256), losses := [] }

theorem u5795 : Upper (D 9) (R 9) [96,5,160,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5795 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5796 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 26 280 160 321 449 321), lower := (rows 97 7 164 26 280 160 64 128 256), losses := [] }

theorem u5796 : Upper (D 9) (R 9) [96,5,160,18,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5796 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5797 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 97 7 164 26 280 288 193 193 449), lower := (rows 97 7 164 26 280 288 64 128 256), losses := [] }

theorem u5797 : Upper (D 9) (R 9) [96,5,160,18,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5797 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5798 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 26 336 33 456 392 392), lower := (rows 97 7 164 26 336 33 64 128 256), losses := [] }

theorem u5798 : Upper (D 9) (R 9) [96,5,160,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5798 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5799 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 26 336 40 449 385 385), lower := (rows 97 7 164 26 336 40 64 128 256), losses := [] }

theorem u5799 : Upper (D 9) (R 9) [96,5,160,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5799 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5800 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 26 336 160 329 393 265), lower := (rows 97 7 164 26 336 160 64 128 256), losses := [] }

theorem u5800 : Upper (D 9) (R 9) [96,5,160,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5800 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5801 : Route 9 := (fun mask => (mask,id))

def c5801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5801 : Upper (D 9) (R 9) [96,5,160,18,320,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,320,256] 13 (by decide) (choices 1) [1,8,128] r5801 c5801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2312
  · exact u2313
  · exact u2314

def b5802 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 26 400 33 328 456 328), lower := (rows 97 7 164 26 400 33 64 128 256), losses := [] }

theorem u5802 : Upper (D 9) (R 9) [96,5,160,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5802 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5803 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 164 26 400 40 321 449 321), lower := (rows 97 7 164 26 400 40 64 128 256), losses := [] }

theorem u5803 : Upper (D 9) (R 9) [96,5,160,18,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5803 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5804 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 26 400 96 329 393 265), lower := (rows 97 7 164 26 400 96 64 128 256), losses := [] }

theorem u5804 : Upper (D 9) (R 9) [96,5,160,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5804 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5805 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 65 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 26 400 288 73 201 329), lower := (rows 97 7 164 26 400 288 64 128 256), losses := [] }

theorem u5805 : Upper (D 9) (R 9) [96,5,160,18,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5805 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5806 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 7 164 74 145 40 336 400 272), lower := (rows 97 7 164 74 145 40 64 128 256), losses := [] }

theorem u5806 : Upper (D 9) (R 9) [96,5,160,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5806 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5807 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 38, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 164 74 145 48 328 392 264), lower := (rows 97 7 164 74 145 48 64 128 256), losses := [] }

theorem u5807 : Upper (D 9) (R 9) [96,5,160,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5807 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5808 : Route 9 := (fun mask => (mask,id))

def c5808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5808 : Upper (D 9) (R 9) [96,5,160,66,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,129,256] 13 (by decide) (choices 1) [8,16,256] r5808 c5808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2315
  · exact u2316
  · exact u2317

def b5809 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 74 152 33 336 400 272), lower := (rows 97 7 164 74 152 33 64 128 256), losses := [] }

theorem u5809 : Upper (D 9) (R 9) [96,5,160,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5809 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5810 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 97 7 164 74 152 48 321 385 257), lower := (rows 97 7 164 74 152 48 64 128 256), losses := [] }

theorem u5810 : Upper (D 9) (R 9) [96,5,160,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5810 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5811 : Route 9 := (fun mask => (mask,id))

def c5811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5811 : Upper (D 9) (R 9) [96,5,160,66,136,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,136,256] 13 (by decide) (choices 1) [1,16,256] r5811 c5811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2318
  · exact u2319
  · exact u2320

def b5812 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 7 164 74 273 40 464 400 400), lower := (rows 97 7 164 74 273 40 64 128 256), losses := [] }

theorem u5812 : Upper (D 9) (R 9) [96,5,160,66,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5812 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5813 : Route 9 := (fun mask => (mask,id))

def c5813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5813 : Upper (D 9) (R 9) [96,5,160,66,257,16] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,257,16] 13 (by decide) (choices 1) [8,128,256] r5813 c5813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2321
  · exact u2322
  · exact u2323

def b5814 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 74 273 160 344 408 280), lower := (rows 97 7 164 74 273 160 64 128 256), losses := [] }

theorem u5814 : Upper (D 9) (R 9) [96,5,160,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5814 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5815 : Route 9 := (fun mask => (mask,id))

def c5815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5815 : Upper (D 9) (R 9) [96,5,160,66,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,257,256] 13 (by decide) (choices 1) [8,16,128] r5815 c5815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2324
  · exact u2325
  · exact u2326

def b5816 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 74 280 33 464 400 400), lower := (rows 97 7 164 74 280 33 64 128 256), losses := [] }

theorem u5816 : Upper (D 9) (R 9) [96,5,160,66,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5816 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5817 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 74 280 48 449 385 385), lower := (rows 97 7 164 74 280 48 64 128 256), losses := [] }

theorem u5817 : Upper (D 9) (R 9) [96,5,160,66,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5817 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5818 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 74 280 160 337 401 273), lower := (rows 97 7 164 74 280 160 64 128 256), losses := [] }

theorem u5818 : Upper (D 9) (R 9) [96,5,160,66,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5818 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5819 : Route 9 := (fun mask => (mask,id))

def c5819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5819 : Upper (D 9) (R 9) [96,5,160,66,264,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,264,256] 13 (by decide) (choices 1) [1,16,128] r5819 c5819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2327
  · exact u2328
  · exact u2329

#print axioms u5819
end Delivery.IrregularNine14.P09
