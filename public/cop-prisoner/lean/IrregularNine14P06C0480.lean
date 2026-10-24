import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0168
import IrregularNine14P06C0169

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28800 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 42 52 73 82 421 453 389 389), lower := (rows 7 42 52 73 82 32 64 128 256), losses := [] }

theorem u28800 : Upper (D 6) (R 6) [6,40,48,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28800
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28801 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 490, targets := 4 },{ cop := 0, region := 456, targets := 32 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 7 42 52 73 84 419 451 387 387), lower := (rows 7 42 52 73 84 32 64 128 256), losses := [] }

theorem u28801 : Upper (D 6) (R 6) [6,40,48,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28801
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28802 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 42 52 73 145 358 326 454 326), lower := (rows 7 42 52 73 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 33 65 129 257), good := (rows 486 42 52 490 500 32 64 128 256) }] }

theorem u28802 : Upper (D 6) (R 6) [6,40,48,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28802
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28803 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 328, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 42 52 73 146 357 325 453 325), lower := (rows 7 42 52 73 146 32 64 128 256), losses := [] }

theorem u28803 : Upper (D 6) (R 6) [6,40,48,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28803
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28804 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 328, targets := 32 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 7 42 52 73 148 355 323 451 323), lower := (rows 7 42 52 73 148 32 64 128 256), losses := [] }

theorem u28804 : Upper (D 6) (R 6) [6,40,48,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28804
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28805 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(1,6),(3,5),(4,5)], upper := (rows 7 42 52 73 208 295 327 391 263), lower := (rows 7 42 52 73 208 32 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 33 0 129 257), good := (rows 423 42 52 427 144 32 0 128 256) }] }

theorem u28805 : Upper (D 6) (R 6) [6,40,48,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28805
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28806 : Route 9 := (fun mask => (mask,id))

def c28806 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28806 : Upper (D 6) (R 6) [6,40,48,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,384] 13 (by decide) (choices 1) [1,2,4,64] r28806 c28806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10138
  · exact u10139
  · exact u10140
  · exact u10141

def b28807 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 328, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 52 74 145 357 325 453 325), lower := (rows 7 42 52 74 145 32 64 128 256), losses := [] }

theorem u28807 : Upper (D 6) (R 6) [6,40,48,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28807
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28808 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 328, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 52 74 208 293 325 389 261), lower := (rows 7 42 52 74 208 32 64 128 256), losses := [] }

theorem u28808 : Upper (D 6) (R 6) [6,40,48,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28808
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28809 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 52 74 400 101 69 197 325), lower := (rows 7 42 52 74 400 32 64 128 256), losses := [] }

theorem u28809 : Upper (D 6) (R 6) [6,40,48,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28809
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28810 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 52 76 145 355 323 451 323), lower := (rows 7 42 52 76 145 32 64 128 256), losses := [] }

theorem u28810 : Upper (D 6) (R 6) [6,40,48,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28810
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28811 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 42 52 76 208 291 323 387 259), lower := (rows 7 42 52 76 208 32 64 128 256), losses := [] }

theorem u28811 : Upper (D 6) (R 6) [6,40,48,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28811
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28812 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 52 76 400 99 67 195 323), lower := (rows 7 42 52 76 400 32 64 128 256), losses := [] }

theorem u28812 : Upper (D 6) (R 6) [6,40,48,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28812
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28813 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 42 52 137 273 102 70 198 326), lower := (rows 7 42 52 137 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 33 65 129 257), good := (rows 486 42 52 490 500 32 64 128 256) }] }

theorem u28813 : Upper (D 6) (R 6) [6,40,48,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28813
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28814 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 42 52 137 274 101 69 197 325), lower := (rows 7 42 52 137 274 32 64 128 256), losses := [] }

theorem u28814 : Upper (D 6) (R 6) [6,40,48,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28814
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28815 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 234, targets := 4 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 7 42 52 137 276 99 67 195 323), lower := (rows 7 42 52 137 276 32 64 128 256), losses := [] }

theorem u28815 : Upper (D 6) (R 6) [6,40,48,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28815
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28816 : Route 9 := (fun mask => (mask,id))

def c28816 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28816 : Upper (D 6) (R 6) [6,40,48,129,320] 13 := by
  apply FastRouting.sound _ _ [6,40,48,129,320] 13 (by decide) (choices 1) [1,2,4,64] r28816 c28816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10142
  · exact u10143
  · exact u10144
  · exact u10145

def b28817 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 52 138 336 101 69 197 325), lower := (rows 7 42 52 138 336 32 64 128 256), losses := [] }

theorem u28817 : Upper (D 6) (R 6) [6,40,48,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28817
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28818 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 336, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 52 140 336 99 67 195 323), lower := (rows 7 42 52 140 336 32 64 128 256), losses := [] }

theorem u28818 : Upper (D 6) (R 6) [6,40,48,132,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28818
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m28819_4 : Upper (D 6) (R 6) [6,40,48,192,320,4] 13 :=
  permutation_upper _ _ _ [6,40,48,192,320,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10147

def r28819 : Route 9 := (fun mask => (mask,id))

def c28819 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28819 : Upper (D 6) (R 6) [6,40,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320] 13 (by decide) (choices 1) [1,2,4] r28819 c28819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10146
  · exact u10147
  · exact m28819_4

def b28820 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 10, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 42 84 11 49 484 452 452 452), lower := (rows 7 42 84 11 49 32 64 128 256), losses := [] }

theorem u28820 : Upper (D 6) (R 6) [6,40,80,3,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28820
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28821 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 42 84 11 145 356 356 484 356), lower := (rows 7 42 84 11 145 32 64 128 256), losses := [] }

theorem u28821 : Upper (D 6) (R 6) [6,40,80,3,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28821
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28822 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 84 11 148 353 353 481 353), lower := (rows 7 42 84 11 148 32 64 128 256), losses := [] }

theorem u28822 : Upper (D 6) (R 6) [6,40,80,3,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28822
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28823 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 42 84 11 176 357 325 453 325), lower := (rows 7 42 84 11 176 32 64 128 256), losses := [] }

theorem u28823 : Upper (D 6) (R 6) [6,40,80,3,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28823
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28824 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 42 84 11 400 101 101 229 357), lower := (rows 7 42 84 11 400 32 64 128 256), losses := [] }

theorem u28824 : Upper (D 6) (R 6) [6,40,80,3,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28824
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28825 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 3, region := 482, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 42 84 13 49 482 450 450 450), lower := (rows 7 42 84 13 49 32 64 128 256), losses := [] }

theorem u28825 : Upper (D 6) (R 6) [6,40,80,5,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28825
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28826 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 42 84 13 145 354 354 482 354), lower := (rows 7 42 84 13 145 32 64 128 256), losses := [] }

theorem u28826 : Upper (D 6) (R 6) [6,40,80,5,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28826
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28827 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 354, targets := 4 }], pairs := [(1,2),(3,5),(3,6)], upper := (rows 7 42 84 13 146 353 353 481 353), lower := (rows 7 42 84 13 146 32 64 128 256), losses := [] }

theorem u28827 : Upper (D 6) (R 6) [6,40,80,5,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28827
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28828 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 3, region := 354, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 42 84 13 176 355 323 451 323), lower := (rows 7 42 84 13 176 32 64 128 256), losses := [] }

theorem u28828 : Upper (D 6) (R 6) [6,40,80,5,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28828
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28829 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 42 84 13 400 99 99 227 355), lower := (rows 7 42 84 13 400 32 64 128 256), losses := [] }

theorem u28829 : Upper (D 6) (R 6) [6,40,80,5,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28829
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28830 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 42 84 14 49 481 449 449 449), lower := (rows 7 42 84 14 49 32 64 128 256), losses := [] }

theorem u28830 : Upper (D 6) (R 6) [6,40,80,6,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28830
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28831 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 84 14 145 353 353 481 353), lower := (rows 7 42 84 14 145 32 64 128 256), losses := [] }

theorem u28831 : Upper (D 6) (R 6) [6,40,80,6,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28831
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28832 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 42 84 14 176 353 321 449 321), lower := (rows 7 42 84 14 176 32 64 128 256), losses := [] }

theorem u28832 : Upper (D 6) (R 6) [6,40,80,6,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28832
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28833 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 84 14 400 97 97 225 353), lower := (rows 7 42 84 14 400 32 64 128 256), losses := [] }

theorem u28833 : Upper (D 6) (R 6) [6,40,80,6,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28833
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28834 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 41 145 358 326 454 326), lower := (rows 7 42 84 41 145 32 64 128 256), losses := [] }

theorem u28834 : Upper (D 6) (R 6) [6,40,80,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28834
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28835 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 41 146 357 325 453 325), lower := (rows 7 42 84 41 146 32 64 128 256), losses := [] }

theorem u28835 : Upper (D 6) (R 6) [6,40,80,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28835
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28836 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 41 148 355 323 451 323), lower := (rows 7 42 84 41 148 32 64 128 256), losses := [] }

theorem u28836 : Upper (D 6) (R 6) [6,40,80,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28836
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28837 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 41 400 103 71 199 327), lower := (rows 7 42 84 41 400 32 64 128 256), losses := [] }

theorem u28837 : Upper (D 6) (R 6) [6,40,80,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28837
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28838 : PairBound 9 := { available := 325, camps := [{ cop := 5, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 84 42 145 357 325 453 325), lower := (rows 7 42 84 42 145 32 64 128 256), losses := [] }

theorem u28838 : Upper (D 6) (R 6) [6,40,80,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28838
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28839 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 84 42 148 353 321 449 321), lower := (rows 7 42 84 42 148 32 64 128 256), losses := [] }

theorem u28839 : Upper (D 6) (R 6) [6,40,80,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28839
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28840 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 84 42 400 101 69 197 325), lower := (rows 7 42 84 42 400 32 64 128 256), losses := [] }

theorem u28840 : Upper (D 6) (R 6) [6,40,80,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28840
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28841 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 44 145 355 323 451 323), lower := (rows 7 42 84 44 145 32 64 128 256), losses := [] }

theorem u28841 : Upper (D 6) (R 6) [6,40,80,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28841
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28842 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 44 146 353 321 449 321), lower := (rows 7 42 84 44 146 32 64 128 256), losses := [] }

theorem u28842 : Upper (D 6) (R 6) [6,40,80,36,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28842
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28843 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 44 400 99 67 195 323), lower := (rows 7 42 84 44 400 32 64 128 256), losses := [] }

theorem u28843 : Upper (D 6) (R 6) [6,40,80,36,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28843
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28844 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(3,5),(4,6)], upper := (rows 7 42 84 73 49 422 454 390 390), lower := (rows 7 42 84 73 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 33 65 129 257), good := (rows 486 42 84 490 500 32 64 128 256) }] }

theorem u28844 : Upper (D 6) (R 6) [6,40,80,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28844
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28845 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 84 73 50 421 453 389 389), lower := (rows 7 42 84 73 50 32 64 128 256), losses := [] }

theorem u28845 : Upper (D 6) (R 6) [6,40,80,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28845
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28846 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 490, targets := 4 },{ cop := 0, region := 456, targets := 32 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 7 42 84 73 52 419 451 387 387), lower := (rows 7 42 84 73 52 32 64 128 256), losses := [] }

theorem u28846 : Upper (D 6) (R 6) [6,40,80,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28846
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28847 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(2,0),(4,6)], upper := (rows 7 42 84 73 145 294 358 422 294), lower := (rows 7 42 84 73 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 33 65 129 257), good := (rows 486 42 84 490 500 32 64 128 256) }] }

theorem u28847 : Upper (D 6) (R 6) [6,40,80,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28847
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28848 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 360, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 7 42 84 73 146 293 357 421 293), lower := (rows 7 42 84 73 146 32 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 25 33 0 129 257), good := (rows 439 58 20 443 146 32 0 128 256) }] }

theorem u28848 : Upper (D 6) (R 6) [6,40,80,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28848
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28849 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,2),(3,2),(4,6)], upper := (rows 7 42 84 73 148 291 355 419 291), lower := (rows 7 42 84 73 148 32 64 128 256), losses := [] }

theorem u28849 : Upper (D 6) (R 6) [6,40,80,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28849
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28850 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 328, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,6),(3,5),(4,6)], upper := (rows 7 42 84 73 176 295 327 391 263), lower := (rows 7 42 84 73 176 32 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 25 33 0 129 257), good := (rows 439 58 20 443 176 32 0 128 256) }] }

theorem u28850 : Upper (D 6) (R 6) [6,40,80,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28850
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28851 : Route 9 := (fun mask => (mask,id))

def c28851 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28851 : Upper (D 6) (R 6) [6,40,80,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,384] 13 (by decide) (choices 1) [1,2,4] r28851 c28851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10148
  · exact u10149
  · exact u10150

def b28852 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 84 74 145 293 357 421 293), lower := (rows 7 42 84 74 145 32 64 128 256), losses := [] }

theorem u28852 : Upper (D 6) (R 6) [6,40,80,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28852
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28853 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 84 74 148 289 353 417 289), lower := (rows 7 42 84 74 148 32 64 128 256), losses := [] }

theorem u28853 : Upper (D 6) (R 6) [6,40,80,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28853
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28854 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 328, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 84 74 176 293 325 389 261), lower := (rows 7 42 84 74 176 32 64 128 256), losses := [] }

theorem u28854 : Upper (D 6) (R 6) [6,40,80,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28854
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28855 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 84 74 400 37 101 165 293), lower := (rows 7 42 84 74 400 32 64 128 256), losses := [] }

theorem u28855 : Upper (D 6) (R 6) [6,40,80,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28855
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28856 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 42 84 76 145 291 355 419 291), lower := (rows 7 42 84 76 145 32 64 128 256), losses := [] }

theorem u28856 : Upper (D 6) (R 6) [6,40,80,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28856
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28857 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 42 84 76 146 289 353 417 289), lower := (rows 7 42 84 76 146 32 64 128 256), losses := [] }

theorem u28857 : Upper (D 6) (R 6) [6,40,80,68,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28857
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28858 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 42 84 76 176 291 323 387 259), lower := (rows 7 42 84 76 176 32 64 128 256), losses := [] }

theorem u28858 : Upper (D 6) (R 6) [6,40,80,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28858
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28859 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 42 84 76 400 35 99 163 291), lower := (rows 7 42 84 76 400 32 64 128 256), losses := [] }

theorem u28859 : Upper (D 6) (R 6) [6,40,80,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28859
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28859
end Delivery.IrregularNine14.P06
