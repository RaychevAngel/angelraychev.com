import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0011

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3600 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 152 304 96 449 385 385), lower := (rows 35 7 76 152 304 96 64 128 256), losses := [] }

theorem u3600 : Upper (D 9) (R 9) [34,5,72,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3600 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3601 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(4,7)], upper := (rows 35 7 76 152 304 160 321 449 321), lower := (rows 35 7 76 152 304 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 35 7 47 184 304 160 0 160 256) },{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 35 7 111 184 48 160 64 160 0) }] }

theorem u3601 : Upper (D 9) (R 9) [34,5,72,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3601 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3602 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 7 76 152 304 288 193 193 449), lower := (rows 35 7 76 152 304 288 64 128 256), losses := [] }

theorem u3602 : Upper (D 9) (R 9) [34,5,72,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3602 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3603 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 7 76 152 336 33 480 416 416), lower := (rows 35 7 76 152 336 33 64 128 256), losses := [] }

theorem u3603 : Upper (D 9) (R 9) [34,5,72,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3603 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3604 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(4,7)], upper := (rows 35 7 76 152 336 160 353 417 289), lower := (rows 35 7 76 152 336 160 64 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 35 7 111 184 80 160 64 160 0) }] }

theorem u3604 : Upper (D 9) (R 9) [34,5,72,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3604 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3605 : Route 9 := (fun mask => (mask,id))

def c3605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3605 : Upper (D 9) (R 9) [34,5,72,144,320,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144,320,256] 13 (by decide) (choices 1) [1,32,128] r3605 c3605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u678
  · exact u679
  · exact u680

def b3606 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 76 168 81 48 448 384 384), lower := (rows 35 7 76 168 81 48 64 128 256), losses := [] }

theorem u3606 : Upper (D 9) (R 9) [34,5,72,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3606 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3607 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 7 76 168 81 160 336 400 272), lower := (rows 35 7 76 168 81 160 64 128 256), losses := [] }

theorem u3607 : Upper (D 9) (R 9) [34,5,72,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3607 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3608 : Route 9 := (fun mask => (mask,id))

def c3608 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u3608 : Upper (D 9) (R 9) [34,5,72,160,65,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,65,256] 13 (by decide) (choices 1) [16,128,256] r3608 c3608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u681
  · exact u682
  · exact u683

def b3609 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 0, region := 460, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 35 7 76 168 145 48 320 448 320), lower := (rows 35 7 76 168 145 48 64 128 256), losses := [] }

theorem u3609 : Upper (D 9) (R 9) [34,5,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3609 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3610 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 168 145 96 336 400 272), lower := (rows 35 7 76 168 145 96 64 128 256), losses := [] }

theorem u3610 : Upper (D 9) (R 9) [34,5,72,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3610 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3611 : Route 9 := (fun mask => (mask,id))

def c3611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3611 : Upper (D 9) (R 9) [34,5,72,160,129,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,129,256] 13 (by decide) (choices 1) [16,256] r3611 c3611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u684
  · exact u685

def b3612 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 76 168 208 33 336 400 272), lower := (rows 35 7 76 168 208 33 64 128 256), losses := [] }

theorem u3612 : Upper (D 9) (R 9) [34,5,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3612 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3613 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 76 168 208 48 321 385 257), lower := (rows 35 7 76 168 208 48 64 128 256), losses := [] }

theorem u3613 : Upper (D 9) (R 9) [34,5,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3613 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3614 : Route 9 := (fun mask => (mask,id))

def c3614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3614 : Upper (D 9) (R 9) [34,5,72,160,192,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,192,256] 13 (by decide) (choices 1) [1,16,256] r3614 c3614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u686
  · exact u687
  · exact u688

def b3615 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 460, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(3,0),(4,5)], upper := (rows 35 7 76 168 273 48 448 448 448), lower := (rows 35 7 76 168 273 48 64 128 256), losses := [] }

theorem u3615 : Upper (D 9) (R 9) [34,5,72,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3615 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3616 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 168 273 96 464 400 400), lower := (rows 35 7 76 168 273 96 64 128 256), losses := [] }

theorem u3616 : Upper (D 9) (R 9) [34,5,72,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3616 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3617 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 7 76 168 273 160 336 464 336), lower := (rows 35 7 76 168 273 160 64 128 256), losses := [] }

theorem u3617 : Upper (D 9) (R 9) [34,5,72,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3617 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3618 : Route 9 := (fun mask => (mask,id))

def c3618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3618 : Upper (D 9) (R 9) [34,5,72,160,257,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,257,256] 13 (by decide) (choices 1) [16,128] r3618 c3618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u689
  · exact u690

def b3619 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 76 168 336 33 464 400 400), lower := (rows 35 7 76 168 336 33 64 128 256), losses := [] }

theorem u3619 : Upper (D 9) (R 9) [34,5,72,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3619 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3620 : Route 9 := (fun mask => (mask,id))

def c3620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3620 : Upper (D 9) (R 9) [34,5,72,160,320,16] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,320,16] 13 (by decide) (choices 1) [1,128,256] r3620 c3620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u691
  · exact u692
  · exact u693

def b3621 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 7 76 168 336 160 337 401 273), lower := (rows 35 7 76 168 336 160 64 128 256), losses := [] }

theorem u3621 : Upper (D 9) (R 9) [34,5,72,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3621 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3622 : Route 9 := (fun mask => (mask,id))

def c3622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3622 : Upper (D 9) (R 9) [34,5,72,160,320,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,320,256] 13 (by decide) (choices 1) [1,16,128] r3622 c3622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u694
  · exact u695
  · exact u696

def b3623 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 76 168 400 33 336 464 336), lower := (rows 35 7 76 168 400 33 64 128 256), losses := [] }

theorem u3623 : Upper (D 9) (R 9) [34,5,72,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3623 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3624 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 7 76 168 400 48 321 449 321), lower := (rows 35 7 76 168 400 48 64 128 256), losses := [] }

theorem u3624 : Upper (D 9) (R 9) [34,5,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3624 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3625 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 168 400 96 337 401 273), lower := (rows 35 7 76 168 400 96 64 128 256), losses := [] }

theorem u3625 : Upper (D 9) (R 9) [34,5,72,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3625 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3626 : Route 9 := (fun mask => (mask,id))

def c3626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3626 : Upper (D 9) (R 9) [34,5,72,160,384,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,384,256] 13 (by decide) (choices 1) [1,16] r3626 c3626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u697
  · exact u698

def b3627 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 76 392 81 48 480 416 416), lower := (rows 35 7 76 392 81 48 64 128 256), losses := [] }

theorem u3627 : Upper (D 9) (R 9) [34,5,72,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3627 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3628 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 428, targets := 1 },{ cop := 0, region := 336, targets := 128 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(3,6),(4,7)], upper := (rows 35 7 76 392 81 160 368 432 304), lower := (rows 35 7 76 392 81 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 24 16 184 0 144 272), good := (rows 35 7 47 424 441 160 0 160 256) }] }

theorem u3628 : Upper (D 9) (R 9) [34,5,72,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3628 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3629 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 7 76 392 112 33 464 400 400), lower := (rows 35 7 76 392 112 33 64 128 256), losses := [] }

theorem u3629 : Upper (D 9) (R 9) [34,5,72,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3629 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3630 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 76 392 112 48 449 385 385), lower := (rows 35 7 76 392 112 48 64 128 256), losses := [] }

theorem u3630 : Upper (D 9) (R 9) [34,5,72,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3630 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3631 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(4,0),(4,7)], upper := (rows 35 7 76 392 112 160 337 401 273), lower := (rows 35 7 76 392 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 22 124 424 112 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 35 7 47 424 48 160 0 160 256) },{ target := 8, region := (rows 5 6 4 8 20 168 64 128 0), good := (rows 35 23 127 168 112 160 64 160 0) }] }

theorem u3631 : Upper (D 9) (R 9) [34,5,72,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3631 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3632 : Route 9 := (fun mask => (mask,id))

def c3632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3632 : Upper (D 9) (R 9) [34,5,72,384,129,16] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,129,16] 13 (by decide) (choices 1) [32,256] r3632 c3632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u699
  · exact u700

def b3633 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 392 145 96 368 432 304), lower := (rows 35 7 76 392 145 96 64 128 256), losses := [] }

theorem u3633 : Upper (D 9) (R 9) [34,5,72,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3633 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3634 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 0, region := 208, targets := 256 }], pairs := [(0,6),(1,6),(2,0),(3,0),(4,8)], upper := (rows 35 7 76 392 145 288 112 240 368), lower := (rows 35 7 76 392 145 288 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 296 0 128 256), good := (rows 35 7 47 424 145 288 0 128 288) }] }

theorem u3634 : Upper (D 9) (R 9) [34,5,72,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3634 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3635 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 76 392 176 33 336 464 336), lower := (rows 35 7 76 392 176 33 64 128 256), losses := [] }

theorem u3635 : Upper (D 9) (R 9) [34,5,72,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3635 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3636 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 7 76 392 176 48 321 449 321), lower := (rows 35 7 76 392 176 48 64 128 256), losses := [] }

theorem u3636 : Upper (D 9) (R 9) [34,5,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3636 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3637 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 392 176 96 337 401 273), lower := (rows 35 7 76 392 176 96 64 128 256), losses := [] }

theorem u3637 : Upper (D 9) (R 9) [34,5,72,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3637 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3638 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 0, region := 208, targets := 256 }], pairs := [(0,6),(1,6),(4,0),(4,6),(4,8)], upper := (rows 35 7 76 392 176 288 81 209 337), lower := (rows 35 7 76 392 176 288 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 24 296 0 128 256), good := (rows 35 7 63 440 176 288 0 128 288) }] }

theorem u3638 : Upper (D 9) (R 9) [34,5,72,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3638 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3639 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 76 392 208 33 368 432 304), lower := (rows 35 7 76 392 208 33 64 128 256), losses := [] }

theorem u3639 : Upper (D 9) (R 9) [34,5,72,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3639 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3640 : Route 9 := (fun mask => (mask,id))

def c3640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3640 : Upper (D 9) (R 9) [34,5,72,384,192,16] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,192,16] 13 (by decide) (choices 1) [1,32,256] r3640 c3640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u701
  · exact u702
  · exact u703

def b3641 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 208, targets := 256 }], pairs := [(0,6),(0,7),(1,6),(1,7),(4,8)], upper := (rows 35 7 76 392 208 288 113 177 305), lower := (rows 35 7 76 392 208 288 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 296 0 128 256), good := (rows 35 7 47 424 144 288 0 128 288) },{ target := 7, region := (rows 5 6 4 8 16 296 64 0 256), good := (rows 35 7 111 296 80 288 64 0 288) }] }

theorem u3641 : Upper (D 9) (R 9) [34,5,72,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3641 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3642 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,8)], upper := (rows 35 7 196 25 88 160 352 416 288), lower := (rows 35 7 196 25 88 160 64 128 256), losses := [] }

theorem u3642 : Upper (D 9) (R 9) [34,5,192,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3642 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3643 : Route 9 := (fun mask => (mask,id))

def c3643 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3643 : Upper (D 9) (R 9) [34,5,192,17,72,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,72,256] 13 (by decide) (choices 1) [32,128,256] r3643 c3643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u704
  · exact u705
  · exact u706

def b3644 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 59, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 196 25 112 40 448 384 384), lower := (rows 35 7 196 25 112 40 64 128 256), losses := [] }

theorem u3644 : Upper (D 9) (R 9) [34,5,192,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3644 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3645 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,8)], upper := (rows 35 7 196 25 112 160 328 392 264), lower := (rows 35 7 196 25 112 160 64 128 256), losses := [] }

theorem u3645 : Upper (D 9) (R 9) [34,5,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3645 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3646 : Route 9 := (fun mask => (mask,id))

def c3646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3646 : Upper (D 9) (R 9) [34,5,192,17,96,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,96,256] 13 (by decide) (choices 1) [8,128,256] r3646 c3646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u707
  · exact u708
  · exact u709

def b3647 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 196 25 280 96 480 416 416), lower := (rows 35 7 196 25 280 96 64 128 256), losses := [] }

theorem u3647 : Upper (D 9) (R 9) [34,5,192,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3647 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3648 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 3, region := 500, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(4,0)], upper := (rows 35 7 196 25 280 288 224 224 480), lower := (rows 35 7 196 25 280 288 64 128 256), losses := [] }

theorem u3648 : Upper (D 9) (R 9) [34,5,192,17,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3648 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3649 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,0),(2,5),(4,0)], upper := (rows 35 7 196 25 304 40 448 448 448), lower := (rows 35 7 196 25 304 40 64 128 256), losses := [] }

theorem u3649 : Upper (D 9) (R 9) [34,5,192,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3649 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3650 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 196 25 304 96 456 392 392), lower := (rows 35 7 196 25 304 96 64 128 256), losses := [] }

theorem u3650 : Upper (D 9) (R 9) [34,5,192,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3650 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3651 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 7 196 25 304 288 200 200 456), lower := (rows 35 7 196 25 304 288 64 128 256), losses := [] }

theorem u3651 : Upper (D 9) (R 9) [34,5,192,17,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3651 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3652 : Route 9 := (fun mask => (mask,id))

def c3652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3652 : Upper (D 9) (R 9) [34,5,192,17,320,8] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,320,8] 13 (by decide) (choices 1) [32,128,256] r3652 c3652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u710
  · exact u711
  · exact u712

def b3653 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 35 7 196 25 336 160 360 424 296), lower := (rows 35 7 196 25 336 160 64 128 256), losses := [] }

theorem u3653 : Upper (D 9) (R 9) [34,5,192,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3653 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3654 : Route 9 := (fun mask => (mask,id))

def c3654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3654 : Upper (D 9) (R 9) [34,5,192,17,320,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,320,256] 13 (by decide) (choices 1) [8,32,128] r3654 c3654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u713
  · exact u714
  · exact u715

def b3655 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 59, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 196 56 81 40 448 384 384), lower := (rows 35 7 196 56 81 40 64 128 256), losses := [] }

theorem u3655 : Upper (D 9) (R 9) [34,5,192,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3655 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3656 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,8)], upper := (rows 35 7 196 56 81 160 328 392 264), lower := (rows 35 7 196 56 81 160 64 128 256), losses := [] }

theorem u3656 : Upper (D 9) (R 9) [34,5,192,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3656 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3657 : Route 9 := (fun mask => (mask,id))

def c3657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3657 : Upper (D 9) (R 9) [34,5,192,48,65,256] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,65,256] 13 (by decide) (choices 1) [8,128,256] r3657 c3657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u716
  · exact u717
  · exact u718

def b3658 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 59, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 7 196 56 88 33 448 384 384), lower := (rows 35 7 196 56 88 33 64 128 256), losses := [] }

theorem u3658 : Upper (D 9) (R 9) [34,5,192,48,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3658 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3659 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 0, region := 454, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(3,8),(4,8)], upper := (rows 35 7 196 56 88 160 321 385 257), lower := (rows 35 7 196 56 88 160 64 128 256), losses := [] }

theorem u3659 : Upper (D 9) (R 9) [34,5,192,48,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3659 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3659
end Delivery.IrregularNine14.P09
