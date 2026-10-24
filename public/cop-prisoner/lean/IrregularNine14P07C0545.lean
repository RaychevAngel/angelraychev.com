import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0268
import IrregularNine14P07C0269
import IrregularNine14P07C0270

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32700 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 205, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 7 200 304 227 195 195 451), lower := (rows 13 50 7 200 304 32 64 128 256), losses := [] }

theorem u32700 : Upper (D 7) (R 7) [12,48,3,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32701 : Route 9 := (fun mask => (mask,id))

def c32701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32701 : Upper (D 7) (R 7) [12,48,3,192,320] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,320] 13 (by decide) (choices 1) [1,2,128] r32701 c32701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16110
  · exact u16111
  · exact u16112

def b32702 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 18, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 7 265 50 224 192 192 448), lower := (rows 13 50 7 265 50 32 64 128 256), losses := [] }

theorem u32702 : Upper (D 7) (R 7) [12,48,3,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32703 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(1,0),(3,1),(4,0)], upper := (rows 13 50 7 265 82 224 224 224 480), lower := (rows 13 50 7 265 82 32 64 128 256), losses := [] }

theorem u32703 : Upper (D 7) (R 7) [12,48,3,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32704 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 7 265 112 226 194 194 450), lower := (rows 13 50 7 265 112 32 64 128 256), losses := [] }

theorem u32704 : Upper (D 7) (R 7) [12,48,3,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32705 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32705 : Upper (D 7) (R 7) [12,48,3,257,192] 13 := by
  apply FastRouting.sound _ _ [12,48,3,257,192] 13 (by decide) (choices 1) [2,64] r32705 c32705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16113
  · exact u16114

def b32706 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 23, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 13 50 7 296 19 224 192 192 448), lower := (rows 13 50 7 296 19 32 64 128 256), losses := [] }

theorem u32706 : Upper (D 7) (R 7) [12,48,3,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32707 : Route 9 := (fun mask => (mask,id))

def c32707 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32707 : Upper (D 7) (R 7) [12,48,3,288,65] 13 := by
  apply FastRouting.sound _ _ [12,48,3,288,65] 13 (by decide) (choices 1) [2,64,128] r32707 c32707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16115
  · exact u16116
  · exact u16117

def r32708 : Route 9 := (fun mask => (mask,id))

def c32708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32708 : Upper (D 7) (R 7) [12,48,3,288,66] 13 := by
  apply FastRouting.sound _ _ [12,48,3,288,66] 13 (by decide) (choices 1) [1,64,128] r32708 c32708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16118
  · exact u16119
  · exact u16120

def r32709 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32709 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32709 : Upper (D 7) (R 7) [12,48,3,288,192] 13 := by
  apply FastRouting.sound _ _ [12,48,3,288,192] 13 (by decide) (choices 1) [1,2,64] r32709 c32709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16121
  · exact u16122
  · exact u16123

def b32710 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 50 7 328 19 224 224 224 480), lower := (rows 13 50 7 328 19 32 64 128 256), losses := [] }

theorem u32710 : Upper (D 7) (R 7) [12,48,3,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32711 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 6, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 50 7 328 49 226 194 194 450), lower := (rows 13 50 7 328 49 32 64 128 256), losses := [] }

theorem u32711 : Upper (D 7) (R 7) [12,48,3,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32712 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 7 328 50 225 193 193 449), lower := (rows 13 50 7 328 50 32 64 128 256), losses := [] }

theorem u32712 : Upper (D 7) (R 7) [12,48,3,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32713 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 50 7 328 81 162 226 162 418), lower := (rows 13 50 7 328 81 32 64 128 256), losses := [] }

theorem u32713 : Upper (D 7) (R 7) [12,48,3,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32714 : Route 9 := (fun mask => (mask,id))

def c32714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32714 : Upper (D 7) (R 7) [12,48,3,320,66] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,66] 13 (by decide) (choices 1) [1,128] r32714 c32714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16124
  · exact u16125

def b32715 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 7 328 112 163 195 131 387), lower := (rows 13 50 7 328 112 32 64 128 256), losses := [] }

theorem u32715 : Upper (D 7) (R 7) [12,48,3,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32716 : Route 9 := (fun mask => (mask,id))

def c32716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32716 : Upper (D 7) (R 7) [12,48,3,320,129] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,129] 13 (by decide) (choices 1) [2,64,128] r32716 c32716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16126
  · exact u16127
  · exact u16128

def r32717 : Route 9 := (fun mask => (mask,id))

def c32717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32717 : Upper (D 7) (R 7) [12,48,3,320,130] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,130] 13 (by decide) (choices 1) [1,64,128] r32717 c32717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16129
  · exact u16130
  · exact u16131

def b32718 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 7 328 176 227 195 195 451), lower := (rows 13 50 7 328 176 32 64 128 256), losses := [] }

theorem u32718 : Upper (D 7) (R 7) [12,48,3,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32719 : Route 9 := (fun mask => (mask,id))

def c32719 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32719 : Upper (D 7) (R 7) [12,48,3,320,192] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,192] 13 (by decide) (choices 1) [1,2,128] r32719 c32719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16132
  · exact u16133
  · exact u16134

def b32720 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 464, targets := 32 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 13 50 37 73 82 418 450 386 386), lower := (rows 13 50 37 73 82 32 64 128 256), losses := [] }

theorem u32720 : Upper (D 7) (R 7) [12,48,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32721 : Route 9 := (fun mask => (mask,id))

def c32721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32721 : Upper (D 7) (R 7) [12,48,33,65,130] 13 := by
  apply FastRouting.sound _ _ [12,48,33,65,130] 13 (by decide) (choices 1) [2,64,128,256] r32721 c32721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16135
  · exact u16136
  · exact u16137
  · exact u16138

def b32722 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 464, targets := 32 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 13 50 37 73 208 418 450 386 386), lower := (rows 13 50 37 73 208 32 64 128 256), losses := [] }

theorem u32722 : Upper (D 7) (R 7) [12,48,33,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32723 : Route 9 := (fun mask => (mask,id))

def c32723 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32723 : Upper (D 7) (R 7) [12,48,33,65,258] 13 := by
  apply FastRouting.sound _ _ [12,48,33,65,258] 13 (by decide) (choices 1) [2,64,128] r32723 c32723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16139
  · exact u16140
  · exact u16141

def b32724 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 464, targets := 32 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 13 50 37 73 336 162 194 130 386), lower := (rows 13 50 37 73 336 32 64 128 256), losses := [] }

theorem u32724 : Upper (D 7) (R 7) [12,48,33,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32725 : Route 9 := (fun mask => (mask,id))

def c32725 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32725 : Upper (D 7) (R 7) [12,48,33,65,384] 13 := by
  apply FastRouting.sound _ _ [12,48,33,65,384] 13 (by decide) (choices 1) [2,64,128] r32725 c32725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16142
  · exact u16143
  · exact u16144

def b32726 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 18, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 37 74 19 480 448 448 448), lower := (rows 13 50 37 74 19 32 64 128 256), losses := [] }

theorem u32726 : Upper (D 7) (R 7) [12,48,33,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32727 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 13 50 37 74 81 418 450 386 386), lower := (rows 13 50 37 74 81 32 64 128 256), losses := [] }

theorem u32727 : Upper (D 7) (R 7) [12,48,33,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32728 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 13 50 37 74 82 417 449 385 385), lower := (rows 13 50 37 74 82 32 64 128 256), losses := [] }

theorem u32728 : Upper (D 7) (R 7) [12,48,33,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32729 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,5)], upper := (rows 13 50 37 74 145 482 450 450 450), lower := (rows 13 50 37 74 145 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 17 0 74 138 266), good := (rows 477 474 21 458 145 0 64 128 256) }] }

theorem u32729 : Upper (D 7) (R 7) [12,48,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32730 : Route 9 := (fun mask => (mask,id))

def c32730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32730 : Upper (D 7) (R 7) [12,48,33,66,130] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66,130] 13 (by decide) (choices 1) [1,64,128,256] r32730 c32730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16145
  · exact u16146
  · exact u16147
  · exact u16148

def r32731 : Route 9 := (fun mask => (mask,id))

def c32731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32731 : Upper (D 7) (R 7) [12,48,33,66,192] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66,192] 13 (by decide) (choices 1) [1,2,128,256] r32731 c32731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16149
  · exact u16150
  · exact u16151
  · exact u16152

def b32732 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 1, region := 200, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,5)], upper := (rows 13 50 37 74 273 226 194 194 450), lower := (rows 13 50 37 74 273 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 17 0 74 138 266), good := (rows 477 474 21 458 273 0 64 128 256) }] }

theorem u32732 : Upper (D 7) (R 7) [12,48,33,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32733 : Route 9 := (fun mask => (mask,id))

def c32733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32733 : Upper (D 7) (R 7) [12,48,33,66,258] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66,258] 13 (by decide) (choices 1) [1,64,128] r32733 c32733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16153
  · exact u16154
  · exact u16155

def r32734 : Route 9 := (fun mask => (mask,id))

def c32734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32734 : Upper (D 7) (R 7) [12,48,33,66,320] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66,320] 13 (by decide) (choices 1) [1,2,128] r32734 c32734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16156
  · exact u16157
  · exact u16158

def r32735 : Route 9 := (fun mask => (mask,id))

def c32735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32735 : Upper (D 7) (R 7) [12,48,33,66,384] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66,384] 13 (by decide) (choices 1) [1,2,64,128] r32735 c32735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16159
  · exact u16160
  · exact u16161
  · exact u16162

def b32736 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 18, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 37 200 19 482 450 450 450), lower := (rows 13 50 37 200 19 32 64 128 256), losses := [] }

theorem u32736 : Upper (D 7) (R 7) [12,48,33,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32737 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 50 37 200 81 418 450 386 386), lower := (rows 13 50 37 200 81 32 64 128 256), losses := [] }

theorem u32737 : Upper (D 7) (R 7) [12,48,33,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32738 : Route 9 := (fun mask => (mask,id))

def c32738 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32738 : Upper (D 7) (R 7) [12,48,33,192,66] 13 := by
  apply FastRouting.sound _ _ [12,48,33,192,66] 13 (by decide) (choices 1) [1,2,128,256] r32738 c32738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16163
  · exact u16164
  · exact u16165
  · exact u16166

def b32739 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 50 37 200 208 291 323 387 259), lower := (rows 13 50 37 200 208 32 64 128 256), losses := [] }

theorem u32739 : Upper (D 7) (R 7) [12,48,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32740 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32740 : Upper (D 7) (R 7) [12,48,33,192,257] 13 := by
  apply FastRouting.sound _ _ [12,48,33,192,257] 13 (by decide) (choices 1) [2,64] r32740 c32740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16167
  · exact u16168

def r32741 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32741 : Upper (D 7) (R 7) [12,48,33,192,258] 13 := by
  apply FastRouting.sound _ _ [12,48,33,192,258] 13 (by decide) (choices 1) [1,2,64] r32741 c32741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16169
  · exact u16170
  · exact u16171

def r32742 : Route 9 := (fun mask => (mask,id))

def c32742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32742 : Upper (D 7) (R 7) [12,48,33,192,320] 13 := by
  apply FastRouting.sound _ _ [12,48,33,192,320] 13 (by decide) (choices 1) [1,2,128] r32742 c32742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16172
  · exact u16173
  · exact u16174

def r32743 : Route 9 := (fun mask => (mask,id))

def c32743 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32743 : Upper (D 7) (R 7) [12,48,33,257,66] 13 := by
  apply FastRouting.sound _ _ [12,48,33,257,66] 13 (by decide) (choices 1) [2,64,128] r32743 c32743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16175
  · exact u16176
  · exact u16177

def r32744 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32744 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32744 : Upper (D 7) (R 7) [12,48,33,257,192] 13 := by
  apply FastRouting.sound _ _ [12,48,33,257,192] 13 (by decide) (choices 1) [2,64] r32744 c32744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16178
  · exact u16179

def b32745 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 18, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 37 266 19 224 192 192 448), lower := (rows 13 50 37 266 19 32 64 128 256), losses := [] }

theorem u32745 : Upper (D 7) (R 7) [12,48,33,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32746 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,5)], upper := (rows 13 50 37 266 81 226 194 194 450), lower := (rows 13 50 37 266 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 17 0 74 138 266), good := (rows 477 474 21 458 81 0 64 128 256) }] }

theorem u32746 : Upper (D 7) (R 7) [12,48,33,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32747 : Route 9 := (fun mask => (mask,id))

def c32747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32747 : Upper (D 7) (R 7) [12,48,33,258,66] 13 := by
  apply FastRouting.sound _ _ [12,48,33,258,66] 13 (by decide) (choices 1) [1,64,128] r32747 c32747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16180
  · exact u16181
  · exact u16182

def r32748 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32748 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32748 : Upper (D 7) (R 7) [12,48,33,258,192] 13 := by
  apply FastRouting.sound _ _ [12,48,33,258,192] 13 (by decide) (choices 1) [1,2,64] r32748 c32748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16183
  · exact u16184
  · exact u16185

def b32749 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 18, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 37 328 19 226 194 194 450), lower := (rows 13 50 37 328 19 32 64 128 256), losses := [] }

theorem u32749 : Upper (D 7) (R 7) [12,48,33,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32750 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 50 37 328 81 162 194 130 386), lower := (rows 13 50 37 328 81 32 64 128 256), losses := [] }

theorem u32750 : Upper (D 7) (R 7) [12,48,33,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32751 : Route 9 := (fun mask => (mask,id))

def c32751 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32751 : Upper (D 7) (R 7) [12,48,33,320,66] 13 := by
  apply FastRouting.sound _ _ [12,48,33,320,66] 13 (by decide) (choices 1) [1,2,128] r32751 c32751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16186
  · exact u16187
  · exact u16188

def r32752 : Route 9 := (fun mask => (mask,id))

def c32752 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32752 : Upper (D 7) (R 7) [12,48,33,320,129] 13 := by
  apply FastRouting.sound _ _ [12,48,33,320,129] 13 (by decide) (choices 1) [2,64,128] r32752 c32752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16189
  · exact u16190
  · exact u16191

def r32753 : Route 9 := (fun mask => (mask,id))

def c32753 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32753 : Upper (D 7) (R 7) [12,48,33,320,130] 13 := by
  apply FastRouting.sound _ _ [12,48,33,320,130] 13 (by decide) (choices 1) [1,2,64,128] r32753 c32753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16192
  · exact u16193
  · exact u16194
  · exact u16195

def r32754 : Route 9 := (fun mask => (mask,id))

def c32754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32754 : Upper (D 7) (R 7) [12,48,33,320,192] 13 := by
  apply FastRouting.sound _ _ [12,48,33,320,192] 13 (by decide) (choices 1) [1,2,128] r32754 c32754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16196
  · exact u16197
  · exact u16198

def b32755 : PairBound 9 := { available := 450, camps := [{ cop := 5, region := 18, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 69 137 50 482 450 450 450), lower := (rows 13 50 69 137 50 32 64 128 256), losses := [] }

theorem u32755 : Upper (D 7) (R 7) [12,48,65,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32756 : Route 9 := (fun mask => (mask,id))

def c32756 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32756 : Upper (D 7) (R 7) [12,48,65,129,66] 13 := by
  apply FastRouting.sound _ _ [12,48,65,129,66] 13 (by decide) (choices 1) [2,128,256] r32756 c32756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16199
  · exact u16200
  · exact u16201

def b32757 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 69 137 112 418 450 386 386), lower := (rows 13 50 69 137 112 32 64 128 256), losses := [] }

theorem u32757 : Upper (D 7) (R 7) [12,48,65,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32758 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 13, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 50 69 137 208 290 354 418 290), lower := (rows 13 50 69 137 208 32 64 128 256), losses := [] }

theorem u32758 : Upper (D 7) (R 7) [12,48,65,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m32759_128 : Upper (D 7) (R 7) [12,48,65,129,258,128] 13 :=
  permutation_upper _ _ _ [12,48,65,129,258,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16203

def r32759 : Route 9 := (fun mask => (mask,id))

def c32759 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32759 : Upper (D 7) (R 7) [12,48,65,129,258] 13 := by
  apply FastRouting.sound _ _ [12,48,65,129,258] 13 (by decide) (choices 1) [2,64,128] r32759 c32759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16202
  · exact u16203
  · exact m32759_128

#print axioms u32759
end Delivery.IrregularNine14.P07
