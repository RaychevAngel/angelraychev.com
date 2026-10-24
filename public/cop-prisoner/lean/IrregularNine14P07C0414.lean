import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0140

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24840 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 56 280 33 194 194 450), lower := (rows 37 194 7 56 280 33 64 128 256), losses := [] }

theorem u24840 : Upper (D 7) (R 7) [36,192,3,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24841 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 56 280 34 193 193 449), lower := (rows 37 194 7 56 280 34 64 128 256), losses := [] }

theorem u24841 : Upper (D 7) (R 7) [36,192,3,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24842 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(2,7)], upper := (rows 37 194 7 56 280 96 195 131 387), lower := (rows 37 194 7 56 280 96 64 128 256), losses := [] }

theorem u24842 : Upper (D 7) (R 7) [36,192,3,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24843 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 56 336 33 202 138 394), lower := (rows 37 194 7 56 336 33 64 128 256), losses := [] }

theorem u24843 : Upper (D 7) (R 7) [36,192,3,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24844 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 56 336 34 201 137 393), lower := (rows 37 194 7 56 336 34 64 128 256), losses := [] }

theorem u24844 : Upper (D 7) (R 7) [36,192,3,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24845 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 194 7 56 336 40 195 131 387), lower := (rows 37 194 7 56 336 40 64 128 256), losses := [] }

theorem u24845 : Upper (D 7) (R 7) [36,192,3,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24845 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24846 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,6),(3,7)], upper := (rows 37 194 7 56 336 160 75 139 267), lower := (rows 37 194 7 56 336 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 162 64 128 256), good := (rows 37 224 37 56 336 160 64 160 256) },{ target := 7, region := (rows 1 2 4 9 21 32 68 0 260), good := (rows 381 66 351 56 336 32 64 0 256) }] }

theorem u24846 : Upper (D 7) (R 7) [36,192,3,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24847 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 73 152 34 368 432 304), lower := (rows 37 194 7 73 152 34 64 128 256), losses := [] }

theorem u24847 : Upper (D 7) (R 7) [36,192,3,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24848 : Route 9 := (fun mask => (mask,id))

def c24848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u24848 : Upper (D 7) (R 7) [36,192,3,65,136,16] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,136,16] 13 (by decide) (choices 1) [2,32,256] r24848 c24848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8400
  · exact u8401
  · exact u8402

def r24849 : Route 9 := (fun mask => (mask,id))

def c24849 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24849 : Upper (D 7) (R 7) [36,192,3,65,136,256] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,136,256] 13 (by decide) (choices 1) [2,16,32] r24849 c24849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8403
  · exact u8404
  · exact u8405

def b24850 : PairBound 9 := { available := 280, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 73 176 34 344 408 280), lower := (rows 37 194 7 73 176 34 64 128 256), losses := [] }

theorem u24850 : Upper (D 7) (R 7) [36,192,3,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24851 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 73 176 40 338 402 274), lower := (rows 37 194 7 73 176 40 64 128 256), losses := [] }

theorem u24851 : Upper (D 7) (R 7) [36,192,3,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24851 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24852 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 7 73 176 48 330 394 266), lower := (rows 37 194 7 73 176 48 64 128 256), losses := [] }

theorem u24852 : Upper (D 7) (R 7) [36,192,3,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24852 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24853 : Route 9 := (fun mask => (mask,id))

def c24853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24853 : Upper (D 7) (R 7) [36,192,3,65,160,256] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,160,256] 13 (by decide) (choices 1) [2,8,16] r24853 c24853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8406
  · exact u8407
  · exact u8408

def b24854 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 73 274 40 240 176 432), lower := (rows 37 194 7 73 274 40 64 128 256), losses := [] }

theorem u24854 : Upper (D 7) (R 7) [36,192,3,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24854 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24855 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 194 7 73 274 48 232 168 424), lower := (rows 37 194 7 73 274 48 64 128 256), losses := [] }

theorem u24855 : Upper (D 7) (R 7) [36,192,3,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24855 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24856 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 194 7 73 274 160 120 184 312), lower := (rows 37 194 7 73 274 160 64 128 256), losses := [] }

theorem u24856 : Upper (D 7) (R 7) [36,192,3,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24857 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 73 280 34 240 176 432), lower := (rows 37 194 7 73 280 34 64 128 256), losses := [] }

theorem u24857 : Upper (D 7) (R 7) [36,192,3,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24858 : Route 9 := (fun mask => (mask,id))

def c24858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u24858 : Upper (D 7) (R 7) [36,192,3,65,264,16] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,264,16] 13 (by decide) (choices 1) [2,32,128] r24858 c24858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8409
  · exact u8410
  · exact u8411

def b24859 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 194 7 73 280 160 114 178 306), lower := (rows 37 194 7 73 280 160 64 128 256), losses := [] }

theorem u24859 : Upper (D 7) (R 7) [36,192,3,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24860 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 73 304 34 216 152 408), lower := (rows 37 194 7 73 304 34 64 128 256), losses := [] }

theorem u24860 : Upper (D 7) (R 7) [36,192,3,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24861 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 73 304 40 210 146 402), lower := (rows 37 194 7 73 304 40 64 128 256), losses := [] }

theorem u24861 : Upper (D 7) (R 7) [36,192,3,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24861 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24862 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 194 7 73 304 48 202 138 394), lower := (rows 37 194 7 73 304 48 64 128 256), losses := [] }

theorem u24862 : Upper (D 7) (R 7) [36,192,3,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24862 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24863 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 194 7 73 304 160 90 154 282), lower := (rows 37 194 7 73 304 160 64 128 256), losses := [] }

theorem u24863 : Upper (D 7) (R 7) [36,192,3,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24864 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 73 400 34 120 184 312), lower := (rows 37 194 7 73 400 34 64 128 256), losses := [] }

theorem u24864 : Upper (D 7) (R 7) [36,192,3,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24865 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 73 400 40 114 178 306), lower := (rows 37 194 7 73 400 40 64 128 256), losses := [] }

theorem u24865 : Upper (D 7) (R 7) [36,192,3,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24865 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24866 : Route 9 := (fun mask => (mask,id))

def c24866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24866 : Upper (D 7) (R 7) [36,192,3,65,384,16] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,384,16] 13 (by decide) (choices 1) [2,8,32] r24866 c24866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8412
  · exact u8413
  · exact u8414

def b24867 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 7 88 176 33 330 394 266), lower := (rows 37 194 7 88 176 33 64 128 256), losses := [] }

theorem u24867 : Upper (D 7) (R 7) [36,192,3,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24868 : PairBound 9 := { available := 265, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 88 176 34 329 393 265), lower := (rows 37 194 7 88 176 34 64 128 256), losses := [] }

theorem u24868 : Upper (D 7) (R 7) [36,192,3,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24869 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 56, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 37 194 7 88 176 40 323 387 259), lower := (rows 37 194 7 88 176 40 64 128 256), losses := [] }

theorem u24869 : Upper (D 7) (R 7) [36,192,3,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24869 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24870 : Route 9 := (fun mask => (mask,id))

def c24870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24870 : Upper (D 7) (R 7) [36,192,3,80,160,256] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,160,256] 13 (by decide) (choices 1) [1,2,8] r24870 c24870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8415
  · exact u8416
  · exact u8417

def b24871 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 88 273 34 232 168 424), lower := (rows 37 194 7 88 273 34 64 128 256), losses := [] }

theorem u24871 : Upper (D 7) (R 7) [36,192,3,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24872 : Route 9 := (fun mask => (mask,id))

def c24872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u24872 : Upper (D 7) (R 7) [36,192,3,80,257,8] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,257,8] 13 (by decide) (choices 1) [2,32,128] r24872 c24872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8418
  · exact u8419
  · exact u8420

def b24873 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 194 7 88 273 160 106 170 298), lower := (rows 37 194 7 88 273 160 64 128 256), losses := [] }

theorem u24873 : Upper (D 7) (R 7) [36,192,3,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24874 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 88 274 33 232 168 424), lower := (rows 37 194 7 88 274 33 64 128 256), losses := [] }

theorem u24874 : Upper (D 7) (R 7) [36,192,3,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24875 : Route 9 := (fun mask => (mask,id))

def c24875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u24875 : Upper (D 7) (R 7) [36,192,3,80,258,8] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,258,8] 13 (by decide) (choices 1) [1,32,128] r24875 c24875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8421
  · exact u8422
  · exact u8423

def b24876 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,6),(3,7)], upper := (rows 37 194 7 88 274 160 105 169 297), lower := (rows 37 194 7 88 274 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 162 64 128 256), good := (rows 37 224 37 88 304 160 64 160 256) },{ target := 7, region := (rows 1 2 4 13 20 32 65 0 257), good := (rows 381 66 351 88 274 32 64 0 256) }] }

theorem u24876 : Upper (D 7) (R 7) [36,192,3,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24877 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 474, targets := 1 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 194 7 88 280 33 226 162 418), lower := (rows 37 194 7 88 280 33 64 128 256), losses := [] }

theorem u24877 : Upper (D 7) (R 7) [36,192,3,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24878 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 37 194 7 88 280 34 225 161 417), lower := (rows 37 194 7 88 280 34 64 128 256), losses := [] }

theorem u24878 : Upper (D 7) (R 7) [36,192,3,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24879 : Route 9 := (fun mask => (mask,id))

def c24879 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24879 : Upper (D 7) (R 7) [36,192,3,80,264,128] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,264,128] 13 (by decide) (choices 1) [1,2,32] r24879 c24879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8424
  · exact u8425
  · exact u8426

def b24880 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 88 304 33 202 138 394), lower := (rows 37 194 7 88 304 33 64 128 256), losses := [] }

theorem u24880 : Upper (D 7) (R 7) [36,192,3,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24881 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 88 304 34 201 137 393), lower := (rows 37 194 7 88 304 34 64 128 256), losses := [] }

theorem u24881 : Upper (D 7) (R 7) [36,192,3,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24882 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(4,6)], upper := (rows 37 194 7 88 304 40 195 131 387), lower := (rows 37 194 7 88 304 40 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 17 40 0 132 260), good := (rows 437 130 407 56 304 40 0 128 256) }] }

theorem u24882 : Upper (D 7) (R 7) [36,192,3,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24882 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24883 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,6),(3,7)], upper := (rows 37 194 7 88 304 160 75 139 267), lower := (rows 37 194 7 88 304 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 162 64 128 256), good := (rows 37 224 37 88 304 160 64 160 256) },{ target := 7, region := (rows 1 2 4 13 17 32 68 0 260), good := (rows 381 66 351 88 304 32 64 0 256) }] }

theorem u24883 : Upper (D 7) (R 7) [36,192,3,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24884 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 88 400 33 106 170 298), lower := (rows 37 194 7 88 400 33 64 128 256), losses := [] }

theorem u24884 : Upper (D 7) (R 7) [36,192,3,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24885 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 88 400 34 105 169 297), lower := (rows 37 194 7 88 400 34 64 128 256), losses := [] }

theorem u24885 : Upper (D 7) (R 7) [36,192,3,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24886 : Route 9 := (fun mask => (mask,id))

def c24886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24886 : Upper (D 7) (R 7) [36,192,3,80,384,8] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,384,8] 13 (by decide) (choices 1) [1,2,32] r24886 c24886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8427
  · exact u8428
  · exact u8429

def b24887 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 104 273 34 216 152 408), lower := (rows 37 194 7 104 273 34 64 128 256), losses := [] }

theorem u24887 : Upper (D 7) (R 7) [36,192,3,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24888 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 7 104 273 40 210 146 402), lower := (rows 37 194 7 104 273 40 64 128 256), losses := [] }

theorem u24888 : Upper (D 7) (R 7) [36,192,3,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24888 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24889 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 3, region := 130, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 7 104 273 48 202 138 394), lower := (rows 37 194 7 104 273 48 64 128 256), losses := [] }

theorem u24889 : Upper (D 7) (R 7) [36,192,3,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24889 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24890 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 194 7 104 273 160 90 154 282), lower := (rows 37 194 7 104 273 160 64 128 256), losses := [] }

theorem u24890 : Upper (D 7) (R 7) [36,192,3,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24891 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 7 104 274 33 216 152 408), lower := (rows 37 194 7 104 274 33 64 128 256), losses := [] }

theorem u24891 : Upper (D 7) (R 7) [36,192,3,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24892 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 7 104 274 40 209 145 401), lower := (rows 37 194 7 104 274 40 64 128 256), losses := [] }

theorem u24892 : Upper (D 7) (R 7) [36,192,3,96,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24892 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24893 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 194 7 104 274 48 201 137 393), lower := (rows 37 194 7 104 274 48 64 128 256), losses := [] }

theorem u24893 : Upper (D 7) (R 7) [36,192,3,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24893 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24894 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 1, region := 40, targets := 1 },{ cop := 1, region := 40, targets := 2 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 37 194 7 104 274 160 89 153 281), lower := (rows 37 194 7 104 274 160 64 128 256), losses := [] }

theorem u24894 : Upper (D 7) (R 7) [36,192,3,96,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24895 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 7 104 280 33 210 146 402), lower := (rows 37 194 7 104 280 33 64 128 256), losses := [] }

theorem u24895 : Upper (D 7) (R 7) [36,192,3,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24896 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 104 280 34 209 145 401), lower := (rows 37 194 7 104 280 34 64 128 256), losses := [] }

theorem u24896 : Upper (D 7) (R 7) [36,192,3,96,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24897 : Route 9 := (fun mask => (mask,id))

def c24897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24897 : Upper (D 7) (R 7) [36,192,3,96,264,16] 13 := by
  apply FastRouting.sound _ _ [36,192,3,96,264,16] 13 (by decide) (choices 1) [1,2,128] r24897 c24897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8430
  · exact u8431
  · exact u8432

def b24898 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 1, region := 40, targets := 1 },{ cop := 1, region := 40, targets := 2 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 37 194 7 104 280 160 83 147 275), lower := (rows 37 194 7 104 280 160 64 128 256), losses := [] }

theorem u24898 : Upper (D 7) (R 7) [36,192,3,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24899 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 7 104 400 33 90 154 282), lower := (rows 37 194 7 104 400 33 64 128 256), losses := [] }

theorem u24899 : Upper (D 7) (R 7) [36,192,3,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24899
end Delivery.IrregularNine14.P07
