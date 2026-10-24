import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5880 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 6, region := 176, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 259 14 28 112 160 65 192 448), lower := (rows 35 259 14 28 112 160 65 128 256), losses := [] }

theorem u5880 : Upper (D 7) (R 7) [34,257,10,20,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5881 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 14 28 112 160 192 193 321), lower := (rows 35 259 14 28 112 160 192 128 256), losses := [] }

theorem u5881 : Upper (D 7) (R 7) [34,257,10,20,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5882 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 14 56 81 160 68 192 448), lower := (rows 35 259 14 56 81 160 68 128 256), losses := [] }

theorem u5882 : Upper (D 7) (R 7) [34,257,10,48,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5882 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5883 : PairBound 9 := { available := 68, camps := [], pairs := [(3,0),(3,1),(4,1),(4,5)], upper := (rows 35 259 14 56 81 160 192 196 324), lower := (rows 35 259 14 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 228 228 132 260), good := (rows 98 258 494 120 120 224 224 224 256) },{ target := 1, region := (rows 1 0 4 25 17 228 228 132 260), good := (rows 121 281 492 120 121 224 224 224 256) },{ target := 5, region := (rows 1 2 4 8 17 0 228 132 260), good := (rows 83 275 462 88 81 192 192 192 256) }] }

theorem u5883 : Upper (D 7) (R 7) [34,257,10,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5884 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 14 73 52 160 80 192 448), lower := (rows 35 259 14 73 52 160 80 128 256), losses := [] }

theorem u5884 : Upper (D 7) (R 7) [34,257,10,65,36,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5884 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5885 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 240, targets := 3 }], pairs := [(2,5),(3,1),(4,0),(4,1)], upper := (rows 35 259 14 73 52 160 192 208 336), lower := (rows 35 259 14 73 52 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 20 244 244 148 276), good := (rows 105 265 508 105 500 224 224 224 256) },{ target := 5, region := (rows 1 2 7 9 16 0 240 144 272), good := (rows 79 271 14 77 468 192 192 192 256) }] }

theorem u5885 : Upper (D 7) (R 7) [34,257,10,65,36,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5886 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 259 14 73 112 160 68 144 400), lower := (rows 35 259 14 73 112 160 68 128 256), losses := [] }

theorem u5886 : Upper (D 7) (R 7) [34,257,10,65,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5886 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5887 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 14 73 112 160 80 132 388), lower := (rows 35 259 14 73 112 160 80 128 256), losses := [] }

theorem u5887 : Upper (D 7) (R 7) [34,257,10,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5887 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5888 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 14 73 112 160 192 148 276), lower := (rows 35 259 14 73 112 160 192 128 256), losses := [] }

theorem u5888 : Upper (D 7) (R 7) [34,257,10,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5889 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 259 14 73 148 96 80 160 416), lower := (rows 35 259 14 73 148 96 80 128 256), losses := [] }

theorem u5889 : Upper (D 7) (R 7) [34,257,10,65,132,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5889 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5890 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 406, targets := 96 }], pairs := [(1,5),(1,6),(2,5),(2,6)], upper := (rows 35 259 14 73 148 96 96 144 400), lower := (rows 35 259 14 73 148 96 96 128 256), losses := [] }

theorem u5890 : Upper (D 7) (R 7) [34,257,10,65,132,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5891 : Route 9 := (fun mask => (mask,id))

def c5891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5891 : Upper (D 7) (R 7) [34,257,10,65,132,64,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,132,64,128] 13 (by decide) (choices 1) [16,32] r5891 c5891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u432
  · exact u433

def r5892 : Route 9 := (fun mask => (mask,id))

def c5892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5892 : Upper (D 7) (R 7) [34,257,10,65,132,128,16] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,132,128,16] 13 (by decide) (choices 1) [32,64] r5892 c5892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u434
  · exact u435

def b5893 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(1,5),(2,5),(2,7),(4,5)], upper := (rows 35 259 14 73 148 160 96 208 336), lower := (rows 35 259 14 73 148 160 96 128 256), losses := [] }

theorem u5893 : Upper (D 7) (R 7) [34,257,10,65,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5894 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 111, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 14 73 176 96 68 144 400), lower := (rows 35 259 14 73 176 96 68 128 256), losses := [] }

theorem u5894 : Upper (D 7) (R 7) [34,257,10,65,160,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5894 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5895 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 259 14 73 176 96 80 132 388), lower := (rows 35 259 14 73 176 96 80 128 256), losses := [] }

theorem u5895 : Upper (D 7) (R 7) [34,257,10,65,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5895 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5896 : Route 9 := (fun mask => (mask,id))

def c5896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5896 : Upper (D 7) (R 7) [34,257,10,65,160,64,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,65,160,64,128] 13 (by decide) (choices 1) [4,16] r5896 c5896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u436
  · exact u437

def b5897 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 35 259 14 73 208 48 68 160 416), lower := (rows 35 259 14 73 208 48 68 128 256), losses := [] }

theorem u5897 : Upper (D 7) (R 7) [34,257,10,65,192,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5897 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5898 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 259 14 73 208 48 96 132 388), lower := (rows 35 259 14 73 208 48 96 128 256), losses := [] }

theorem u5898 : Upper (D 7) (R 7) [34,257,10,65,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5898 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5899 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 14 73 208 48 192 164 292), lower := (rows 35 259 14 73 208 48 192 128 256), losses := [] }

theorem u5899 : Upper (D 7) (R 7) [34,257,10,65,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5899 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5900 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 259 14 73 208 160 68 176 304), lower := (rows 35 259 14 73 208 160 68 128 256), losses := [] }

theorem u5900 : Upper (D 7) (R 7) [34,257,10,65,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5900 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5901 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 259 14 73 208 160 80 164 292), lower := (rows 35 259 14 73 208 160 80 128 256), losses := [] }

theorem u5901 : Upper (D 7) (R 7) [34,257,10,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5901 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5902 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(1,5),(2,5),(2,7),(4,5)], upper := (rows 35 259 14 73 208 160 96 148 276), lower := (rows 35 259 14 73 208 160 96 128 256), losses := [] }

theorem u5902 : Upper (D 7) (R 7) [34,257,10,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5903 : Route 9 := (fun mask => (mask,id))

def c5903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5903 : Upper (D 7) (R 7) [34,257,10,68,129,128,16] 13 := by
  apply FastRouting.sound _ _ [34,257,10,68,129,128,16] 13 (by decide) (choices 1) [32,64] r5903 c5903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u438
  · exact u439

def b5904 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,0),(2,7),(3,0),(3,7)], upper := (rows 35 259 14 76 145 160 96 208 336), lower := (rows 35 259 14 76 145 160 96 128 256), losses := [] }

theorem u5904 : Upper (D 7) (R 7) [34,257,10,68,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5905 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 259 14 88 52 160 65 192 448), lower := (rows 35 259 14 88 52 160 65 128 256), losses := [] }

theorem u5905 : Upper (D 7) (R 7) [34,257,10,80,36,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5906 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 259 14 88 52 160 192 193 321), lower := (rows 35 259 14 88 52 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 7 25 17 224 224 128 256), good := (rows 126 286 14 120 124 224 224 224 256) }] }

theorem u5906 : Upper (D 7) (R 7) [34,257,10,80,36,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5907 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 14 88 145 96 68 160 416), lower := (rows 35 259 14 88 145 96 68 128 256), losses := [] }

theorem u5907 : Upper (D 7) (R 7) [34,257,10,80,129,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5907 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5908 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 104, targets := 131 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7),(3,0),(3,1),(3,7)], upper := (rows 35 259 14 88 145 96 96 132 388), lower := (rows 35 259 14 88 145 96 96 128 256), losses := [] }

theorem u5908 : Upper (D 7) (R 7) [34,257,10,80,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5909 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 259 14 88 145 96 192 164 292), lower := (rows 35 259 14 88 145 96 192 128 256), losses := [] }

theorem u5909 : Upper (D 7) (R 7) [34,257,10,80,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5910 : Route 9 := (fun mask => (mask,id))

def c5910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5910 : Upper (D 7) (R 7) [34,257,10,80,129,128,4] 13 := by
  apply FastRouting.sound _ _ [34,257,10,80,129,128,4] 13 (by decide) (choices 1) [32,64] r5910 c5910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u440
  · exact u441

def b5911 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(1,7),(2,7),(3,0),(3,1)], upper := (rows 35 259 14 88 145 160 96 196 324), lower := (rows 35 259 14 88 145 160 96 128 256), losses := [{ target := 7, region := (rows 1 18 28 24 16 32 97 0 280), good := (rows 99 323 270 350 351 96 96 0 256) }] }

theorem u5911 : Upper (D 7) (R 7) [34,257,10,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5912 : PairBound 9 := { available := 132, camps := [{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,0)], upper := (rows 35 259 14 88 176 96 65 132 388), lower := (rows 35 259 14 88 176 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 5 104 125 104 64 199 327), good := (rows 446 406 446 504 184 504 508 128 256) }] }

theorem u5912 : Upper (D 7) (R 7) [34,257,10,80,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5913 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 14 88 176 96 68 129 385), lower := (rows 35 259 14 88 176 96 68 128 256), losses := [] }

theorem u5913 : Upper (D 7) (R 7) [34,257,10,80,160,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5913 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5914 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 14 88 176 96 192 133 261), lower := (rows 35 259 14 88 176 96 192 128 256), losses := [] }

theorem u5914 : Upper (D 7) (R 7) [34,257,10,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5915 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 14 104 81 160 68 144 400), lower := (rows 35 259 14 104 81 160 68 128 256), losses := [] }

theorem u5915 : Upper (D 7) (R 7) [34,257,10,96,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5915 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5916 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 14 104 81 160 80 132 388), lower := (rows 35 259 14 104 81 160 80 128 256), losses := [] }

theorem u5916 : Upper (D 7) (R 7) [34,257,10,96,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5916 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5917 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 259 14 104 81 160 192 148 276), lower := (rows 35 259 14 104 81 160 192 128 256), losses := [] }

theorem u5917 : Upper (D 7) (R 7) [34,257,10,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5918 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 168, targets := 1 }], pairs := [(2,7),(3,0),(3,7),(4,7)], upper := (rows 35 259 14 104 84 160 65 144 400), lower := (rows 35 259 14 104 84 160 65 128 256), losses := [] }

theorem u5918 : Upper (D 7) (R 7) [34,257,10,96,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5919 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 259 14 104 84 160 80 129 385), lower := (rows 35 259 14 104 84 160 80 128 256), losses := [] }

theorem u5919 : Upper (D 7) (R 7) [34,257,10,96,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5919 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5920 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 259 14 104 84 160 192 145 273), lower := (rows 35 259 14 104 84 160 192 128 256), losses := [] }

theorem u5920 : Upper (D 7) (R 7) [34,257,10,96,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5921 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 259 14 104 145 48 68 192 448), lower := (rows 35 259 14 104 145 48 68 128 256), losses := [] }

theorem u5921 : Upper (D 7) (R 7) [34,257,10,96,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5921 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5922 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 14 104 145 48 192 196 324), lower := (rows 35 259 14 104 145 48 192 128 256), losses := [] }

theorem u5922 : Upper (D 7) (R 7) [34,257,10,96,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5922 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5923 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,0),(2,7),(3,0)], upper := (rows 35 259 14 104 145 160 68 208 336), lower := (rows 35 259 14 104 145 160 68 128 256), losses := [] }

theorem u5923 : Upper (D 7) (R 7) [34,257,10,96,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5923 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5924 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 14 104 145 160 80 196 324), lower := (rows 35 259 14 104 145 160 80 128 256), losses := [] }

theorem u5924 : Upper (D 7) (R 7) [34,257,10,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5924 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5925 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 0, region := 72, targets := 2 }], pairs := [(2,7),(3,1),(3,7),(4,1)], upper := (rows 35 259 14 104 148 160 65 208 336), lower := (rows 35 259 14 104 148 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 13 20 180 67 132 260), good := (rows 105 329 508 104 444 160 73 160 256) }] }

theorem u5925 : Upper (D 7) (R 7) [34,257,10,96,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5926 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 14 104 148 160 80 193 321), lower := (rows 35 259 14 104 148 160 80 128 256), losses := [] }

theorem u5926 : Upper (D 7) (R 7) [34,257,10,96,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5926 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5927 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 4, region := 40, targets := 3 }], pairs := [(2,7),(3,0),(3,1),(3,7)], upper := (rows 35 259 14 104 208 160 65 148 276), lower := (rows 35 259 14 104 208 160 65 128 256), losses := [] }

theorem u5927 : Upper (D 7) (R 7) [34,257,10,96,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5928 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,0),(2,7),(3,0)], upper := (rows 35 259 14 104 208 160 68 145 273), lower := (rows 35 259 14 104 208 160 68 128 256), losses := [] }

theorem u5928 : Upper (D 7) (R 7) [34,257,10,96,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5928 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5929 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 14 104 208 160 80 133 261), lower := (rows 35 259 14 104 208 160 80 128 256), losses := [] }

theorem u5929 : Upper (D 7) (R 7) [34,257,10,96,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5929 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5930 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 259 14 200 81 48 68 160 416), lower := (rows 35 259 14 200 81 48 68 128 256), losses := [] }

theorem u5930 : Upper (D 7) (R 7) [34,257,10,192,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5930 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5931 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 14 200 81 48 96 132 388), lower := (rows 35 259 14 200 81 48 96 128 256), losses := [] }

theorem u5931 : Upper (D 7) (R 7) [34,257,10,192,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5931 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5932 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 14 200 81 48 192 164 292), lower := (rows 35 259 14 200 81 48 192 128 256), losses := [] }

theorem u5932 : Upper (D 7) (R 7) [34,257,10,192,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5932 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5933 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 168, targets := 3 },{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 35 259 14 200 81 160 68 176 304), lower := (rows 35 259 14 200 81 160 68 128 256), losses := [] }

theorem u5933 : Upper (D 7) (R 7) [34,257,10,192,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5933 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5934 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 35 259 14 200 81 160 80 164 292), lower := (rows 35 259 14 200 81 160 80 128 256), losses := [] }

theorem u5934 : Upper (D 7) (R 7) [34,257,10,192,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5934 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5935 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 259 14 200 81 160 96 148 276), lower := (rows 35 259 14 200 81 160 96 128 256), losses := [] }

theorem u5935 : Upper (D 7) (R 7) [34,257,10,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5936 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 168, targets := 3 },{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(3,1)], upper := (rows 35 259 14 200 84 160 65 176 304), lower := (rows 35 259 14 200 84 160 65 128 256), losses := [] }

theorem u5936 : Upper (D 7) (R 7) [34,257,10,192,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5937 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 259 14 200 84 160 80 161 289), lower := (rows 35 259 14 200 84 160 80 128 256), losses := [] }

theorem u5937 : Upper (D 7) (R 7) [34,257,10,192,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5937 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5938 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 419, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(1,6),(3,0),(3,1)], upper := (rows 35 259 14 200 84 160 96 145 273), lower := (rows 35 259 14 200 84 160 96 128 256), losses := [] }

theorem u5938 : Upper (D 7) (R 7) [34,257,10,192,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5939 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 3, region := 48, targets := 1 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 35 259 14 200 112 160 65 148 276), lower := (rows 35 259 14 200 112 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 29 172 67 132 260), good := (rows 113 337 508 248 112 160 81 160 256) }] }

theorem u5939 : Upper (D 7) (R 7) [34,257,10,192,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5939
end Delivery.IrregularNine14.P07
