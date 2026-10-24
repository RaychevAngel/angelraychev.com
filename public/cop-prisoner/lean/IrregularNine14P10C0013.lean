import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0003

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b780 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 104 280 48 480 416 416), lower := (rows 35 70 133 104 280 48 64 128 256), losses := [] }

theorem u780 : Upper (D 10) (R 10) [34,68,129,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b780 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 133 104 280 160 368 432 304), lower := (rows 35 70 133 104 280 160 64 128 256), losses := [] }

theorem u781 : Upper (D 10) (R 10) [34,68,129,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b781 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r782 : Route 9 := (fun mask => (mask,id))

def c782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u782 : Upper (D 10) (R 10) [34,68,129,96,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,264,256] 13 (by decide) (choices 1) [16,32,128] r782 c782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u181
  · exact u182
  · exact u183

def b783 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 133 104 304 40 464 400 400), lower := (rows 35 70 133 104 304 40 64 128 256), losses := [] }

theorem u783 : Upper (D 10) (R 10) [34,68,129,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b783 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 392, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 133 104 304 48 456 392 392), lower := (rows 35 70 133 104 304 48 64 128 256), losses := [] }

theorem u784 : Upper (D 10) (R 10) [34,68,129,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b784 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 133 104 304 160 344 408 280), lower := (rows 35 70 133 104 304 160 64 128 256), losses := [] }

theorem u785 : Upper (D 10) (R 10) [34,68,129,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b785 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 104 304 288 216 152 408), lower := (rows 35 70 133 104 304 288 64 128 256), losses := [] }

theorem u786 : Upper (D 10) (R 10) [34,68,129,96,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b786 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 133 152 304 40 352 480 352), lower := (rows 35 70 133 152 304 40 64 128 256), losses := [] }

theorem u787 : Upper (D 10) (R 10) [34,68,129,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b787 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b788 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 133 152 304 96 360 424 296), lower := (rows 35 70 133 152 304 96 64 128 256), losses := [] }

theorem u788 : Upper (D 10) (R 10) [34,68,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b788 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b789 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 152 304 288 104 232 360), lower := (rows 35 70 133 152 304 288 64 128 256), losses := [] }

theorem u789 : Upper (D 10) (R 10) [34,68,129,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b789 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 133 168 280 48 352 480 352), lower := (rows 35 70 133 168 280 48 64 128 256), losses := [] }

theorem u790 : Upper (D 10) (R 10) [34,68,129,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b790 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 133 168 280 96 368 432 304), lower := (rows 35 70 133 168 280 96 64 128 256), losses := [] }

theorem u791 : Upper (D 10) (R 10) [34,68,129,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b791 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r792 : Route 9 := (fun mask => (mask,id))

def c792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u792 : Upper (D 10) (R 10) [34,68,129,160,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264,256] 13 (by decide) (choices 1) [16,32] r792 c792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u184
  · exact u185

def b793 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 168 304 40 336 464 336), lower := (rows 35 70 133 168 304 40 64 128 256), losses := [] }

theorem u793 : Upper (D 10) (R 10) [34,68,129,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b793 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 328, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 133 168 304 48 328 456 328), lower := (rows 35 70 133 168 304 48 64 128 256), losses := [] }

theorem u794 : Upper (D 10) (R 10) [34,68,129,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b794 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b795 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 133 168 304 96 344 408 280), lower := (rows 35 70 133 168 304 96 64 128 256), losses := [] }

theorem u795 : Upper (D 10) (R 10) [34,68,129,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b795 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b796 : PairBound 9 := { available := 88, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 168 304 288 88 216 344), lower := (rows 35 70 133 168 304 288 64 128 256), losses := [] }

theorem u796 : Upper (D 10) (R 10) [34,68,129,160,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b796 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 176, camps := [{ cop := 8, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 296 336 40 240 176 432), lower := (rows 35 70 133 296 336 40 64 128 256), losses := [] }

theorem u797 : Upper (D 10) (R 10) [34,68,129,288,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b797 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 133 296 336 48 232 168 424), lower := (rows 35 70 133 296 336 48 64 128 256), losses := [] }

theorem u798 : Upper (D 10) (R 10) [34,68,129,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b798 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b799 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 133 296 336 160 120 184 312), lower := (rows 35 70 133 296 336 160 64 128 256), losses := [] }

theorem u799 : Upper (D 10) (R 10) [34,68,129,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b799 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b800 : PairBound 9 := { available := 112, camps := [{ cop := 8, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 296 400 40 112 240 368), lower := (rows 35 70 133 296 400 40 64 128 256), losses := [] }

theorem u800 : Upper (D 10) (R 10) [34,68,129,288,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b800 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b801 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 133 296 400 48 104 232 360), lower := (rows 35 70 133 296 400 48 64 128 256), losses := [] }

theorem u801 : Upper (D 10) (R 10) [34,68,129,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b801 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b802 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 133 296 400 96 120 184 312), lower := (rows 35 70 133 296 400 96 64 128 256), losses := [] }

theorem u802 : Upper (D 10) (R 10) [34,68,129,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b802 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b803 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 56 336 33 480 416 416), lower := (rows 35 70 140 56 336 33 64 128 256), losses := [] }

theorem u803 : Upper (D 10) (R 10) [34,68,136,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b803 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b804 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 140 56 336 160 353 417 289), lower := (rows 35 70 140 56 336 160 64 128 256), losses := [] }

theorem u804 : Upper (D 10) (R 10) [34,68,136,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b804 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b805 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 140 56 336 288 225 161 417), lower := (rows 35 70 140 56 336 288 64 128 256), losses := [] }

theorem u805 : Upper (D 10) (R 10) [34,68,136,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b805 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 265 112 48 480 416 416), lower := (rows 35 70 140 265 112 48 64 128 256), losses := [] }

theorem u806 : Upper (D 10) (R 10) [34,68,136,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b806 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b807 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 140 265 112 160 368 432 304), lower := (rows 35 70 140 265 112 160 64 128 256), losses := [] }

theorem u807 : Upper (D 10) (R 10) [34,68,136,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b807 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b808 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 208, targets := 256 }], pairs := [(1,8),(4,8)], upper := (rows 35 70 140 265 112 288 240 176 432), lower := (rows 35 70 140 265 112 288 64 128 256), losses := [{ target := 8, region := (rows 1 10 12 8 49 32 113 177 0), good := (rows 243 70 142 223 240 240 64 128 0) }] }

theorem u808 : Upper (D 10) (R 10) [34,68,136,257,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b808 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 140 265 176 48 352 480 352), lower := (rows 35 70 140 265 176 48 64 128 256), losses := [] }

theorem u809 : Upper (D 10) (R 10) [34,68,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b809 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b810 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 265 176 96 368 432 304), lower := (rows 35 70 140 265 176 96 64 128 256), losses := [] }

theorem u810 : Upper (D 10) (R 10) [34,68,136,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b810 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b811 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 208, targets := 256 }], pairs := [(4,6),(4,8)], upper := (rows 35 70 140 265 176 288 112 240 368), lower := (rows 35 70 140 265 176 288 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 20 296 0 128 256), good := (rows 35 22 188 297 176 288 0 128 288) }] }

theorem u811 : Upper (D 10) (R 10) [34,68,136,257,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b811 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b812 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 265 208 48 352 416 288), lower := (rows 35 70 140 265 208 48 64 128 256), losses := [] }

theorem u812 : Upper (D 10) (R 10) [34,68,136,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b812 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b813 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 208, targets := 256 }], pairs := [(1,8),(4,8)], upper := (rows 35 70 140 265 208 288 112 176 304), lower := (rows 35 70 140 265 208 288 64 128 256), losses := [{ target := 8, region := (rows 1 10 12 8 57 32 97 161 0), good := (rows 243 70 158 223 208 240 64 128 0) }] }

theorem u813 : Upper (D 10) (R 10) [34,68,136,257,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b813 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b814 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 140 265 304 48 224 224 480), lower := (rows 35 70 140 265 304 48 64 128 256), losses := [] }

theorem u814 : Upper (D 10) (R 10) [34,68,136,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b814 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b815 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 265 304 96 240 176 432), lower := (rows 35 70 140 265 304 96 64 128 256), losses := [] }

theorem u815 : Upper (D 10) (R 10) [34,68,136,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b815 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b816 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 140 265 304 160 112 240 368), lower := (rows 35 70 140 265 304 160 64 128 256), losses := [] }

theorem u816 : Upper (D 10) (R 10) [34,68,136,257,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b816 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b817 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 265 336 48 224 160 416), lower := (rows 35 70 140 265 336 48 64 128 256), losses := [] }

theorem u817 : Upper (D 10) (R 10) [34,68,136,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b817 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b818 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 140 265 336 160 112 176 304), lower := (rows 35 70 140 265 336 160 64 128 256), losses := [] }

theorem u818 : Upper (D 10) (R 10) [34,68,136,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b818 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 265 400 48 96 224 352), lower := (rows 35 70 140 265 400 48 64 128 256), losses := [] }

theorem u819 : Upper (D 10) (R 10) [34,68,136,257,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b819 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 265 400 96 112 176 304), lower := (rows 35 70 140 265 400 96 64 128 256), losses := [] }

theorem u820 : Upper (D 10) (R 10) [34,68,136,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b820 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 280 112 33 480 416 416), lower := (rows 35 70 140 280 112 33 64 128 256), losses := [] }

theorem u821 : Upper (D 10) (R 10) [34,68,136,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b821 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b822 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 140 280 112 160 353 417 289), lower := (rows 35 70 140 280 112 160 64 128 256), losses := [] }

theorem u822 : Upper (D 10) (R 10) [34,68,136,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b822 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b823 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 208, targets := 256 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(4,8)], upper := (rows 35 70 140 280 112 288 225 161 417), lower := (rows 35 70 140 280 112 288 64 128 256), losses := [] }

theorem u823 : Upper (D 10) (R 10) [34,68,136,272,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b823 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b824 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 296 112 33 464 400 400), lower := (rows 35 70 140 296 112 33 64 128 256), losses := [] }

theorem u824 : Upper (D 10) (R 10) [34,68,136,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b824 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b825 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 296 112 48 449 385 385), lower := (rows 35 70 140 296 112 48 64 128 256), losses := [] }

theorem u825 : Upper (D 10) (R 10) [34,68,136,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b825 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b826 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 140 296 112 160 337 401 273), lower := (rows 35 70 140 296 112 160 64 128 256), losses := [] }

theorem u826 : Upper (D 10) (R 10) [34,68,136,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b826 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b827 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 140 296 112 288 209 145 401), lower := (rows 35 70 140 296 112 288 64 128 256), losses := [] }

theorem u827 : Upper (D 10) (R 10) [34,68,136,288,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b827 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b828 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 296 145 48 352 480 352), lower := (rows 35 70 140 296 145 48 64 128 256), losses := [] }

theorem u828 : Upper (D 10) (R 10) [34,68,136,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b828 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b829 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 296 145 96 368 432 304), lower := (rows 35 70 140 296 145 96 64 128 256), losses := [] }

theorem u829 : Upper (D 10) (R 10) [34,68,136,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b829 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b830 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 140 296 145 288 112 240 368), lower := (rows 35 70 140 296 145 288 64 128 256), losses := [] }

theorem u830 : Upper (D 10) (R 10) [34,68,136,288,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b830 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b831 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 296 176 33 336 464 336), lower := (rows 35 70 140 296 176 33 64 128 256), losses := [] }

theorem u831 : Upper (D 10) (R 10) [34,68,136,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b831 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b832 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 140 296 176 48 321 449 321), lower := (rows 35 70 140 296 176 48 64 128 256), losses := [] }

theorem u832 : Upper (D 10) (R 10) [34,68,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b832 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 296 176 96 337 401 273), lower := (rows 35 70 140 296 176 96 64 128 256), losses := [] }

theorem u833 : Upper (D 10) (R 10) [34,68,136,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b833 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 140 296 176 288 81 209 337), lower := (rows 35 70 140 296 176 288 64 128 256), losses := [] }

theorem u834 : Upper (D 10) (R 10) [34,68,136,288,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b834 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 296 208 33 368 432 304), lower := (rows 35 70 140 296 208 33 64 128 256), losses := [] }

theorem u835 : Upper (D 10) (R 10) [34,68,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b835 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b836 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 296 208 48 353 417 289), lower := (rows 35 70 140 296 208 48 64 128 256), losses := [] }

theorem u836 : Upper (D 10) (R 10) [34,68,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b836 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b837 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 140 296 208 288 113 177 305), lower := (rows 35 70 140 296 208 288 64 128 256), losses := [] }

theorem u837 : Upper (D 10) (R 10) [34,68,136,288,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b837 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 140 296 273 48 224 224 480), lower := (rows 35 70 140 296 273 48 64 128 256), losses := [] }

theorem u838 : Upper (D 10) (R 10) [34,68,136,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b838 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b839 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 296 273 96 240 176 432), lower := (rows 35 70 140 296 273 96 64 128 256), losses := [] }

theorem u839 : Upper (D 10) (R 10) [34,68,136,288,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b839 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u839
end Delivery.IrregularNine14.P10
