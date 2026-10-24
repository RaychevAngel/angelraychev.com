import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b780 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 13 200 146 34 96 144 257), lower := (rows 37 322 13 200 146 34 96 144 256), losses := [] }

theorem u780 : Upper (D 7) (R 7) [36,320,9,192,130,2,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b780 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 221, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 322 140 25 208 34 96 129 258), lower := (rows 37 322 140 25 208 34 96 129 256), losses := [] }

theorem u781 : Upper (D 7) (R 7) [36,320,136,17,192,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b782 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 8, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 322 140 25 208 34 96 130 257), lower := (rows 37 322 140 25 208 34 96 130 256), losses := [] }

theorem u782 : Upper (D 7) (R 7) [36,320,136,17,192,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b783 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 274, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 322 196 11 146 40 96 129 272), lower := (rows 37 322 196 11 146 40 96 129 256), losses := [] }

theorem u783 : Upper (D 7) (R 7) [36,320,192,3,130,8,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b783 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 148, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 37 322 196 11 146 40 96 144 257), lower := (rows 37 322 196 11 146 40 96 144 256), losses := [] }

theorem u784 : Upper (D 7) (R 7) [36,320,192,3,130,8,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b784 [(5,3),(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 306, targets := 1 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,0),(4,0)], upper := (rows 37 322 196 25 146 34 65 136 288), lower := (rows 37 322 196 25 146 34 65 136 256), losses := [] }

theorem u785 : Upper (D 7) (R 7) [36,320,192,17,130,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b785 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 180, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(2,0),(2,1),(4,0)], upper := (rows 37 322 196 25 146 34 65 160 264), lower := (rows 37 322 196 25 146 34 65 160 256), losses := [] }

theorem u786 : Upper (D 7) (R 7) [36,320,192,17,130,2,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 2, camps := [{ cop := 7, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 322 196 25 152 34 96 129 258), lower := (rows 37 322 196 25 152 34 96 129 256), losses := [] }

theorem u787 : Upper (D 7) (R 7) [36,320,192,17,136,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b788 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 8, region := 230, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 322 196 25 152 34 96 130 257), lower := (rows 37 322 196 25 152 34 96 130 256), losses := [] }

theorem u788 : Upper (D 7) (R 7) [36,320,192,17,136,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b789 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 322 196 26 176 34 65 129 264), lower := (rows 37 322 196 26 176 34 65 129 256), losses := [] }

theorem u789 : Upper (D 7) (R 7) [36,320,192,18,160,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 152, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 322 196 26 176 34 65 136 257), lower := (rows 37 322 196 26 176 34 65 136 256), losses := [] }

theorem u790 : Upper (D 7) (R 7) [36,320,192,18,160,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b790 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 306, targets := 1 },{ cop := 0, region := 130, targets := 64 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(4,0)], upper := (rows 97 162 13 28 336 34 192 129 258), lower := (rows 97 162 13 28 336 34 192 129 256), losses := [] }

theorem u791 : Upper (D 7) (R 7) [96,160,9,20,320,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b792 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 284, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 28 336 34 192 130 257), lower := (rows 97 162 13 28 336 34 192 130 256), losses := [] }

theorem u792 : Upper (D 7) (R 7) [96,160,9,20,320,2,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b793 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 162 13 152 336 34 68 129 258), lower := (rows 97 162 13 152 336 34 68 129 256), losses := [{ target := 0, region := (rows 0 138 4 136 85 174 68 128 430), good := (rows 368 426 382 442 336 290 372 442 256) }] }

theorem u793 : Upper (D 7) (R 7) [96,160,9,144,320,2,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b793 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 349, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 152 336 34 68 130 257), lower := (rows 97 162 13 152 336 34 68 130 256), losses := [] }

theorem u794 : Upper (D 7) (R 7) [96,160,9,144,320,2,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b794 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b795 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 162 13 280 208 34 68 129 258), lower := (rows 97 162 13 280 208 34 68 129 256), losses := [] }

theorem u795 : Upper (D 7) (R 7) [96,160,9,272,192,2,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b795 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b796 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 349, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 280 208 34 68 130 257), lower := (rows 97 162 13 280 208 34 68 130 256), losses := [] }

theorem u796 : Upper (D 7) (R 7) [96,160,9,272,192,2,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b796 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 305, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 162 76 152 273 33 66 130 260), lower := (rows 97 162 76 152 273 33 66 130 256), losses := [] }

theorem u797 : Upper (D 7) (R 7) [96,160,72,144,257,1,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 337, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(4,7)], upper := (rows 97 162 76 152 273 33 66 132 258), lower := (rows 97 162 76 152 273 33 66 132 256), losses := [] }

theorem u798 : Upper (D 7) (R 7) [96,160,72,144,257,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b798 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b799 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 188, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 97 259 14 56 145 34 192 132 320), lower := (rows 97 259 14 56 145 34 192 132 256), losses := [] }

theorem u799 : Upper (D 7) (R 7) [96,257,10,48,129,2,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b799 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b800 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 302, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 97 259 14 56 145 34 192 192 260), lower := (rows 97 259 14 56 145 34 192 192 256), losses := [] }

theorem u800 : Upper (D 7) (R 7) [96,257,10,48,129,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b801 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 188, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 97 259 28 42 145 160 66 132 320), lower := (rows 97 259 28 42 145 160 66 132 256), losses := [] }

theorem u801 : Upper (D 7) (R 7) [96,257,24,34,129,128,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b801 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b802 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 302, targets := 64 },{ cop := 6, region := 161, targets := 2 }], pairs := [(0,1),(1,6),(2,6),(3,6)], upper := (rows 97 259 28 42 145 160 66 192 260), lower := (rows 97 259 28 42 145 160 66 192 256), losses := [] }

theorem u802 : Upper (D 7) (R 7) [96,257,24,34,129,128,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b803 : PairBound 9 := { available := 4, camps := [{ cop := 6, region := 177, targets := 2 },{ cop := 0, region := 144, targets := 32 },{ cop := 1, region := 168, targets := 64 }], pairs := [(0,1),(3,6),(4,1),(4,5)], upper := (rows 97 259 28 42 208 160 66 129 260), lower := (rows 97 259 28 42 208 160 66 129 256), losses := [] }

theorem u803 : Upper (D 7) (R 7) [96,257,24,34,192,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b804 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 252, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 97 259 28 42 208 160 66 132 257), lower := (rows 97 259 28 42 208 160 66 132 256), losses := [] }

theorem u804 : Upper (D 7) (R 7) [96,257,24,34,192,128,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b804 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b805 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 330, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 97 259 38 88 145 160 66 132 264), lower := (rows 97 259 38 88 145 160 66 132 256), losses := [] }

theorem u805 : Upper (D 7) (R 7) [96,257,34,80,129,128,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b805 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 259 38 88 145 160 66 136 260), lower := (rows 97 259 38 88 145 160 66 136 256), losses := [] }

theorem u806 : Upper (D 7) (R 7) [96,257,34,80,129,128,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b806 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b807 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 7 26 176 33 192 136 320), lower := (rows 97 262 7 26 176 33 192 136 256), losses := [] }

theorem u807 : Upper (D 7) (R 7) [96,260,3,18,160,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b807 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b808 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 241, targets := 2 },{ cop := 0, region := 144, targets := 1 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(4,0),(4,1)], upper := (rows 97 262 7 26 176 33 192 192 264), lower := (rows 97 262 7 26 176 33 192 192 256), losses := [] }

theorem u808 : Upper (D 7) (R 7) [96,260,3,18,160,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 217, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 262 7 56 145 34 192 136 320), lower := (rows 97 262 7 56 145 34 192 136 256), losses := [] }

theorem u809 : Upper (D 7) (R 7) [96,260,3,48,129,2,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b809 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b810 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 302, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 97 262 7 56 145 34 192 192 264), lower := (rows 97 262 7 56 145 34 192 192 256), losses := [] }

theorem u810 : Upper (D 7) (R 7) [96,260,3,48,129,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b811 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 7 56 146 33 192 136 320), lower := (rows 97 262 7 56 146 33 192 136 256), losses := [] }

theorem u811 : Upper (D 7) (R 7) [96,260,3,48,130,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b811 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b812 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 208, targets := 33 },{ cop := 4, region := 105, targets := 2 }], pairs := [(0,1),(3,1),(4,0),(4,5)], upper := (rows 97 262 7 56 146 33 192 192 264), lower := (rows 97 262 7 56 146 33 192 192 256), losses := [] }

theorem u812 : Upper (D 7) (R 7) [96,260,3,48,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b813 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 326, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 97 262 14 168 19 33 192 144 320), lower := (rows 97 262 14 168 19 33 192 144 256), losses := [] }

theorem u813 : Upper (D 7) (R 7) [96,260,10,160,3,1,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b813 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b814 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 233, targets := 2 },{ cop := 0, region := 136, targets := 1 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(3,0),(3,1)], upper := (rows 97 262 14 168 19 33 192 192 272), lower := (rows 97 262 14 168 19 33 192 192 256), losses := [] }

theorem u814 : Upper (D 7) (R 7) [96,260,10,160,3,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b815 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 326, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 97 262 14 168 19 48 192 129 320), lower := (rows 97 262 14 168 19 48 192 129 256), losses := [] }

theorem u815 : Upper (D 7) (R 7) [96,260,10,160,3,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b815 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b816 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(2,0),(3,0)], upper := (rows 97 262 14 168 19 48 192 192 257), lower := (rows 97 262 14 168 19 48 192 192 256), losses := [] }

theorem u816 : Upper (D 7) (R 7) [96,260,10,160,3,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b816 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b817 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 38 25 146 33 192 136 320), lower := (rows 97 262 38 25 146 33 192 136 256), losses := [] }

theorem u817 : Upper (D 7) (R 7) [96,260,34,17,130,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b817 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b818 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 294, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 97 262 38 25 146 33 192 192 264), lower := (rows 97 262 38 25 146 33 192 192 256), losses := [] }

theorem u818 : Upper (D 7) (R 7) [96,260,34,17,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 2, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(2,1)], upper := (rows 97 262 44 74 146 160 65 129 272), lower := (rows 97 262 44 74 146 160 65 129 256), losses := [{ target := 0, region := (rows 0 247 133 73 176 176 64 128 437), good := (rows 382 262 318 74 438 438 334 446 256) }] }

theorem u819 : Upper (D 7) (R 7) [96,260,40,66,130,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 180, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 97 262 44 74 146 160 65 144 257), lower := (rows 97 262 44 74 146 160 65 144 256), losses := [] }

theorem u820 : Upper (D 7) (R 7) [96,260,40,66,130,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b820 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 358, targets := 1 },{ cop := 4, region := 136, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 97 262 44 137 19 34 192 144 320), lower := (rows 97 262 44 137 19 34 192 144 256), losses := [] }

theorem u821 : Upper (D 7) (R 7) [96,260,40,129,3,2,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b821 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b822 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 310, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 97 262 44 137 19 34 192 192 272), lower := (rows 97 262 44 137 19 34 192 192 256), losses := [] }

theorem u822 : Upper (D 7) (R 7) [96,260,40,129,3,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b823 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 374, targets := 1 },{ cop := 5, region := 193, targets := 2 }], pairs := [(0,1),(1,0),(2,0),(4,0)], upper := (rows 97 262 44 137 82 34 192 129 272), lower := (rows 97 262 44 137 82 34 192 129 256), losses := [] }

theorem u823 : Upper (D 7) (R 7) [96,260,40,129,66,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b824 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 294, targets := 192 }], pairs := [(1,6),(1,7),(2,6)], upper := (rows 97 262 44 137 82 34 192 144 257), lower := (rows 97 262 44 137 82 34 192 144 256), losses := [] }

theorem u824 : Upper (D 7) (R 7) [96,260,40,129,66,2,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b824 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b825 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 172, targets := 64 },{ cop := 2, region := 193, targets := 2 }], pairs := [(0,1),(2,6),(3,6)], upper := (rows 97 262 44 138 19 48 192 129 320), lower := (rows 97 262 44 138 19 48 192 129 256), losses := [] }

theorem u825 : Upper (D 7) (R 7) [96,260,40,130,3,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b825 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b826 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 200, targets := 33 },{ cop := 2, region := 193, targets := 2 }], pairs := [(0,1),(3,0),(3,5)], upper := (rows 97 262 44 138 19 48 192 192 257), lower := (rows 97 262 44 138 19 48 192 192 256), losses := [] }

theorem u826 : Upper (D 7) (R 7) [96,260,40,130,3,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b826 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b827 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 310, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 44 200 146 34 65 129 272), lower := (rows 97 262 44 200 146 34 65 129 256), losses := [] }

theorem u827 : Upper (D 7) (R 7) [96,260,40,192,130,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b828 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 44 200 146 34 65 144 257), lower := (rows 97 262 44 200 146 34 65 144 256), losses := [] }

theorem u828 : Upper (D 7) (R 7) [96,260,40,192,130,2,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b828 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b829 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 330, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 97 262 133 11 56 160 66 144 320), lower := (rows 97 262 133 11 56 160 66 144 256), losses := [] }

theorem u829 : Upper (D 7) (R 7) [96,260,129,3,40,128,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b829 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b830 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 314, targets := 64 },{ cop := 6, region := 161, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 97 262 133 11 56 160 66 192 272), lower := (rows 97 262 133 11 56 160 66 192 256), losses := [] }

theorem u830 : Upper (D 7) (R 7) [96,260,129,3,40,128,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b831 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 184, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 97 262 133 26 176 34 65 136 320), lower := (rows 97 262 133 26 176 34 65 136 256), losses := [] }

theorem u831 : Upper (D 7) (R 7) [96,260,129,18,160,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b831 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b832 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 314, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 262 133 26 176 34 65 192 264), lower := (rows 97 262 133 26 176 34 65 192 256), losses := [] }

theorem u832 : Upper (D 7) (R 7) [96,260,129,18,160,2,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 97 262 133 56 146 33 66 136 320), lower := (rows 97 262 133 56 146 33 66 136 256), losses := [] }

theorem u833 : Upper (D 7) (R 7) [96,260,129,48,130,1,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b833 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 314, targets := 64 },{ cop := 1, region := 208, targets := 1 }], pairs := [(1,6),(3,6),(4,0),(4,6)], upper := (rows 97 262 133 56 146 33 66 192 264), lower := (rows 97 262 133 56 146 33 66 192 256), losses := [] }

theorem u834 : Upper (D 7) (R 7) [96,260,129,48,130,1,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 209, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(4,1)], upper := (rows 97 262 134 42 88 33 192 129 272), lower := (rows 97 262 134 42 88 33 192 129 256), losses := [{ target := 0, region := (rows 0 215 196 41 145 32 196 128 501), good := (rows 382 326 470 298 350 314 470 478 256) }] }

theorem u835 : Upper (D 7) (R 7) [96,260,130,34,72,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b836 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 262 134 42 88 33 192 144 257), lower := (rows 97 262 134 42 88 33 192 144 256), losses := [] }

theorem u836 : Upper (D 7) (R 7) [96,260,130,34,72,1,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b836 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b837 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 197, targets := 2 },{ cop := 6, region := 294, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(2,1)], upper := (rows 97 262 164 25 26 34 192 129 320), lower := (rows 97 262 164 25 26 34 192 129 256), losses := [] }

theorem u837 : Upper (D 7) (R 7) [96,260,160,17,10,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 197, targets := 2 },{ cop := 8, region := 230, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(2,1)], upper := (rows 97 262 164 25 26 34 192 192 257), lower := (rows 97 262 164 25 26 34 192 192 256), losses := [] }

theorem u838 : Upper (D 7) (R 7) [96,260,160,17,10,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b839 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 97 262 164 25 146 33 66 136 320), lower := (rows 97 262 164 25 146 33 66 136 256), losses := [] }

theorem u839 : Upper (D 7) (R 7) [96,260,160,17,130,1,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b839 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u839
end Delivery.IrregularNine14.P07
