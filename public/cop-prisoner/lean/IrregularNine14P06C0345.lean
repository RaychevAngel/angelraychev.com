import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20700 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 88 276 40 67 131 259), lower := (rows 35 70 164 88 276 40 64 128 256), losses := [] }

theorem u20700 : Upper (D 6) (R 6) [34,68,160,80,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20700 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20701 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 164 88 280 33 71 135 263), lower := (rows 35 70 164 88 280 33 64 128 256), losses := [] }

theorem u20701 : Upper (D 6) (R 6) [34,68,160,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20702 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 88 280 34 69 133 261), lower := (rows 35 70 164 88 280 34 64 128 256), losses := [] }

theorem u20702 : Upper (D 6) (R 6) [34,68,160,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20703 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 88 280 36 67 131 259), lower := (rows 35 70 164 88 280 36 64 128 256), losses := [] }

theorem u20703 : Upper (D 6) (R 6) [34,68,160,80,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20704 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 388 13 26 33 112 240 368), lower := (rows 35 70 388 13 26 33 64 128 256), losses := [] }

theorem u20704 : Upper (D 6) (R 6) [34,68,384,5,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20705 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 388 13 26 48 97 225 353), lower := (rows 35 70 388 13 26 48 64 128 256), losses := [] }

theorem u20705 : Upper (D 6) (R 6) [34,68,384,5,10,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20705 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20706 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 388 13 26 96 113 177 305), lower := (rows 35 70 388 13 26 96 64 128 256), losses := [] }

theorem u20706 : Upper (D 6) (R 6) [34,68,384,5,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20707 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 13 56 33 82 210 338), lower := (rows 35 70 388 13 56 33 64 128 256), losses := [] }

theorem u20707 : Upper (D 6) (R 6) [34,68,384,5,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20708 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 13 56 34 81 209 337), lower := (rows 35 70 388 13 56 34 64 128 256), losses := [] }

theorem u20708 : Upper (D 6) (R 6) [34,68,384,5,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20709 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 388 13 56 48 67 195 323), lower := (rows 35 70 388 13 56 48 64 128 256), losses := [] }

theorem u20709 : Upper (D 6) (R 6) [34,68,384,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20709 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20710 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 388 13 56 96 83 147 275), lower := (rows 35 70 388 13 56 96 64 128 256), losses := [] }

theorem u20710 : Upper (D 6) (R 6) [34,68,384,5,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20711 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 13 81 34 120 184 312), lower := (rows 35 70 388 13 81 34 64 128 256), losses := [] }

theorem u20711 : Upper (D 6) (R 6) [34,68,384,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20712 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 388 13 81 40 114 178 306), lower := (rows 35 70 388 13 81 40 64 128 256), losses := [] }

theorem u20712 : Upper (D 6) (R 6) [34,68,384,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20712 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20713 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 388 13 81 48 106 170 298), lower := (rows 35 70 388 13 81 48 64 128 256), losses := [] }

theorem u20713 : Upper (D 6) (R 6) [34,68,384,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20713 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20714 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 70 388 13 88 33 114 178 306), lower := (rows 35 70 388 13 88 33 64 128 256), losses := [] }

theorem u20714 : Upper (D 6) (R 6) [34,68,384,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20715 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 13 88 34 113 177 305), lower := (rows 35 70 388 13 88 34 64 128 256), losses := [] }

theorem u20715 : Upper (D 6) (R 6) [34,68,384,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20716 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 388 13 88 48 99 163 291), lower := (rows 35 70 388 13 88 48 64 128 256), losses := [] }

theorem u20716 : Upper (D 6) (R 6) [34,68,384,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20716 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20717 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 388 13 112 33 90 154 282), lower := (rows 35 70 388 13 112 33 64 128 256), losses := [] }

theorem u20717 : Upper (D 6) (R 6) [34,68,384,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20718 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 13 112 34 89 153 281), lower := (rows 35 70 388 13 112 34 64 128 256), losses := [] }

theorem u20718 : Upper (D 6) (R 6) [34,68,384,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20719 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 388 13 112 40 83 147 275), lower := (rows 35 70 388 13 112 40 64 128 256), losses := [] }

theorem u20719 : Upper (D 6) (R 6) [34,68,384,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20719 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20720 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 388 13 112 48 75 139 267), lower := (rows 35 70 388 13 112 48 64 128 256), losses := [] }

theorem u20720 : Upper (D 6) (R 6) [34,68,384,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20720 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20721 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 388 25 28 33 98 226 354), lower := (rows 35 70 388 25 28 33 64 128 256), losses := [] }

theorem u20721 : Upper (D 6) (R 6) [34,68,384,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20722 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 25 28 34 97 225 353), lower := (rows 35 70 388 25 28 34 64 128 256), losses := [] }

theorem u20722 : Upper (D 6) (R 6) [34,68,384,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20723 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 388 25 28 96 99 163 291), lower := (rows 35 70 388 25 28 96 64 128 256), losses := [] }

theorem u20723 : Upper (D 6) (R 6) [34,68,384,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20724 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 25 52 33 74 202 330), lower := (rows 35 70 388 25 52 33 64 128 256), losses := [] }

theorem u20724 : Upper (D 6) (R 6) [34,68,384,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20725 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 25 52 34 73 201 329), lower := (rows 35 70 388 25 52 34 64 128 256), losses := [] }

theorem u20725 : Upper (D 6) (R 6) [34,68,384,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20726 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 388 25 52 40 67 195 323), lower := (rows 35 70 388 25 52 40 64 128 256), losses := [] }

theorem u20726 : Upper (D 6) (R 6) [34,68,384,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20726 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20727 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 388 25 52 96 75 139 267), lower := (rows 35 70 388 25 52 96 64 128 256), losses := [] }

theorem u20727 : Upper (D 6) (R 6) [34,68,384,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20728 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 388 25 88 33 102 166 294), lower := (rows 35 70 388 25 88 33 64 128 256), losses := [] }

theorem u20728 : Upper (D 6) (R 6) [34,68,384,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20729 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 25 88 34 101 165 293), lower := (rows 35 70 388 25 88 34 64 128 256), losses := [] }

theorem u20729 : Upper (D 6) (R 6) [34,68,384,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20730 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 388 25 88 36 99 163 291), lower := (rows 35 70 388 25 88 36 64 128 256), losses := [] }

theorem u20730 : Upper (D 6) (R 6) [34,68,384,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20731 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 25 112 33 78 142 270), lower := (rows 35 70 388 25 112 33 64 128 256), losses := [] }

theorem u20731 : Upper (D 6) (R 6) [34,68,384,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20732 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 25 112 34 77 141 269), lower := (rows 35 70 388 25 112 34 64 128 256), losses := [] }

theorem u20732 : Upper (D 6) (R 6) [34,68,384,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20733 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 70 388 25 112 36 75 139 267), lower := (rows 35 70 388 25 112 36 64 128 256), losses := [] }

theorem u20733 : Upper (D 6) (R 6) [34,68,384,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20734 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 388 25 112 40 71 135 263), lower := (rows 35 70 388 25 112 40 64 128 256), losses := [] }

theorem u20734 : Upper (D 6) (R 6) [34,68,384,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20734 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20735 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 388 26 52 33 73 201 329), lower := (rows 35 70 388 26 52 33 64 128 256), losses := [] }

theorem u20735 : Upper (D 6) (R 6) [34,68,384,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20736 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 388 26 52 40 65 193 321), lower := (rows 35 70 388 26 52 40 64 128 256), losses := [] }

theorem u20736 : Upper (D 6) (R 6) [34,68,384,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20736 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20737 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 388 26 52 96 73 137 265), lower := (rows 35 70 388 26 52 96 64 128 256), losses := [] }

theorem u20737 : Upper (D 6) (R 6) [34,68,384,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20738 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 388 26 81 33 108 172 300), lower := (rows 35 70 388 26 81 33 64 128 256), losses := [] }

theorem u20738 : Upper (D 6) (R 6) [34,68,384,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20739 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 388 26 81 36 105 169 297), lower := (rows 35 70 388 26 81 36 64 128 256), losses := [] }

theorem u20739 : Upper (D 6) (R 6) [34,68,384,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20740 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 388 26 81 40 101 165 293), lower := (rows 35 70 388 26 81 40 64 128 256), losses := [] }

theorem u20740 : Upper (D 6) (R 6) [34,68,384,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20740 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20741 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 388 26 112 33 77 141 269), lower := (rows 35 70 388 26 112 33 64 128 256), losses := [] }

theorem u20741 : Upper (D 6) (R 6) [34,68,384,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20742 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 35 70 388 26 112 36 73 137 265), lower := (rows 35 70 388 26 112 36 64 128 256), losses := [] }

theorem u20742 : Upper (D 6) (R 6) [34,68,384,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20743 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 388 26 112 40 69 133 261), lower := (rows 35 70 388 26 112 40 64 128 256), losses := [] }

theorem u20743 : Upper (D 6) (R 6) [34,68,384,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20743 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20744 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 388 28 81 33 106 170 298), lower := (rows 35 70 388 28 81 33 64 128 256), losses := [] }

theorem u20744 : Upper (D 6) (R 6) [34,68,384,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20745 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 28 81 34 105 169 297), lower := (rows 35 70 388 28 81 34 64 128 256), losses := [] }

theorem u20745 : Upper (D 6) (R 6) [34,68,384,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20746 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(4,2)], upper := (rows 35 70 388 28 81 40 99 163 291), lower := (rows 35 70 388 28 81 40 64 128 256), losses := [] }

theorem u20746 : Upper (D 6) (R 6) [34,68,384,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20746 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20747 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 388 28 112 33 75 139 267), lower := (rows 35 70 388 28 112 33 64 128 256), losses := [] }

theorem u20747 : Upper (D 6) (R 6) [34,68,384,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20748 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 28 112 34 73 137 265), lower := (rows 35 70 388 28 112 34 64 128 256), losses := [] }

theorem u20748 : Upper (D 6) (R 6) [34,68,384,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20749 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 388 28 112 40 67 131 259), lower := (rows 35 70 388 28 112 40 64 128 256), losses := [] }

theorem u20749 : Upper (D 6) (R 6) [34,68,384,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20749 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20750 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 388 44 81 33 90 154 282), lower := (rows 35 70 388 44 81 33 64 128 256), losses := [] }

theorem u20750 : Upper (D 6) (R 6) [34,68,384,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20751 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 44 81 34 89 153 281), lower := (rows 35 70 388 44 81 34 64 128 256), losses := [] }

theorem u20751 : Upper (D 6) (R 6) [34,68,384,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20752 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 388 44 81 40 83 147 275), lower := (rows 35 70 388 44 81 40 64 128 256), losses := [] }

theorem u20752 : Upper (D 6) (R 6) [34,68,384,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20752 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20753 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 388 44 81 48 75 139 267), lower := (rows 35 70 388 44 81 48 64 128 256), losses := [] }

theorem u20753 : Upper (D 6) (R 6) [34,68,384,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20753 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20754 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 70 388 44 88 33 83 147 275), lower := (rows 35 70 388 44 88 33 64 128 256), losses := [] }

theorem u20754 : Upper (D 6) (R 6) [34,68,384,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20755 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 44 88 34 81 145 273), lower := (rows 35 70 388 44 88 34 64 128 256), losses := [] }

theorem u20755 : Upper (D 6) (R 6) [34,68,384,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20756 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 388 44 88 48 67 131 259), lower := (rows 35 70 388 44 88 48 64 128 256), losses := [] }

theorem u20756 : Upper (D 6) (R 6) [34,68,384,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20756 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20757 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 56 81 33 78 142 270), lower := (rows 35 70 388 56 81 33 64 128 256), losses := [] }

theorem u20757 : Upper (D 6) (R 6) [34,68,384,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20758 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 388 56 81 34 77 141 269), lower := (rows 35 70 388 56 81 34 64 128 256), losses := [] }

theorem u20758 : Upper (D 6) (R 6) [34,68,384,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20759 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 388 56 81 36 75 139 267), lower := (rows 35 70 388 56 81 36 64 128 256), losses := [] }

theorem u20759 : Upper (D 6) (R 6) [34,68,384,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20759
end Delivery.IrregularNine14.P06
