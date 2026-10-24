import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0101

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20580 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 296 21 34 81 209 337), lower := (rows 35 70 140 296 21 34 64 128 256), losses := [] }

theorem u20580 : Upper (D 6) (R 6) [34,68,136,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20581 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 296 21 48 67 195 323), lower := (rows 35 70 140 296 21 48 64 128 256), losses := [] }

theorem u20581 : Upper (D 6) (R 6) [34,68,136,288,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20581 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20582 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 296 21 96 83 147 275), lower := (rows 35 70 140 296 21 96 64 128 256), losses := [] }

theorem u20582 : Upper (D 6) (R 6) [34,68,136,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20583 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 296 81 33 86 150 278), lower := (rows 35 70 140 296 81 33 64 128 256), losses := [] }

theorem u20583 : Upper (D 6) (R 6) [34,68,136,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20584 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 296 81 34 85 149 277), lower := (rows 35 70 140 296 81 34 64 128 256), losses := [] }

theorem u20584 : Upper (D 6) (R 6) [34,68,136,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20585 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 70 140 296 81 36 83 147 275), lower := (rows 35 70 140 296 81 36 64 128 256), losses := [] }

theorem u20585 : Upper (D 6) (R 6) [34,68,136,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20586 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 296 81 48 71 135 263), lower := (rows 35 70 140 296 81 48 64 128 256), losses := [] }

theorem u20586 : Upper (D 6) (R 6) [34,68,136,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20586 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20587 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 328 21 33 114 178 306), lower := (rows 35 70 140 328 21 33 64 128 256), losses := [] }

theorem u20587 : Upper (D 6) (R 6) [34,68,136,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20588 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 328 21 34 113 177 305), lower := (rows 35 70 140 328 21 34 64 128 256), losses := [] }

theorem u20588 : Upper (D 6) (R 6) [34,68,136,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20589 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 328 21 48 99 163 291), lower := (rows 35 70 140 328 21 48 64 128 256), losses := [] }

theorem u20589 : Upper (D 6) (R 6) [34,68,136,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20589 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20590 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 328 52 33 83 147 275), lower := (rows 35 70 140 328 52 33 64 128 256), losses := [] }

theorem u20590 : Upper (D 6) (R 6) [34,68,136,320,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20591 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 328 52 34 81 145 273), lower := (rows 35 70 140 328 52 34 64 128 256), losses := [] }

theorem u20591 : Upper (D 6) (R 6) [34,68,136,320,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20592 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 140 328 52 48 67 131 259), lower := (rows 35 70 140 328 52 48 64 128 256), losses := [] }

theorem u20592 : Upper (D 6) (R 6) [34,68,136,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20592 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20593 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 13 81 34 344 408 280), lower := (rows 35 70 164 13 81 34 64 128 256), losses := [] }

theorem u20593 : Upper (D 6) (R 6) [34,68,160,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20594 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 164 13 81 40 338 402 274), lower := (rows 35 70 164 13 81 40 64 128 256), losses := [] }

theorem u20594 : Upper (D 6) (R 6) [34,68,160,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20594 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20595 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 13 81 48 330 394 266), lower := (rows 35 70 164 13 81 48 64 128 256), losses := [] }

theorem u20595 : Upper (D 6) (R 6) [34,68,160,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20595 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20596 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 70 164 13 81 288 90 154 282), lower := (rows 35 70 164 13 81 288 64 128 256), losses := [] }

theorem u20596 : Upper (D 6) (R 6) [34,68,160,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20596 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20597 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 164 13 88 33 338 402 274), lower := (rows 35 70 164 13 88 33 64 128 256), losses := [] }

theorem u20597 : Upper (D 6) (R 6) [34,68,160,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20598 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 13 88 34 337 401 273), lower := (rows 35 70 164 13 88 34 64 128 256), losses := [] }

theorem u20598 : Upper (D 6) (R 6) [34,68,160,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20599 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 13 88 48 323 387 259), lower := (rows 35 70 164 13 88 48 64 128 256), losses := [] }

theorem u20599 : Upper (D 6) (R 6) [34,68,160,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20599 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20600 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 70 164 13 88 288 83 147 275), lower := (rows 35 70 164 13 88 288 64 128 256), losses := [] }

theorem u20600 : Upper (D 6) (R 6) [34,68,160,5,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20600 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20601 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 13 273 34 88 216 344), lower := (rows 35 70 164 13 273 34 64 128 256), losses := [] }

theorem u20601 : Upper (D 6) (R 6) [34,68,160,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20602 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 164 13 273 40 82 210 338), lower := (rows 35 70 164 13 273 40 64 128 256), losses := [] }

theorem u20602 : Upper (D 6) (R 6) [34,68,160,5,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20602 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20603 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 338, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 70 164 13 273 48 74 202 330), lower := (rows 35 70 164 13 273 48 64 128 256), losses := [] }

theorem u20603 : Upper (D 6) (R 6) [34,68,160,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20603 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20604 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 13 273 96 90 154 282), lower := (rows 35 70 164 13 273 96 64 128 256), losses := [] }

theorem u20604 : Upper (D 6) (R 6) [34,68,160,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20605 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 164 13 274 33 88 216 344), lower := (rows 35 70 164 13 274 33 64 128 256), losses := [] }

theorem u20605 : Upper (D 6) (R 6) [34,68,160,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20606 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 164 13 274 40 81 209 337), lower := (rows 35 70 164 13 274 40 64 128 256), losses := [] }

theorem u20606 : Upper (D 6) (R 6) [34,68,160,5,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20606 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20607 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 164 13 274 48 73 201 329), lower := (rows 35 70 164 13 274 48 64 128 256), losses := [] }

theorem u20607 : Upper (D 6) (R 6) [34,68,160,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20607 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20608 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 13 274 96 89 153 281), lower := (rows 35 70 164 13 274 96 64 128 256), losses := [] }

theorem u20608 : Upper (D 6) (R 6) [34,68,160,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20609 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 164 13 280 33 82 210 338), lower := (rows 35 70 164 13 280 33 64 128 256), losses := [] }

theorem u20609 : Upper (D 6) (R 6) [34,68,160,5,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20610 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 13 280 34 81 209 337), lower := (rows 35 70 164 13 280 34 64 128 256), losses := [] }

theorem u20610 : Upper (D 6) (R 6) [34,68,160,5,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20611 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 338, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 70 164 13 280 48 67 195 323), lower := (rows 35 70 164 13 280 48 64 128 256), losses := [] }

theorem u20611 : Upper (D 6) (R 6) [34,68,160,5,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20611 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20612 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 13 280 96 83 147 275), lower := (rows 35 70 164 13 280 96 64 128 256), losses := [] }

theorem u20612 : Upper (D 6) (R 6) [34,68,160,5,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20613 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 164 13 336 33 90 154 282), lower := (rows 35 70 164 13 336 33 64 128 256), losses := [] }

theorem u20613 : Upper (D 6) (R 6) [34,68,160,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20614 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 13 336 34 89 153 281), lower := (rows 35 70 164 13 336 34 64 128 256), losses := [] }

theorem u20614 : Upper (D 6) (R 6) [34,68,160,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20615 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 164 13 336 40 83 147 275), lower := (rows 35 70 164 13 336 40 64 128 256), losses := [] }

theorem u20615 : Upper (D 6) (R 6) [34,68,160,5,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20615 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20616 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 13 336 48 75 139 267), lower := (rows 35 70 164 13 336 48 64 128 256), losses := [] }

theorem u20616 : Upper (D 6) (R 6) [34,68,160,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20616 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20617 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 164 25 28 33 322 450 322), lower := (rows 35 70 164 25 28 33 64 128 256), losses := [] }

theorem u20617 : Upper (D 6) (R 6) [34,68,160,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20618 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 25 28 34 321 449 321), lower := (rows 35 70 164 25 28 34 64 128 256), losses := [] }

theorem u20618 : Upper (D 6) (R 6) [34,68,160,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20619 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 25 28 96 323 387 259), lower := (rows 35 70 164 25 28 96 64 128 256), losses := [] }

theorem u20619 : Upper (D 6) (R 6) [34,68,160,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20620 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(1,5)], upper := (rows 35 70 164 25 28 288 67 195 323), lower := (rows 35 70 164 25 28 288 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 73 137 265), good := (rows 451 70 132 475 478 256 64 128 256) }] }

theorem u20620 : Upper (D 6) (R 6) [34,68,160,17,12,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20620 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20621 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 164 25 88 33 326 390 262), lower := (rows 35 70 164 25 88 33 64 128 256), losses := [] }

theorem u20621 : Upper (D 6) (R 6) [34,68,160,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20622 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 25 88 34 325 389 261), lower := (rows 35 70 164 25 88 34 64 128 256), losses := [] }

theorem u20622 : Upper (D 6) (R 6) [34,68,160,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20623 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 25 88 36 323 387 259), lower := (rows 35 70 164 25 88 36 64 128 256), losses := [] }

theorem u20623 : Upper (D 6) (R 6) [34,68,160,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20624 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 164 25 88 288 71 135 263), lower := (rows 35 70 164 25 88 288 64 128 256), losses := [] }

theorem u20624 : Upper (D 6) (R 6) [34,68,160,17,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20624 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20625 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 164 25 274 33 76 204 332), lower := (rows 35 70 164 25 274 33 64 128 256), losses := [] }

theorem u20625 : Upper (D 6) (R 6) [34,68,160,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20626 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 25 274 36 73 201 329), lower := (rows 35 70 164 25 274 36 64 128 256), losses := [] }

theorem u20626 : Upper (D 6) (R 6) [34,68,160,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20627 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 70 164 25 274 40 69 197 325), lower := (rows 35 70 164 25 274 40 64 128 256), losses := [] }

theorem u20627 : Upper (D 6) (R 6) [34,68,160,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20627 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20628 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 25 274 96 77 141 269), lower := (rows 35 70 164 25 274 96 64 128 256), losses := [] }

theorem u20628 : Upper (D 6) (R 6) [34,68,160,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20629 : Route 9 := (fun mask => (mask,id))

def c20629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20629 : Upper (D 6) (R 6) [34,68,160,17,260,1] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,260,1] 13 (by decide) (choices 1) [2,8] r20629 c20629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6085
  · exact u6086

def b20630 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 25 276 34 73 201 329), lower := (rows 35 70 164 25 276 34 64 128 256), losses := [] }

theorem u20630 : Upper (D 6) (R 6) [34,68,160,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20631 : Route 9 := (fun mask => (mask,id))

def c20631 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20631 : Upper (D 6) (R 6) [34,68,160,17,260,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,260,8] 13 (by decide) (choices 1) [1,2] r20631 c20631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6087
  · exact u6088

def b20632 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 25 276 96 75 139 267), lower := (rows 35 70 164 25 276 96 64 128 256), losses := [] }

theorem u20632 : Upper (D 6) (R 6) [34,68,160,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20633 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 70 164 25 280 33 70 198 326), lower := (rows 35 70 164 25 280 33 64 128 256), losses := [] }

theorem u20633 : Upper (D 6) (R 6) [34,68,160,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20634 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 25 280 34 69 197 325), lower := (rows 35 70 164 25 280 34 64 128 256), losses := [] }

theorem u20634 : Upper (D 6) (R 6) [34,68,160,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20635 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 25 280 36 67 195 323), lower := (rows 35 70 164 25 280 36 64 128 256), losses := [] }

theorem u20635 : Upper (D 6) (R 6) [34,68,160,17,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20636 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 25 280 96 71 135 263), lower := (rows 35 70 164 25 280 96 64 128 256), losses := [] }

theorem u20636 : Upper (D 6) (R 6) [34,68,160,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20637 : Route 9 := (fun mask => (mask,id))

def c20637 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20637 : Upper (D 6) (R 6) [34,68,160,17,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,320,1] 13 (by decide) (choices 1) [2,4,8] r20637 c20637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6089
  · exact u6090
  · exact u6091

def b20638 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 25 336 34 77 141 269), lower := (rows 35 70 164 25 336 34 64 128 256), losses := [] }

theorem u20638 : Upper (D 6) (R 6) [34,68,160,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20639 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 25 336 36 75 139 267), lower := (rows 35 70 164 25 336 36 64 128 256), losses := [] }

theorem u20639 : Upper (D 6) (R 6) [34,68,160,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20639
end Delivery.IrregularNine14.P06
