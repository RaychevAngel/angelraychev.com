import IrregularTen14Base

namespace Delivery.IrregularTen14.Case50
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_0 : Bound 10 := { allowed := (rows 224 144 240 240 0 0 0 0 0 0), upper := (rows 273 98 767 767 767 767 767 767 1023 767), lower := (rows 273 98 4 8 16 32 64 128 256 512), losses := [] }

theorem upper_0 : Upper D R [272,96] 13 :=
  bound_sound D R [272,96] 13 bound_0
    ((Boolean.boundCheck_true D R [272,96] 13 bound_0).mp (by decide +kernel))

theorem upper : Upper D R [272,96] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case50
