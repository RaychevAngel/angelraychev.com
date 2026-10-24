import FiniteExclusionKernel

set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

namespace Delivery.FiniteExclusion.Cycle3x3x3
open FiniteGame Extremal

def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 5
  | 5 => 3
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

theorem node_2 : Excluded a [2] :=
  source_excluded a [2] 0 3 1 (by decide) (by decide +kernel)

theorem node_4 : Excluded a [3,0] :=
  source_excluded a [3,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_5 : Excluded a [3,4] :=
  predecessor_excluded a [3,4] 2 4 0 1 (by decide) (by decide +kernel)

theorem node_7 : Excluded a [3,5,1] :=
  source_excluded a [3,5,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_9 : Excluded a [3,5,4,0] :=
  source_excluded a [3,5,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_10 : Excluded a [3,5,4,1] :=
  source_excluded a [3,5,4,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_11 : Excluded a [3,5,4,2] :=
  source_excluded a [3,5,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_13 : Excluded a [3,5,4,6,0] :=
  source_excluded a [3,5,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_14 : Excluded a [3,5,4,6,1] :=
  source_excluded a [3,5,4,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_15 : Excluded a [3,5,4,6,2] :=
  source_excluded a [3,5,4,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_16 : Excluded a [3,5,4,6,7] :=
  predecessor_excluded a [3,5,4,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_18 : Excluded a [3,5,4,6,8,0] :=
  source_excluded a [3,5,4,6,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_19 : Excluded a [3,5,4,6,8,1] :=
  source_excluded a [3,5,4,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_20 : Excluded a [3,5,4,6,8,2] :=
  source_excluded a [3,5,4,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_23 : Excluded a [3,5,4,6,8,7,0,1] :=
  predecessor_excluded a [3,5,4,6,8,7,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_25 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_25 : LosingRegion (edgeOf a b_25) 0 :=
  losingMask a b_25 0 1512339026974287451980800
    (by decide +kernel) (by decide +kernel)

theorem node_25 : Excluded a [3,5,4,6,8,7,0,2,1] :=
  losing_excluded a [3,5,4,6,8,7,0,2,1] (by decide) b_25 (by decide +kernel) 1 0 7 cert_25 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_25 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1512339026974287451980800 1 7; decide +kernel)

theorem node_24 : Excluded a [3,5,4,6,8,7,0,2] :=
  branch_excluded a [3,5,4,6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,6,8,7,0,2,0] (by decide +kernel))
      node_25
      (invalid_excluded a [3,5,4,6,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,2,8] (by decide +kernel)))

theorem node_22 : Excluded a [3,5,4,6,8,7,0] :=
  branch_excluded a [3,5,4,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,6,8,7,0,0] (by decide +kernel))
      node_23
      node_24
      (invalid_excluded a [3,5,4,6,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,0,8] (by decide +kernel)))

def b_28 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_28 : LosingRegion (edgeOf a b_28) 0 :=
  losingMask a b_28 0 1210109877908713044575232
    (by decide +kernel) (by decide +kernel)

theorem node_28 : Excluded a [3,5,4,6,8,7,1,0,2] :=
  losing_excluded a [3,5,4,6,8,7,1,0,2] (by decide) b_28 (by decide +kernel) 1 0 8 cert_28 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_28 1 0 ∧ 8 ≠ 1 ∧ maskRegion 1210109877908713044575232 1 8; decide +kernel)

theorem node_27 : Excluded a [3,5,4,6,8,7,1,0] :=
  branch_excluded a [3,5,4,6,8,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,6,8,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,0,1] (by decide +kernel))
      node_28
      (invalid_excluded a [3,5,4,6,8,7,1,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,0,8] (by decide +kernel)))

theorem node_29 : Excluded a [3,5,4,6,8,7,1,2] :=
  predecessor_excluded a [3,5,4,6,8,7,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_26 : Excluded a [3,5,4,6,8,7,1] :=
  branch_excluded a [3,5,4,6,8,7,1] (by decide)
    (fin9_cases _
      node_27
      (invalid_excluded a [3,5,4,6,8,7,1,1] (by decide +kernel))
      node_29
      (invalid_excluded a [3,5,4,6,8,7,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,1,8] (by decide +kernel)))

theorem node_31 : Excluded a [3,5,4,6,8,7,2,0] :=
  predecessor_excluded a [3,5,4,6,8,7,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_33 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_33 : LosingRegion (edgeOf a b_33) 0 :=
  losingMask a b_33 0 1212468764877266386717696
    (by decide +kernel) (by decide +kernel)

theorem node_33 : Excluded a [3,5,4,6,8,7,2,1,0] :=
  losing_excluded a [3,5,4,6,8,7,2,1,0] (by decide) b_33 (by decide +kernel) 1 0 2 cert_33 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_33 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212468764877266386717696 1 2; decide +kernel)

theorem node_32 : Excluded a [3,5,4,6,8,7,2,1] :=
  branch_excluded a [3,5,4,6,8,7,2,1] (by decide)
    (fin9_cases _
      node_33
      (invalid_excluded a [3,5,4,6,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,1,8] (by decide +kernel)))

theorem node_30 : Excluded a [3,5,4,6,8,7,2] :=
  branch_excluded a [3,5,4,6,8,7,2] (by decide)
    (fin9_cases _
      node_31
      node_32
      (invalid_excluded a [3,5,4,6,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,2,8] (by decide +kernel)))

theorem node_21 : Excluded a [3,5,4,6,8,7] :=
  branch_excluded a [3,5,4,6,8,7] (by decide)
    (fin9_cases _
      node_22
      node_26
      node_30
      (invalid_excluded a [3,5,4,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,7,8] (by decide +kernel)))

theorem node_17 : Excluded a [3,5,4,6,8] :=
  branch_excluded a [3,5,4,6,8] (by decide)
    (fin9_cases _
      node_18
      node_19
      node_20
      (invalid_excluded a [3,5,4,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,6] (by decide +kernel))
      node_21
      (invalid_excluded a [3,5,4,6,8,8] (by decide +kernel)))

theorem node_12 : Excluded a [3,5,4,6] :=
  branch_excluded a [3,5,4,6] (by decide)
    (fin9_cases _
      node_13
      node_14
      node_15
      (invalid_excluded a [3,5,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,6] (by decide +kernel))
      node_16
      node_17)

theorem node_35 : Excluded a [3,5,4,7,0] :=
  source_excluded a [3,5,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_36 : Excluded a [3,5,4,7,1] :=
  source_excluded a [3,5,4,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_37 : Excluded a [3,5,4,7,2] :=
  source_excluded a [3,5,4,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_39 : Excluded a [3,5,4,7,6,0] :=
  source_excluded a [3,5,4,7,6,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_40 : Excluded a [3,5,4,7,6,1] :=
  source_excluded a [3,5,4,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_41 : Excluded a [3,5,4,7,6,2] :=
  source_excluded a [3,5,4,7,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_44 : Excluded a [3,5,4,7,6,8,0,1] :=
  predecessor_excluded a [3,5,4,7,6,8,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_46 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_46 : LosingRegion (edgeOf a b_46) 0 :=
  losingMask a b_46 0 1512339036535073631439872
    (by decide +kernel) (by decide +kernel)

theorem node_46 : Excluded a [3,5,4,7,6,8,0,2,1] :=
  losing_excluded a [3,5,4,7,6,8,0,2,1] (by decide) b_46 (by decide +kernel) 1 0 2 cert_46 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_46 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1512339036535073631439872 1 2; decide +kernel)

theorem node_45 : Excluded a [3,5,4,7,6,8,0,2] :=
  branch_excluded a [3,5,4,7,6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,7,6,8,0,2,0] (by decide +kernel))
      node_46
      (invalid_excluded a [3,5,4,7,6,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,2,8] (by decide +kernel)))

theorem node_43 : Excluded a [3,5,4,7,6,8,0] :=
  branch_excluded a [3,5,4,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,7,6,8,0,0] (by decide +kernel))
      node_44
      node_45
      (invalid_excluded a [3,5,4,7,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,0,8] (by decide +kernel)))

def b_49 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_49 : LosingRegion (edgeOf a b_49) 0 :=
  losingMask a b_49 0 1210109884669021633250304
    (by decide +kernel) (by decide +kernel)

theorem node_49 : Excluded a [3,5,4,7,6,8,1,0,2] :=
  losing_excluded a [3,5,4,7,6,8,1,0,2] (by decide) b_49 (by decide +kernel) 1 0 8 cert_49 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_49 1 0 ∧ 8 ≠ 1 ∧ maskRegion 1210109884669021633250304 1 8; decide +kernel)

theorem node_48 : Excluded a [3,5,4,7,6,8,1,0] :=
  branch_excluded a [3,5,4,7,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,7,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,0,1] (by decide +kernel))
      node_49
      (invalid_excluded a [3,5,4,7,6,8,1,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,0,8] (by decide +kernel)))

theorem node_50 : Excluded a [3,5,4,7,6,8,1,2] :=
  predecessor_excluded a [3,5,4,7,6,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_47 : Excluded a [3,5,4,7,6,8,1] :=
  branch_excluded a [3,5,4,7,6,8,1] (by decide)
    (fin9_cases _
      node_48
      (invalid_excluded a [3,5,4,7,6,8,1,1] (by decide +kernel))
      node_50
      (invalid_excluded a [3,5,4,7,6,8,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,1,8] (by decide +kernel)))

theorem node_52 : Excluded a [3,5,4,7,6,8,2,0] :=
  predecessor_excluded a [3,5,4,7,6,8,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_54 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_54 : LosingRegion (edgeOf a b_54) 0 :=
  losingMask a b_54 0 1212468762058140047934464
    (by decide +kernel) (by decide +kernel)

theorem node_54 : Excluded a [3,5,4,7,6,8,2,1,0] :=
  losing_excluded a [3,5,4,7,6,8,2,1,0] (by decide) b_54 (by decide +kernel) 1 0 6 cert_54 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_54 1 0 ∧ 6 ≠ 1 ∧ maskRegion 1212468762058140047934464 1 6; decide +kernel)

theorem node_53 : Excluded a [3,5,4,7,6,8,2,1] :=
  branch_excluded a [3,5,4,7,6,8,2,1] (by decide)
    (fin9_cases _
      node_54
      (invalid_excluded a [3,5,4,7,6,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,1,8] (by decide +kernel)))

theorem node_51 : Excluded a [3,5,4,7,6,8,2] :=
  branch_excluded a [3,5,4,7,6,8,2] (by decide)
    (fin9_cases _
      node_52
      node_53
      (invalid_excluded a [3,5,4,7,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,2,8] (by decide +kernel)))

theorem node_42 : Excluded a [3,5,4,7,6,8] :=
  branch_excluded a [3,5,4,7,6,8] (by decide)
    (fin9_cases _
      node_43
      node_47
      node_51
      (invalid_excluded a [3,5,4,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,8,8] (by decide +kernel)))

theorem node_38 : Excluded a [3,5,4,7,6] :=
  branch_excluded a [3,5,4,7,6] (by decide)
    (fin9_cases _
      node_39
      node_40
      node_41
      (invalid_excluded a [3,5,4,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,6,7] (by decide +kernel))
      node_42)

theorem node_55 : Excluded a [3,5,4,7,8] :=
  predecessor_excluded a [3,5,4,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_34 : Excluded a [3,5,4,7] :=
  branch_excluded a [3,5,4,7] (by decide)
    (fin9_cases _
      node_35
      node_36
      node_37
      (invalid_excluded a [3,5,4,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,5] (by decide +kernel))
      node_38
      (invalid_excluded a [3,5,4,7,7] (by decide +kernel))
      node_55)

theorem node_57 : Excluded a [3,5,4,8,0] :=
  source_excluded a [3,5,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_58 : Excluded a [3,5,4,8,1] :=
  source_excluded a [3,5,4,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_59 : Excluded a [3,5,4,8,2] :=
  source_excluded a [3,5,4,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_60 : Excluded a [3,5,4,8,6] :=
  predecessor_excluded a [3,5,4,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_62 : Excluded a [3,5,4,8,7,0] :=
  source_excluded a [3,5,4,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_63 : Excluded a [3,5,4,8,7,1] :=
  source_excluded a [3,5,4,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_64 : Excluded a [3,5,4,8,7,2] :=
  source_excluded a [3,5,4,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_67 : Excluded a [3,5,4,8,7,6,0,1] :=
  predecessor_excluded a [3,5,4,8,7,6,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_69 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 8
  | 4 => 7
  | 5 => 6
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_69 : LosingRegion (edgeOf a b_69) 0 :=
  losingMask a b_69 0 1512339031459766612329472
    (by decide +kernel) (by decide +kernel)

theorem node_69 : Excluded a [3,5,4,8,7,6,0,2,1] :=
  losing_excluded a [3,5,4,8,7,6,0,2,1] (by decide) b_69 (by decide +kernel) 1 0 7 cert_69 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_69 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1512339031459766612329472 1 7; decide +kernel)

theorem node_68 : Excluded a [3,5,4,8,7,6,0,2] :=
  branch_excluded a [3,5,4,8,7,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,8,7,6,0,2,0] (by decide +kernel))
      node_69
      (invalid_excluded a [3,5,4,8,7,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,2,8] (by decide +kernel)))

theorem node_66 : Excluded a [3,5,4,8,7,6,0] :=
  branch_excluded a [3,5,4,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,8,7,6,0,0] (by decide +kernel))
      node_67
      node_68
      (invalid_excluded a [3,5,4,8,7,6,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,0,8] (by decide +kernel)))

def b_72 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 8
  | 4 => 7
  | 5 => 6
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_72 : LosingRegion (edgeOf a b_72) 0 :=
  losingMask a b_72 0 1210109887465655228304384
    (by decide +kernel) (by decide +kernel)

theorem node_72 : Excluded a [3,5,4,8,7,6,1,0,2] :=
  losing_excluded a [3,5,4,8,7,6,1,0,2] (by decide) b_72 (by decide +kernel) 1 0 2 cert_72 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_72 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1210109887465655228304384 1 2; decide +kernel)

theorem node_71 : Excluded a [3,5,4,8,7,6,1,0] :=
  branch_excluded a [3,5,4,8,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,8,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,0,1] (by decide +kernel))
      node_72
      (invalid_excluded a [3,5,4,8,7,6,1,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,0,8] (by decide +kernel)))

theorem node_73 : Excluded a [3,5,4,8,7,6,1,2] :=
  predecessor_excluded a [3,5,4,8,7,6,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_70 : Excluded a [3,5,4,8,7,6,1] :=
  branch_excluded a [3,5,4,8,7,6,1] (by decide)
    (fin9_cases _
      node_71
      (invalid_excluded a [3,5,4,8,7,6,1,1] (by decide +kernel))
      node_73
      (invalid_excluded a [3,5,4,8,7,6,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,1,8] (by decide +kernel)))

theorem node_75 : Excluded a [3,5,4,8,7,6,2,0] :=
  predecessor_excluded a [3,5,4,8,7,6,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_77 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 8
  | 4 => 7
  | 5 => 6
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_77 : LosingRegion (edgeOf a b_77) 0 :=
  losingMask a b_77 0 1212468759815673198183424
    (by decide +kernel) (by decide +kernel)

theorem node_77 : Excluded a [3,5,4,8,7,6,2,1,0] :=
  losing_excluded a [3,5,4,8,7,6,2,1,0] (by decide) b_77 (by decide +kernel) 1 0 6 cert_77 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_77 1 0 ∧ 6 ≠ 1 ∧ maskRegion 1212468759815673198183424 1 6; decide +kernel)

theorem node_76 : Excluded a [3,5,4,8,7,6,2,1] :=
  branch_excluded a [3,5,4,8,7,6,2,1] (by decide)
    (fin9_cases _
      node_77
      (invalid_excluded a [3,5,4,8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,1,8] (by decide +kernel)))

theorem node_74 : Excluded a [3,5,4,8,7,6,2] :=
  branch_excluded a [3,5,4,8,7,6,2] (by decide)
    (fin9_cases _
      node_75
      node_76
      (invalid_excluded a [3,5,4,8,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,2,8] (by decide +kernel)))

theorem node_65 : Excluded a [3,5,4,8,7,6] :=
  branch_excluded a [3,5,4,8,7,6] (by decide)
    (fin9_cases _
      node_66
      node_70
      node_74
      (invalid_excluded a [3,5,4,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6,8] (by decide +kernel)))

theorem node_61 : Excluded a [3,5,4,8,7] :=
  branch_excluded a [3,5,4,8,7] (by decide)
    (fin9_cases _
      node_62
      node_63
      node_64
      (invalid_excluded a [3,5,4,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,5] (by decide +kernel))
      node_65
      (invalid_excluded a [3,5,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,8] (by decide +kernel)))

theorem node_56 : Excluded a [3,5,4,8] :=
  branch_excluded a [3,5,4,8] (by decide)
    (fin9_cases _
      node_57
      node_58
      node_59
      (invalid_excluded a [3,5,4,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,5] (by decide +kernel))
      node_60
      node_61
      (invalid_excluded a [3,5,4,8,8] (by decide +kernel)))

theorem node_8 : Excluded a [3,5,4] :=
  branch_excluded a [3,5,4] (by decide)
    (fin9_cases _
      node_9
      node_10
      node_11
      (invalid_excluded a [3,5,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,5] (by decide +kernel))
      node_12
      node_34
      node_56)

theorem node_80 : Excluded a [3,5,6,0,1] :=
  source_excluded a [3,5,6,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_81 : Excluded a [3,5,6,0,2] :=
  source_excluded a [3,5,6,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_83 : Excluded a [3,5,6,0,7,1] :=
  source_excluded a [3,5,6,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_84 : Excluded a [3,5,6,0,7,2] :=
  source_excluded a [3,5,6,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_85 : Excluded a [3,5,6,0,7,4] :=
  source_excluded a [3,5,6,0,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_86 : Excluded a [3,5,6,0,7,8] :=
  predecessor_excluded a [3,5,6,0,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_82 : Excluded a [3,5,6,0,7] :=
  branch_excluded a [3,5,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,6,0,7,0] (by decide +kernel))
      node_83
      node_84
      (invalid_excluded a [3,5,6,0,7,3] (by decide +kernel))
      node_85
      (invalid_excluded a [3,5,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,7,7] (by decide +kernel))
      node_86)

theorem node_88 : Excluded a [3,5,6,0,8,1] :=
  source_excluded a [3,5,6,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_89 : Excluded a [3,5,6,0,8,2] :=
  source_excluded a [3,5,6,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_90 : Excluded a [3,5,6,0,8,4] :=
  source_excluded a [3,5,6,0,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_92 : Excluded a [3,5,6,0,8,7,1] :=
  predecessor_excluded a [3,5,6,0,8,7,1] 3 1 2 6 (by decide) (by decide +kernel)

def b_95 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 6
  | 3 => 0
  | 4 => 8
  | 5 => 7
  | 6 => 2
  | 7 => 1
  | 8 => 4
  | _ => 0

def cert_95 : LosingRegion (edgeOf a b_95) 0 :=
  losingMask a b_95 0 2150513463195807993826304
    (by decide +kernel) (by decide +kernel)

theorem node_95 : Excluded a [3,5,6,0,8,7,2,1,4] :=
  losing_excluded a [3,5,6,0,8,7,2,1,4] (by decide) b_95 (by decide +kernel) 1 0 2 cert_95 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_95 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2150513463195807993826304 1 2; decide +kernel)

theorem node_94 : Excluded a [3,5,6,0,8,7,2,1] :=
  branch_excluded a [3,5,6,0,8,7,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,6,0,8,7,2,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,1,3] (by decide +kernel))
      node_95
      (invalid_excluded a [3,5,6,0,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,1,8] (by decide +kernel)))

theorem node_96 : Excluded a [3,5,6,0,8,7,2,4] :=
  source_excluded a [3,5,6,0,8,7,2,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_93 : Excluded a [3,5,6,0,8,7,2] :=
  branch_excluded a [3,5,6,0,8,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,6,0,8,7,2,0] (by decide +kernel))
      node_94
      (invalid_excluded a [3,5,6,0,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,3] (by decide +kernel))
      node_96
      (invalid_excluded a [3,5,6,0,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,2,8] (by decide +kernel)))

theorem node_97 : Excluded a [3,5,6,0,8,7,4] :=
  predecessor_excluded a [3,5,6,0,8,7,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_91 : Excluded a [3,5,6,0,8,7] :=
  branch_excluded a [3,5,6,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,6,0,8,7,0] (by decide +kernel))
      node_92
      node_93
      (invalid_excluded a [3,5,6,0,8,7,3] (by decide +kernel))
      node_97
      (invalid_excluded a [3,5,6,0,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,7,8] (by decide +kernel)))

theorem node_87 : Excluded a [3,5,6,0,8] :=
  branch_excluded a [3,5,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,6,0,8,0] (by decide +kernel))
      node_88
      node_89
      (invalid_excluded a [3,5,6,0,8,3] (by decide +kernel))
      node_90
      (invalid_excluded a [3,5,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,8,6] (by decide +kernel))
      node_91
      (invalid_excluded a [3,5,6,0,8,8] (by decide +kernel)))

theorem node_79 : Excluded a [3,5,6,0] :=
  branch_excluded a [3,5,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,6,0,0] (by decide +kernel))
      node_80
      node_81
      (invalid_excluded a [3,5,6,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,0,6] (by decide +kernel))
      node_82
      node_87)

theorem node_98 : Excluded a [3,5,6,1] :=
  source_excluded a [3,5,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_99 : Excluded a [3,5,6,2] :=
  predecessor_excluded a [3,5,6,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_101 : Excluded a [3,5,6,7,0] :=
  predecessor_excluded a [3,5,6,7,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_102 : Excluded a [3,5,6,7,1] :=
  source_excluded a [3,5,6,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_103 : Excluded a [3,5,6,7,2] :=
  source_excluded a [3,5,6,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_104 : Excluded a [3,5,6,7,8] :=
  predecessor_excluded a [3,5,6,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_100 : Excluded a [3,5,6,7] :=
  branch_excluded a [3,5,6,7] (by decide)
    (fin9_cases _
      node_101
      node_102
      node_103
      (invalid_excluded a [3,5,6,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,7,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,7,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,7,7] (by decide +kernel))
      node_104)

theorem node_106 : Excluded a [3,5,6,8,0] :=
  predecessor_excluded a [3,5,6,8,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_107 : Excluded a [3,5,6,8,1] :=
  source_excluded a [3,5,6,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_108 : Excluded a [3,5,6,8,2] :=
  source_excluded a [3,5,6,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_110 : Excluded a [3,5,6,8,7,0] :=
  source_excluded a [3,5,6,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_111 : Excluded a [3,5,6,8,7,1] :=
  source_excluded a [3,5,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_112 : Excluded a [3,5,6,8,7,2] :=
  source_excluded a [3,5,6,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_113 : Excluded a [3,5,6,8,7,4] :=
  source_excluded a [3,5,6,8,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_109 : Excluded a [3,5,6,8,7] :=
  branch_excluded a [3,5,6,8,7] (by decide)
    (fin9_cases _
      node_110
      node_111
      node_112
      (invalid_excluded a [3,5,6,8,7,3] (by decide +kernel))
      node_113
      (invalid_excluded a [3,5,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,7,8] (by decide +kernel)))

theorem node_105 : Excluded a [3,5,6,8] :=
  branch_excluded a [3,5,6,8] (by decide)
    (fin9_cases _
      node_106
      node_107
      node_108
      (invalid_excluded a [3,5,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,6] (by decide +kernel))
      node_109
      (invalid_excluded a [3,5,6,8,8] (by decide +kernel)))

theorem node_78 : Excluded a [3,5,6] :=
  branch_excluded a [3,5,6] (by decide)
    (fin9_cases _
      node_79
      node_98
      node_99
      (invalid_excluded a [3,5,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,6] (by decide +kernel))
      node_100
      node_105)

theorem node_116 : Excluded a [3,5,7,0,1] :=
  source_excluded a [3,5,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_117 : Excluded a [3,5,7,0,2] :=
  source_excluded a [3,5,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_119 : Excluded a [3,5,7,0,6,1] :=
  source_excluded a [3,5,7,0,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_120 : Excluded a [3,5,7,0,6,2] :=
  source_excluded a [3,5,7,0,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_121 : Excluded a [3,5,7,0,6,4] :=
  source_excluded a [3,5,7,0,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_124 : Excluded a [3,5,7,0,6,8,1,2] :=
  predecessor_excluded a [3,5,7,0,6,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_125 : Excluded a [3,5,7,0,6,8,1,4] :=
  predecessor_excluded a [3,5,7,0,6,8,1,4] 0 6 7 4 (by decide) (by decide +kernel)

theorem node_123 : Excluded a [3,5,7,0,6,8,1] :=
  branch_excluded a [3,5,7,0,6,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,6,8,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,1,1] (by decide +kernel))
      node_124
      (invalid_excluded a [3,5,7,0,6,8,1,3] (by decide +kernel))
      node_125
      (invalid_excluded a [3,5,7,0,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,1,8] (by decide +kernel)))

theorem node_126 : Excluded a [3,5,7,0,6,8,2] :=
  source_excluded a [3,5,7,0,6,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_128 : Excluded a [3,5,7,0,6,8,4,1] :=
  predecessor_excluded a [3,5,7,0,6,8,4,1] 3 1 2 7 (by decide) (by decide +kernel)

def b_130 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 0
  | 4 => 6
  | 5 => 8
  | 6 => 4
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_130 : LosingRegion (edgeOf a b_130) 0 :=
  losingMask a b_130 0 1847689424653181290286080
    (by decide +kernel) (by decide +kernel)

theorem node_130 : Excluded a [3,5,7,0,6,8,4,2,1] :=
  losing_excluded a [3,5,7,0,6,8,4,2,1] (by decide) b_130 (by decide +kernel) 1 0 2 cert_130 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_130 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1847689424653181290286080 1 2; decide +kernel)

theorem node_129 : Excluded a [3,5,7,0,6,8,4,2] :=
  branch_excluded a [3,5,7,0,6,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,6,8,4,2,0] (by decide +kernel))
      node_130
      (invalid_excluded a [3,5,7,0,6,8,4,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,2,8] (by decide +kernel)))

theorem node_127 : Excluded a [3,5,7,0,6,8,4] :=
  branch_excluded a [3,5,7,0,6,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,6,8,4,0] (by decide +kernel))
      node_128
      node_129
      (invalid_excluded a [3,5,7,0,6,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,4,8] (by decide +kernel)))

theorem node_122 : Excluded a [3,5,7,0,6,8] :=
  branch_excluded a [3,5,7,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,6,8,0] (by decide +kernel))
      node_123
      node_126
      (invalid_excluded a [3,5,7,0,6,8,3] (by decide +kernel))
      node_127
      (invalid_excluded a [3,5,7,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,8,8] (by decide +kernel)))

theorem node_118 : Excluded a [3,5,7,0,6] :=
  branch_excluded a [3,5,7,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,6,0] (by decide +kernel))
      node_119
      node_120
      (invalid_excluded a [3,5,7,0,6,3] (by decide +kernel))
      node_121
      (invalid_excluded a [3,5,7,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,6,7] (by decide +kernel))
      node_122)

theorem node_132 : Excluded a [3,5,7,0,8,1] :=
  source_excluded a [3,5,7,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_133 : Excluded a [3,5,7,0,8,2] :=
  source_excluded a [3,5,7,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_134 : Excluded a [3,5,7,0,8,4] :=
  source_excluded a [3,5,7,0,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_135 : Excluded a [3,5,7,0,8,6] :=
  predecessor_excluded a [3,5,7,0,8,6] 0 6 4 5 (by decide) (by decide +kernel)

theorem node_131 : Excluded a [3,5,7,0,8] :=
  branch_excluded a [3,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,0] (by decide +kernel))
      node_132
      node_133
      (invalid_excluded a [3,5,7,0,8,3] (by decide +kernel))
      node_134
      (invalid_excluded a [3,5,7,0,8,5] (by decide +kernel))
      node_135
      (invalid_excluded a [3,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,8] (by decide +kernel)))

theorem node_115 : Excluded a [3,5,7,0] :=
  branch_excluded a [3,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,0] (by decide +kernel))
      node_116
      node_117
      (invalid_excluded a [3,5,7,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,5] (by decide +kernel))
      node_118
      (invalid_excluded a [3,5,7,0,7] (by decide +kernel))
      node_131)

theorem node_136 : Excluded a [3,5,7,1] :=
  source_excluded a [3,5,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_137 : Excluded a [3,5,7,2] :=
  predecessor_excluded a [3,5,7,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_139 : Excluded a [3,5,7,6,0] :=
  predecessor_excluded a [3,5,7,6,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_140 : Excluded a [3,5,7,6,1] :=
  source_excluded a [3,5,7,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_141 : Excluded a [3,5,7,6,2] :=
  source_excluded a [3,5,7,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_143 : Excluded a [3,5,7,6,8,0] :=
  source_excluded a [3,5,7,6,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_144 : Excluded a [3,5,7,6,8,1] :=
  source_excluded a [3,5,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_145 : Excluded a [3,5,7,6,8,2] :=
  source_excluded a [3,5,7,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_146 : Excluded a [3,5,7,6,8,4] :=
  source_excluded a [3,5,7,6,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_142 : Excluded a [3,5,7,6,8] :=
  branch_excluded a [3,5,7,6,8] (by decide)
    (fin9_cases _
      node_143
      node_144
      node_145
      (invalid_excluded a [3,5,7,6,8,3] (by decide +kernel))
      node_146
      (invalid_excluded a [3,5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,8] (by decide +kernel)))

theorem node_138 : Excluded a [3,5,7,6] :=
  branch_excluded a [3,5,7,6] (by decide)
    (fin9_cases _
      node_139
      node_140
      node_141
      (invalid_excluded a [3,5,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,7] (by decide +kernel))
      node_142)

theorem node_148 : Excluded a [3,5,7,8,0] :=
  predecessor_excluded a [3,5,7,8,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_149 : Excluded a [3,5,7,8,1] :=
  source_excluded a [3,5,7,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_150 : Excluded a [3,5,7,8,2] :=
  source_excluded a [3,5,7,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_151 : Excluded a [3,5,7,8,6] :=
  predecessor_excluded a [3,5,7,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_147 : Excluded a [3,5,7,8] :=
  branch_excluded a [3,5,7,8] (by decide)
    (fin9_cases _
      node_148
      node_149
      node_150
      (invalid_excluded a [3,5,7,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,5] (by decide +kernel))
      node_151
      (invalid_excluded a [3,5,7,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,8] (by decide +kernel)))

theorem node_114 : Excluded a [3,5,7] :=
  branch_excluded a [3,5,7] (by decide)
    (fin9_cases _
      node_115
      node_136
      node_137
      (invalid_excluded a [3,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,5] (by decide +kernel))
      node_138
      (invalid_excluded a [3,5,7,7] (by decide +kernel))
      node_147)

theorem node_154 : Excluded a [3,5,8,0,1] :=
  source_excluded a [3,5,8,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_155 : Excluded a [3,5,8,0,2] :=
  source_excluded a [3,5,8,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_157 : Excluded a [3,5,8,0,6,1] :=
  source_excluded a [3,5,8,0,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_158 : Excluded a [3,5,8,0,6,2] :=
  source_excluded a [3,5,8,0,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_159 : Excluded a [3,5,8,0,6,4] :=
  source_excluded a [3,5,8,0,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_160 : Excluded a [3,5,8,0,6,7] :=
  predecessor_excluded a [3,5,8,0,6,7] 0 7 4 5 (by decide) (by decide +kernel)

theorem node_156 : Excluded a [3,5,8,0,6] :=
  branch_excluded a [3,5,8,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,0,6,0] (by decide +kernel))
      node_157
      node_158
      (invalid_excluded a [3,5,8,0,6,3] (by decide +kernel))
      node_159
      (invalid_excluded a [3,5,8,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,6,6] (by decide +kernel))
      node_160
      (invalid_excluded a [3,5,8,0,6,8] (by decide +kernel)))

theorem node_162 : Excluded a [3,5,8,0,7,1] :=
  source_excluded a [3,5,8,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_163 : Excluded a [3,5,8,0,7,2] :=
  source_excluded a [3,5,8,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_164 : Excluded a [3,5,8,0,7,4] :=
  source_excluded a [3,5,8,0,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_167 : Excluded a [3,5,8,0,7,6,1,2] :=
  source_excluded a [3,5,8,0,7,6,1,2] 7 0 2 (by decide) (by decide +kernel)

def b_169 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 8
  | 3 => 0
  | 4 => 7
  | 5 => 6
  | 6 => 1
  | 7 => 4
  | 8 => 2
  | _ => 0

def cert_169 : LosingRegion (edgeOf a b_169) 0 :=
  losingMask a b_169 0 1241462544943818227059712
    (by decide +kernel) (by decide +kernel)

theorem node_169 : Excluded a [3,5,8,0,7,6,1,4,2] :=
  losing_excluded a [3,5,8,0,7,6,1,4,2] (by decide) b_169 (by decide +kernel) 1 0 2 cert_169 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_169 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1241462544943818227059712 1 2; decide +kernel)

theorem node_168 : Excluded a [3,5,8,0,7,6,1,4] :=
  branch_excluded a [3,5,8,0,7,6,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,0,7,6,1,4,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,4,1] (by decide +kernel))
      node_169
      (invalid_excluded a [3,5,8,0,7,6,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,4,8] (by decide +kernel)))

theorem node_166 : Excluded a [3,5,8,0,7,6,1] :=
  branch_excluded a [3,5,8,0,7,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,0,7,6,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,1] (by decide +kernel))
      node_167
      (invalid_excluded a [3,5,8,0,7,6,1,3] (by decide +kernel))
      node_168
      (invalid_excluded a [3,5,8,0,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,1,8] (by decide +kernel)))

theorem node_170 : Excluded a [3,5,8,0,7,6,2] :=
  predecessor_excluded a [3,5,8,0,7,6,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_171 : Excluded a [3,5,8,0,7,6,4] :=
  source_excluded a [3,5,8,0,7,6,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_165 : Excluded a [3,5,8,0,7,6] :=
  branch_excluded a [3,5,8,0,7,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,0,7,6,0] (by decide +kernel))
      node_166
      node_170
      (invalid_excluded a [3,5,8,0,7,6,3] (by decide +kernel))
      node_171
      (invalid_excluded a [3,5,8,0,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,6,8] (by decide +kernel)))

theorem node_161 : Excluded a [3,5,8,0,7] :=
  branch_excluded a [3,5,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,0,7,0] (by decide +kernel))
      node_162
      node_163
      (invalid_excluded a [3,5,8,0,7,3] (by decide +kernel))
      node_164
      (invalid_excluded a [3,5,8,0,7,5] (by decide +kernel))
      node_165
      (invalid_excluded a [3,5,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,7,8] (by decide +kernel)))

theorem node_153 : Excluded a [3,5,8,0] :=
  branch_excluded a [3,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,0,0] (by decide +kernel))
      node_154
      node_155
      (invalid_excluded a [3,5,8,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,0,5] (by decide +kernel))
      node_156
      node_161
      (invalid_excluded a [3,5,8,0,8] (by decide +kernel)))

theorem node_172 : Excluded a [3,5,8,1] :=
  source_excluded a [3,5,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_173 : Excluded a [3,5,8,2] :=
  predecessor_excluded a [3,5,8,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_175 : Excluded a [3,5,8,6,0] :=
  predecessor_excluded a [3,5,8,6,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_176 : Excluded a [3,5,8,6,1] :=
  source_excluded a [3,5,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_177 : Excluded a [3,5,8,6,2] :=
  source_excluded a [3,5,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_178 : Excluded a [3,5,8,6,7] :=
  predecessor_excluded a [3,5,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_174 : Excluded a [3,5,8,6] :=
  branch_excluded a [3,5,8,6] (by decide)
    (fin9_cases _
      node_175
      node_176
      node_177
      (invalid_excluded a [3,5,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,6] (by decide +kernel))
      node_178
      (invalid_excluded a [3,5,8,6,8] (by decide +kernel)))

theorem node_180 : Excluded a [3,5,8,7,0] :=
  predecessor_excluded a [3,5,8,7,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_181 : Excluded a [3,5,8,7,1] :=
  source_excluded a [3,5,8,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_182 : Excluded a [3,5,8,7,2] :=
  source_excluded a [3,5,8,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_184 : Excluded a [3,5,8,7,6,0] :=
  source_excluded a [3,5,8,7,6,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_185 : Excluded a [3,5,8,7,6,1] :=
  source_excluded a [3,5,8,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_186 : Excluded a [3,5,8,7,6,2] :=
  source_excluded a [3,5,8,7,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_187 : Excluded a [3,5,8,7,6,4] :=
  source_excluded a [3,5,8,7,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_183 : Excluded a [3,5,8,7,6] :=
  branch_excluded a [3,5,8,7,6] (by decide)
    (fin9_cases _
      node_184
      node_185
      node_186
      (invalid_excluded a [3,5,8,7,6,3] (by decide +kernel))
      node_187
      (invalid_excluded a [3,5,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,6,8] (by decide +kernel)))

theorem node_179 : Excluded a [3,5,8,7] :=
  branch_excluded a [3,5,8,7] (by decide)
    (fin9_cases _
      node_180
      node_181
      node_182
      (invalid_excluded a [3,5,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,5] (by decide +kernel))
      node_183
      (invalid_excluded a [3,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,8] (by decide +kernel)))

theorem node_152 : Excluded a [3,5,8] :=
  branch_excluded a [3,5,8] (by decide)
    (fin9_cases _
      node_153
      node_172
      node_173
      (invalid_excluded a [3,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,5] (by decide +kernel))
      node_174
      node_179
      (invalid_excluded a [3,5,8,8] (by decide +kernel)))

theorem node_6 : Excluded a [3,5] :=
  branch_excluded a [3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,0] (by decide +kernel))
      node_7
      (invalid_excluded a [3,5,2] (by decide +kernel))
      (invalid_excluded a [3,5,3] (by decide +kernel))
      node_8
      (invalid_excluded a [3,5,5] (by decide +kernel))
      node_78
      node_114
      node_152)

theorem node_189 : Excluded a [3,6,1] :=
  source_excluded a [3,6,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_191 : Excluded a [3,6,4,0] :=
  source_excluded a [3,6,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_192 : Excluded a [3,6,4,1] :=
  source_excluded a [3,6,4,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_193 : Excluded a [3,6,4,2] :=
  source_excluded a [3,6,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_194 : Excluded a [3,6,4,5] :=
  source_excluded a [3,6,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_196 : Excluded a [3,6,4,7,0] :=
  source_excluded a [3,6,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_197 : Excluded a [3,6,4,7,1] :=
  predecessor_excluded a [3,6,4,7,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_199 : Excluded a [3,6,4,7,2,0] :=
  source_excluded a [3,6,4,7,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_200 : Excluded a [3,6,4,7,2,1] :=
  source_excluded a [3,6,4,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_202 : Excluded a [3,6,4,7,2,8,0] :=
  predecessor_excluded a [3,6,4,7,2,8,0] 3 0 1 6 (by decide) (by decide +kernel)

def b_205 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 6
  | 2 => 4
  | 3 => 7
  | 4 => 2
  | 5 => 8
  | 6 => 1
  | 7 => 0
  | 8 => 5
  | _ => 0

def cert_205 : LosingRegion (edgeOf a b_205) 0 :=
  losingMask a b_205 0 1521783764518221361710080
    (by decide +kernel) (by decide +kernel)

theorem node_205 : Excluded a [3,6,4,7,2,8,1,0,5] :=
  losing_excluded a [3,6,4,7,2,8,1,0,5] (by decide) b_205 (by decide +kernel) 3 0 6 cert_205 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_205 3 0 ∧ 6 ≠ 3 ∧ maskRegion 1521783764518221361710080 3 6; decide +kernel)

theorem node_204 : Excluded a [3,6,4,7,2,8,1,0] :=
  branch_excluded a [3,6,4,7,2,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,4,7,2,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,0,1] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,0,2] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,0,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,0,4] (by decide +kernel))
      node_205
      (invalid_excluded a [3,6,4,7,2,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,0,8] (by decide +kernel)))

theorem node_206 : Excluded a [3,6,4,7,2,8,1,5] :=
  source_excluded a [3,6,4,7,2,8,1,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_203 : Excluded a [3,6,4,7,2,8,1] :=
  branch_excluded a [3,6,4,7,2,8,1] (by decide)
    (fin9_cases _
      node_204
      (invalid_excluded a [3,6,4,7,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,2] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,4] (by decide +kernel))
      node_206
      (invalid_excluded a [3,6,4,7,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,8] (by decide +kernel)))

theorem node_207 : Excluded a [3,6,4,7,2,8,5] :=
  predecessor_excluded a [3,6,4,7,2,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_201 : Excluded a [3,6,4,7,2,8] :=
  branch_excluded a [3,6,4,7,2,8] (by decide)
    (fin9_cases _
      node_202
      node_203
      (invalid_excluded a [3,6,4,7,2,8,2] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,4] (by decide +kernel))
      node_207
      (invalid_excluded a [3,6,4,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,8] (by decide +kernel)))

theorem node_198 : Excluded a [3,6,4,7,2] :=
  branch_excluded a [3,6,4,7,2] (by decide)
    (fin9_cases _
      node_199
      node_200
      (invalid_excluded a [3,6,4,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,7] (by decide +kernel))
      node_201)

theorem node_208 : Excluded a [3,6,4,7,8] :=
  predecessor_excluded a [3,6,4,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_195 : Excluded a [3,6,4,7] :=
  branch_excluded a [3,6,4,7] (by decide)
    (fin9_cases _
      node_196
      node_197
      node_198
      (invalid_excluded a [3,6,4,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,7] (by decide +kernel))
      node_208)

theorem node_210 : Excluded a [3,6,4,8,0] :=
  source_excluded a [3,6,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_211 : Excluded a [3,6,4,8,1] :=
  predecessor_excluded a [3,6,4,8,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_213 : Excluded a [3,6,4,8,2,0] :=
  source_excluded a [3,6,4,8,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_214 : Excluded a [3,6,4,8,2,1] :=
  source_excluded a [3,6,4,8,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_215 : Excluded a [3,6,4,8,2,7] :=
  predecessor_excluded a [3,6,4,8,2,7] 0 8 5 3 (by decide) (by decide +kernel)

theorem node_212 : Excluded a [3,6,4,8,2] :=
  branch_excluded a [3,6,4,8,2] (by decide)
    (fin9_cases _
      node_213
      node_214
      (invalid_excluded a [3,6,4,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,2,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,2,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,2,6] (by decide +kernel))
      node_215
      (invalid_excluded a [3,6,4,8,2,8] (by decide +kernel)))

theorem node_217 : Excluded a [3,6,4,8,7,0] :=
  source_excluded a [3,6,4,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_218 : Excluded a [3,6,4,8,7,1] :=
  source_excluded a [3,6,4,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_219 : Excluded a [3,6,4,8,7,2] :=
  predecessor_excluded a [3,6,4,8,7,2] 0 4 5 2 (by decide) (by decide +kernel)

theorem node_216 : Excluded a [3,6,4,8,7] :=
  branch_excluded a [3,6,4,8,7] (by decide)
    (fin9_cases _
      node_217
      node_218
      node_219
      (invalid_excluded a [3,6,4,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,8] (by decide +kernel)))

theorem node_209 : Excluded a [3,6,4,8] :=
  branch_excluded a [3,6,4,8] (by decide)
    (fin9_cases _
      node_210
      node_211
      node_212
      (invalid_excluded a [3,6,4,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,6] (by decide +kernel))
      node_216
      (invalid_excluded a [3,6,4,8,8] (by decide +kernel)))

theorem node_190 : Excluded a [3,6,4] :=
  branch_excluded a [3,6,4] (by decide)
    (fin9_cases _
      node_191
      node_192
      node_193
      (invalid_excluded a [3,6,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,4] (by decide +kernel))
      node_194
      (invalid_excluded a [3,6,4,6] (by decide +kernel))
      node_195
      node_209)

theorem node_220 : Excluded a [3,6,5] :=
  predecessor_excluded a [3,6,5] 1 3 2 0 (by decide) (by decide +kernel)

theorem node_221 : Excluded a [3,6,7] :=
  predecessor_excluded a [3,6,7] 0 7 1 2 (by decide) (by decide +kernel)

theorem node_224 : Excluded a [3,6,8,0,1] :=
  predecessor_excluded a [3,6,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_226 : Excluded a [3,6,8,0,2,1] :=
  source_excluded a [3,6,8,0,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_227 : Excluded a [3,6,8,0,2,4] :=
  source_excluded a [3,6,8,0,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_230 : Excluded a [3,6,8,0,2,7,1,4] :=
  predecessor_excluded a [3,6,8,0,2,7,1,4] 0 4 5 7 (by decide) (by decide +kernel)

def b_232 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 6
  | 2 => 8
  | 3 => 0
  | 4 => 2
  | 5 => 7
  | 6 => 1
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_232 : LosingRegion (edgeOf a b_232) 0 :=
  losingMask a b_232 0 1352346355913495631899648
    (by decide +kernel) (by decide +kernel)

theorem node_232 : Excluded a [3,6,8,0,2,7,1,5,4] :=
  losing_excluded a [3,6,8,0,2,7,1,5,4] (by decide) b_232 (by decide +kernel) 1 0 2 cert_232 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_232 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1352346355913495631899648 1 2; decide +kernel)

theorem node_231 : Excluded a [3,6,8,0,2,7,1,5] :=
  branch_excluded a [3,6,8,0,2,7,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,0,2,7,1,5,0] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,5,1] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,5,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,5,3] (by decide +kernel))
      node_232
      (invalid_excluded a [3,6,8,0,2,7,1,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,5,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,5,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,5,8] (by decide +kernel)))

theorem node_229 : Excluded a [3,6,8,0,2,7,1] :=
  branch_excluded a [3,6,8,0,2,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,0,2,7,1,0] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,3] (by decide +kernel))
      node_230
      node_231
      (invalid_excluded a [3,6,8,0,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,1,8] (by decide +kernel)))

theorem node_234 : Excluded a [3,6,8,0,2,7,4,1] :=
  predecessor_excluded a [3,6,8,0,2,7,4,1] 0 6 7 1 (by decide) (by decide +kernel)

theorem node_235 : Excluded a [3,6,8,0,2,7,4,5] :=
  predecessor_excluded a [3,6,8,0,2,7,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_233 : Excluded a [3,6,8,0,2,7,4] :=
  branch_excluded a [3,6,8,0,2,7,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,0,2,7,4,0] (by decide +kernel))
      node_234
      (invalid_excluded a [3,6,8,0,2,7,4,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,4,4] (by decide +kernel))
      node_235
      (invalid_excluded a [3,6,8,0,2,7,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,4,8] (by decide +kernel)))

theorem node_236 : Excluded a [3,6,8,0,2,7,5] :=
  source_excluded a [3,6,8,0,2,7,5] 6 0 5 (by decide) (by decide +kernel)

theorem node_228 : Excluded a [3,6,8,0,2,7] :=
  branch_excluded a [3,6,8,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,0,2,7,0] (by decide +kernel))
      node_229
      (invalid_excluded a [3,6,8,0,2,7,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,3] (by decide +kernel))
      node_233
      node_236
      (invalid_excluded a [3,6,8,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,7,8] (by decide +kernel)))

theorem node_225 : Excluded a [3,6,8,0,2] :=
  branch_excluded a [3,6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,0,2,0] (by decide +kernel))
      node_226
      (invalid_excluded a [3,6,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,3] (by decide +kernel))
      node_227
      (invalid_excluded a [3,6,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,2,6] (by decide +kernel))
      node_228
      (invalid_excluded a [3,6,8,0,2,8] (by decide +kernel)))

theorem node_238 : Excluded a [3,6,8,0,7,1] :=
  source_excluded a [3,6,8,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_239 : Excluded a [3,6,8,0,7,2] :=
  predecessor_excluded a [3,6,8,0,7,2] 1 0 5 3 (by decide) (by decide +kernel)

theorem node_240 : Excluded a [3,6,8,0,7,4] :=
  source_excluded a [3,6,8,0,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_237 : Excluded a [3,6,8,0,7] :=
  branch_excluded a [3,6,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,0,7,0] (by decide +kernel))
      node_238
      node_239
      (invalid_excluded a [3,6,8,0,7,3] (by decide +kernel))
      node_240
      (invalid_excluded a [3,6,8,0,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,7,8] (by decide +kernel)))

theorem node_223 : Excluded a [3,6,8,0] :=
  branch_excluded a [3,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,0,0] (by decide +kernel))
      node_224
      node_225
      (invalid_excluded a [3,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,0,6] (by decide +kernel))
      node_237
      (invalid_excluded a [3,6,8,0,8] (by decide +kernel)))

theorem node_241 : Excluded a [3,6,8,1] :=
  source_excluded a [3,6,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_242 : Excluded a [3,6,8,2] :=
  predecessor_excluded a [3,6,8,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_243 : Excluded a [3,6,8,5] :=
  source_excluded a [3,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_245 : Excluded a [3,6,8,7,0] :=
  predecessor_excluded a [3,6,8,7,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_247 : Excluded a [3,6,8,7,1,0] :=
  source_excluded a [3,6,8,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_248 : Excluded a [3,6,8,7,1,2] :=
  predecessor_excluded a [3,6,8,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_249 : Excluded a [3,6,8,7,1,4] :=
  source_excluded a [3,6,8,7,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_246 : Excluded a [3,6,8,7,1] :=
  branch_excluded a [3,6,8,7,1] (by decide)
    (fin9_cases _
      node_247
      (invalid_excluded a [3,6,8,7,1,1] (by decide +kernel))
      node_248
      (invalid_excluded a [3,6,8,7,1,3] (by decide +kernel))
      node_249
      (invalid_excluded a [3,6,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,8] (by decide +kernel)))

theorem node_251 : Excluded a [3,6,8,7,2,0] :=
  source_excluded a [3,6,8,7,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_252 : Excluded a [3,6,8,7,2,1] :=
  source_excluded a [3,6,8,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_253 : Excluded a [3,6,8,7,2,4] :=
  source_excluded a [3,6,8,7,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_250 : Excluded a [3,6,8,7,2] :=
  branch_excluded a [3,6,8,7,2] (by decide)
    (fin9_cases _
      node_251
      node_252
      (invalid_excluded a [3,6,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,3] (by decide +kernel))
      node_253
      (invalid_excluded a [3,6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,8] (by decide +kernel)))

theorem node_244 : Excluded a [3,6,8,7] :=
  branch_excluded a [3,6,8,7] (by decide)
    (fin9_cases _
      node_245
      node_246
      node_250
      (invalid_excluded a [3,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,8] (by decide +kernel)))

theorem node_222 : Excluded a [3,6,8] :=
  branch_excluded a [3,6,8] (by decide)
    (fin9_cases _
      node_223
      node_241
      node_242
      (invalid_excluded a [3,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,4] (by decide +kernel))
      node_243
      (invalid_excluded a [3,6,8,6] (by decide +kernel))
      node_244
      (invalid_excluded a [3,6,8,8] (by decide +kernel)))

theorem node_188 : Excluded a [3,6] :=
  branch_excluded a [3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,0] (by decide +kernel))
      node_189
      (invalid_excluded a [3,6,2] (by decide +kernel))
      (invalid_excluded a [3,6,3] (by decide +kernel))
      node_190
      node_220
      (invalid_excluded a [3,6,6] (by decide +kernel))
      node_221
      node_222)

theorem node_255 : Excluded a [3,7,1] :=
  source_excluded a [3,7,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_257 : Excluded a [3,7,4,0] :=
  source_excluded a [3,7,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_258 : Excluded a [3,7,4,1] :=
  source_excluded a [3,7,4,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_259 : Excluded a [3,7,4,2] :=
  source_excluded a [3,7,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_260 : Excluded a [3,7,4,5] :=
  source_excluded a [3,7,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_262 : Excluded a [3,7,4,6,0] :=
  source_excluded a [3,7,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_263 : Excluded a [3,7,4,6,1] :=
  predecessor_excluded a [3,7,4,6,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_265 : Excluded a [3,7,4,6,2,0] :=
  source_excluded a [3,7,4,6,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_266 : Excluded a [3,7,4,6,2,1] :=
  source_excluded a [3,7,4,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_267 : Excluded a [3,7,4,6,2,8] :=
  predecessor_excluded a [3,7,4,6,2,8] 0 6 5 3 (by decide) (by decide +kernel)

theorem node_264 : Excluded a [3,7,4,6,2] :=
  branch_excluded a [3,7,4,6,2] (by decide)
    (fin9_cases _
      node_265
      node_266
      (invalid_excluded a [3,7,4,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,7] (by decide +kernel))
      node_267)

theorem node_269 : Excluded a [3,7,4,6,8,0] :=
  source_excluded a [3,7,4,6,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_270 : Excluded a [3,7,4,6,8,1] :=
  source_excluded a [3,7,4,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_271 : Excluded a [3,7,4,6,8,2] :=
  predecessor_excluded a [3,7,4,6,8,2] 0 4 5 2 (by decide) (by decide +kernel)

theorem node_268 : Excluded a [3,7,4,6,8] :=
  branch_excluded a [3,7,4,6,8] (by decide)
    (fin9_cases _
      node_269
      node_270
      node_271
      (invalid_excluded a [3,7,4,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,8] (by decide +kernel)))

theorem node_261 : Excluded a [3,7,4,6] :=
  branch_excluded a [3,7,4,6] (by decide)
    (fin9_cases _
      node_262
      node_263
      node_264
      (invalid_excluded a [3,7,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,7] (by decide +kernel))
      node_268)

theorem node_273 : Excluded a [3,7,4,8,0] :=
  source_excluded a [3,7,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_274 : Excluded a [3,7,4,8,1] :=
  predecessor_excluded a [3,7,4,8,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_276 : Excluded a [3,7,4,8,2,0] :=
  source_excluded a [3,7,4,8,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_277 : Excluded a [3,7,4,8,2,1] :=
  source_excluded a [3,7,4,8,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_280 : Excluded a [3,7,4,8,2,6,0,1] :=
  predecessor_excluded a [3,7,4,8,2,6,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_281 : Excluded a [3,7,4,8,2,6,0,5] :=
  predecessor_excluded a [3,7,4,8,2,6,0,5] 0 6 7 5 (by decide) (by decide +kernel)

theorem node_279 : Excluded a [3,7,4,8,2,6,0] :=
  branch_excluded a [3,7,4,8,2,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,4,8,2,6,0,0] (by decide +kernel))
      node_280
      (invalid_excluded a [3,7,4,8,2,6,0,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,0,4] (by decide +kernel))
      node_281
      (invalid_excluded a [3,7,4,8,2,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,0,8] (by decide +kernel)))

theorem node_282 : Excluded a [3,7,4,8,2,6,1] :=
  source_excluded a [3,7,4,8,2,6,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_284 : Excluded a [3,7,4,8,2,6,5,0] :=
  predecessor_excluded a [3,7,4,8,2,6,5,0] 3 0 1 7 (by decide) (by decide +kernel)

def b_286 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 4
  | 3 => 8
  | 4 => 2
  | 5 => 6
  | 6 => 5
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_286 : LosingRegion (edgeOf a b_286) 0 :=
  losingMask a b_286 0 1210109914017039972828160
    (by decide +kernel) (by decide +kernel)

theorem node_286 : Excluded a [3,7,4,8,2,6,5,1,0] :=
  losing_excluded a [3,7,4,8,2,6,5,1,0] (by decide) b_286 (by decide +kernel) 3 0 7 cert_286 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_286 3 0 ∧ 7 ≠ 3 ∧ maskRegion 1210109914017039972828160 3 7; decide +kernel)

theorem node_285 : Excluded a [3,7,4,8,2,6,5,1] :=
  branch_excluded a [3,7,4,8,2,6,5,1] (by decide)
    (fin9_cases _
      node_286
      (invalid_excluded a [3,7,4,8,2,6,5,1,1] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,1,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,1,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,1,8] (by decide +kernel)))

theorem node_283 : Excluded a [3,7,4,8,2,6,5] :=
  branch_excluded a [3,7,4,8,2,6,5] (by decide)
    (fin9_cases _
      node_284
      node_285
      (invalid_excluded a [3,7,4,8,2,6,5,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,5,8] (by decide +kernel)))

theorem node_278 : Excluded a [3,7,4,8,2,6] :=
  branch_excluded a [3,7,4,8,2,6] (by decide)
    (fin9_cases _
      node_279
      node_282
      (invalid_excluded a [3,7,4,8,2,6,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,4] (by decide +kernel))
      node_283
      (invalid_excluded a [3,7,4,8,2,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6,8] (by decide +kernel)))

theorem node_275 : Excluded a [3,7,4,8,2] :=
  branch_excluded a [3,7,4,8,2] (by decide)
    (fin9_cases _
      node_276
      node_277
      (invalid_excluded a [3,7,4,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,5] (by decide +kernel))
      node_278
      (invalid_excluded a [3,7,4,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,8] (by decide +kernel)))

theorem node_287 : Excluded a [3,7,4,8,6] :=
  predecessor_excluded a [3,7,4,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_272 : Excluded a [3,7,4,8] :=
  branch_excluded a [3,7,4,8] (by decide)
    (fin9_cases _
      node_273
      node_274
      node_275
      (invalid_excluded a [3,7,4,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,5] (by decide +kernel))
      node_287
      (invalid_excluded a [3,7,4,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,8] (by decide +kernel)))

theorem node_256 : Excluded a [3,7,4] :=
  branch_excluded a [3,7,4] (by decide)
    (fin9_cases _
      node_257
      node_258
      node_259
      (invalid_excluded a [3,7,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,4] (by decide +kernel))
      node_260
      node_261
      (invalid_excluded a [3,7,4,7] (by decide +kernel))
      node_272)

theorem node_288 : Excluded a [3,7,5] :=
  predecessor_excluded a [3,7,5] 1 3 2 0 (by decide) (by decide +kernel)

theorem node_291 : Excluded a [3,7,6,0,1] :=
  predecessor_excluded a [3,7,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_293 : Excluded a [3,7,6,0,2,1] :=
  source_excluded a [3,7,6,0,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_294 : Excluded a [3,7,6,0,2,4] :=
  source_excluded a [3,7,6,0,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_296 : Excluded a [3,7,6,0,2,8,1] :=
  source_excluded a [3,7,6,0,2,8,1] 6 0 1 (by decide) (by decide +kernel)

def b_299 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 6
  | 3 => 0
  | 4 => 2
  | 5 => 8
  | 6 => 4
  | 7 => 1
  | 8 => 5
  | _ => 0

def cert_299 : LosingRegion (edgeOf a b_299) 0 :=
  losingMask a b_299 0 1499048681831290759031808
    (by decide +kernel) (by decide +kernel)

theorem node_299 : Excluded a [3,7,6,0,2,8,4,1,5] :=
  losing_excluded a [3,7,6,0,2,8,4,1,5] (by decide) b_299 (by decide +kernel) 1 0 2 cert_299 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_299 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1499048681831290759031808 1 2; decide +kernel)

theorem node_298 : Excluded a [3,7,6,0,2,8,4,1] :=
  branch_excluded a [3,7,6,0,2,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,2,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,1,4] (by decide +kernel))
      node_299
      (invalid_excluded a [3,7,6,0,2,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,1,8] (by decide +kernel)))

theorem node_300 : Excluded a [3,7,6,0,2,8,4,5] :=
  source_excluded a [3,7,6,0,2,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_297 : Excluded a [3,7,6,0,2,8,4] :=
  branch_excluded a [3,7,6,0,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,2,8,4,0] (by decide +kernel))
      node_298
      (invalid_excluded a [3,7,6,0,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,4] (by decide +kernel))
      node_300
      (invalid_excluded a [3,7,6,0,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,4,8] (by decide +kernel)))

theorem node_301 : Excluded a [3,7,6,0,2,8,5] :=
  predecessor_excluded a [3,7,6,0,2,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_295 : Excluded a [3,7,6,0,2,8] :=
  branch_excluded a [3,7,6,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,2,8,0] (by decide +kernel))
      node_296
      (invalid_excluded a [3,7,6,0,2,8,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,3] (by decide +kernel))
      node_297
      node_301
      (invalid_excluded a [3,7,6,0,2,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,8,8] (by decide +kernel)))

theorem node_292 : Excluded a [3,7,6,0,2] :=
  branch_excluded a [3,7,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,2,0] (by decide +kernel))
      node_293
      (invalid_excluded a [3,7,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,3] (by decide +kernel))
      node_294
      (invalid_excluded a [3,7,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,2,7] (by decide +kernel))
      node_295)

theorem node_303 : Excluded a [3,7,6,0,8,1] :=
  source_excluded a [3,7,6,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_304 : Excluded a [3,7,6,0,8,2] :=
  predecessor_excluded a [3,7,6,0,8,2] 1 0 5 3 (by decide) (by decide +kernel)

theorem node_305 : Excluded a [3,7,6,0,8,4] :=
  source_excluded a [3,7,6,0,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_302 : Excluded a [3,7,6,0,8] :=
  branch_excluded a [3,7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,8,0] (by decide +kernel))
      node_303
      node_304
      (invalid_excluded a [3,7,6,0,8,3] (by decide +kernel))
      node_305
      (invalid_excluded a [3,7,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,8] (by decide +kernel)))

theorem node_290 : Excluded a [3,7,6,0] :=
  branch_excluded a [3,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,0] (by decide +kernel))
      node_291
      node_292
      (invalid_excluded a [3,7,6,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,7] (by decide +kernel))
      node_302)

theorem node_306 : Excluded a [3,7,6,1] :=
  source_excluded a [3,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_307 : Excluded a [3,7,6,2] :=
  predecessor_excluded a [3,7,6,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_308 : Excluded a [3,7,6,5] :=
  source_excluded a [3,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_310 : Excluded a [3,7,6,8,0] :=
  predecessor_excluded a [3,7,6,8,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_312 : Excluded a [3,7,6,8,1,0] :=
  source_excluded a [3,7,6,8,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_313 : Excluded a [3,7,6,8,1,2] :=
  predecessor_excluded a [3,7,6,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_314 : Excluded a [3,7,6,8,1,4] :=
  source_excluded a [3,7,6,8,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_311 : Excluded a [3,7,6,8,1] :=
  branch_excluded a [3,7,6,8,1] (by decide)
    (fin9_cases _
      node_312
      (invalid_excluded a [3,7,6,8,1,1] (by decide +kernel))
      node_313
      (invalid_excluded a [3,7,6,8,1,3] (by decide +kernel))
      node_314
      (invalid_excluded a [3,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,8] (by decide +kernel)))

theorem node_316 : Excluded a [3,7,6,8,2,0] :=
  source_excluded a [3,7,6,8,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_317 : Excluded a [3,7,6,8,2,1] :=
  source_excluded a [3,7,6,8,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_318 : Excluded a [3,7,6,8,2,4] :=
  source_excluded a [3,7,6,8,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_315 : Excluded a [3,7,6,8,2] :=
  branch_excluded a [3,7,6,8,2] (by decide)
    (fin9_cases _
      node_316
      node_317
      (invalid_excluded a [3,7,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,2,3] (by decide +kernel))
      node_318
      (invalid_excluded a [3,7,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,2,8] (by decide +kernel)))

theorem node_309 : Excluded a [3,7,6,8] :=
  branch_excluded a [3,7,6,8] (by decide)
    (fin9_cases _
      node_310
      node_311
      node_315
      (invalid_excluded a [3,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,8] (by decide +kernel)))

theorem node_289 : Excluded a [3,7,6] :=
  branch_excluded a [3,7,6] (by decide)
    (fin9_cases _
      node_290
      node_306
      node_307
      (invalid_excluded a [3,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,4] (by decide +kernel))
      node_308
      (invalid_excluded a [3,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,7] (by decide +kernel))
      node_309)

theorem node_319 : Excluded a [3,7,8] :=
  predecessor_excluded a [3,7,8] 0 8 1 2 (by decide) (by decide +kernel)

theorem node_254 : Excluded a [3,7] :=
  branch_excluded a [3,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,0] (by decide +kernel))
      node_255
      (invalid_excluded a [3,7,2] (by decide +kernel))
      (invalid_excluded a [3,7,3] (by decide +kernel))
      node_256
      node_288
      node_289
      (invalid_excluded a [3,7,7] (by decide +kernel))
      node_319)

theorem node_321 : Excluded a [3,8,1] :=
  source_excluded a [3,8,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_323 : Excluded a [3,8,4,0] :=
  source_excluded a [3,8,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_324 : Excluded a [3,8,4,1] :=
  source_excluded a [3,8,4,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_325 : Excluded a [3,8,4,2] :=
  source_excluded a [3,8,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_326 : Excluded a [3,8,4,5] :=
  source_excluded a [3,8,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_328 : Excluded a [3,8,4,6,0] :=
  source_excluded a [3,8,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_329 : Excluded a [3,8,4,6,1] :=
  predecessor_excluded a [3,8,4,6,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_331 : Excluded a [3,8,4,6,2,0] :=
  source_excluded a [3,8,4,6,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_332 : Excluded a [3,8,4,6,2,1] :=
  source_excluded a [3,8,4,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_335 : Excluded a [3,8,4,6,2,7,0,1] :=
  source_excluded a [3,8,4,6,2,7,0,1] 7 0 1 (by decide) (by decide +kernel)

def b_337 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 4
  | 3 => 6
  | 4 => 2
  | 5 => 7
  | 6 => 0
  | 7 => 5
  | 8 => 1
  | _ => 0

def cert_337 : LosingRegion (edgeOf a b_337) 0 :=
  losingMask a b_337 0 1212487208886158893253632
    (by decide +kernel) (by decide +kernel)

theorem node_337 : Excluded a [3,8,4,6,2,7,0,5,1] :=
  losing_excluded a [3,8,4,6,2,7,0,5,1] (by decide) b_337 (by decide +kernel) 3 0 8 cert_337 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_337 3 0 ∧ 8 ≠ 3 ∧ maskRegion 1212487208886158893253632 3 8; decide +kernel)

theorem node_336 : Excluded a [3,8,4,6,2,7,0,5] :=
  branch_excluded a [3,8,4,6,2,7,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,4,6,2,7,0,5,0] (by decide +kernel))
      node_337
      (invalid_excluded a [3,8,4,6,2,7,0,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,5,6] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,5,8] (by decide +kernel)))

theorem node_334 : Excluded a [3,8,4,6,2,7,0] :=
  branch_excluded a [3,8,4,6,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,4,6,2,7,0,0] (by decide +kernel))
      node_335
      (invalid_excluded a [3,8,4,6,2,7,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,4] (by decide +kernel))
      node_336
      (invalid_excluded a [3,8,4,6,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,0,8] (by decide +kernel)))

theorem node_338 : Excluded a [3,8,4,6,2,7,1] :=
  predecessor_excluded a [3,8,4,6,2,7,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_339 : Excluded a [3,8,4,6,2,7,5] :=
  source_excluded a [3,8,4,6,2,7,5] 6 0 5 (by decide) (by decide +kernel)

theorem node_333 : Excluded a [3,8,4,6,2,7] :=
  branch_excluded a [3,8,4,6,2,7] (by decide)
    (fin9_cases _
      node_334
      node_338
      (invalid_excluded a [3,8,4,6,2,7,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,4] (by decide +kernel))
      node_339
      (invalid_excluded a [3,8,4,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,7,8] (by decide +kernel)))

theorem node_330 : Excluded a [3,8,4,6,2] :=
  branch_excluded a [3,8,4,6,2] (by decide)
    (fin9_cases _
      node_331
      node_332
      (invalid_excluded a [3,8,4,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,6] (by decide +kernel))
      node_333
      (invalid_excluded a [3,8,4,6,2,8] (by decide +kernel)))

theorem node_340 : Excluded a [3,8,4,6,7] :=
  predecessor_excluded a [3,8,4,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_327 : Excluded a [3,8,4,6] :=
  branch_excluded a [3,8,4,6] (by decide)
    (fin9_cases _
      node_328
      node_329
      node_330
      (invalid_excluded a [3,8,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,6] (by decide +kernel))
      node_340
      (invalid_excluded a [3,8,4,6,8] (by decide +kernel)))

theorem node_342 : Excluded a [3,8,4,7,0] :=
  source_excluded a [3,8,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_343 : Excluded a [3,8,4,7,1] :=
  predecessor_excluded a [3,8,4,7,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_345 : Excluded a [3,8,4,7,2,0] :=
  source_excluded a [3,8,4,7,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_346 : Excluded a [3,8,4,7,2,1] :=
  source_excluded a [3,8,4,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_347 : Excluded a [3,8,4,7,2,6] :=
  predecessor_excluded a [3,8,4,7,2,6] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_344 : Excluded a [3,8,4,7,2] :=
  branch_excluded a [3,8,4,7,2] (by decide)
    (fin9_cases _
      node_345
      node_346
      (invalid_excluded a [3,8,4,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,5] (by decide +kernel))
      node_347
      (invalid_excluded a [3,8,4,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,8] (by decide +kernel)))

theorem node_349 : Excluded a [3,8,4,7,6,0] :=
  source_excluded a [3,8,4,7,6,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_350 : Excluded a [3,8,4,7,6,1] :=
  source_excluded a [3,8,4,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_351 : Excluded a [3,8,4,7,6,2] :=
  predecessor_excluded a [3,8,4,7,6,2] 0 4 5 2 (by decide) (by decide +kernel)

theorem node_348 : Excluded a [3,8,4,7,6] :=
  branch_excluded a [3,8,4,7,6] (by decide)
    (fin9_cases _
      node_349
      node_350
      node_351
      (invalid_excluded a [3,8,4,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,6,8] (by decide +kernel)))

theorem node_341 : Excluded a [3,8,4,7] :=
  branch_excluded a [3,8,4,7] (by decide)
    (fin9_cases _
      node_342
      node_343
      node_344
      (invalid_excluded a [3,8,4,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,5] (by decide +kernel))
      node_348
      (invalid_excluded a [3,8,4,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,8] (by decide +kernel)))

theorem node_322 : Excluded a [3,8,4] :=
  branch_excluded a [3,8,4] (by decide)
    (fin9_cases _
      node_323
      node_324
      node_325
      (invalid_excluded a [3,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,4] (by decide +kernel))
      node_326
      node_327
      node_341
      (invalid_excluded a [3,8,4,8] (by decide +kernel)))

theorem node_352 : Excluded a [3,8,5] :=
  predecessor_excluded a [3,8,5] 1 3 2 0 (by decide) (by decide +kernel)

theorem node_353 : Excluded a [3,8,6] :=
  predecessor_excluded a [3,8,6] 0 6 1 2 (by decide) (by decide +kernel)

theorem node_356 : Excluded a [3,8,7,0,1] :=
  predecessor_excluded a [3,8,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_358 : Excluded a [3,8,7,0,2,1] :=
  source_excluded a [3,8,7,0,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_359 : Excluded a [3,8,7,0,2,4] :=
  source_excluded a [3,8,7,0,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_361 : Excluded a [3,8,7,0,2,6,1] :=
  predecessor_excluded a [3,8,7,0,2,6,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_362 : Excluded a [3,8,7,0,2,6,4] :=
  predecessor_excluded a [3,8,7,0,2,6,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_364 : Excluded a [3,8,7,0,2,6,5,1] :=
  source_excluded a [3,8,7,0,2,6,5,1] 7 0 1 (by decide) (by decide +kernel)

def b_366 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 7
  | 3 => 0
  | 4 => 2
  | 5 => 6
  | 6 => 5
  | 7 => 4
  | 8 => 1
  | _ => 0

def cert_366 : LosingRegion (edgeOf a b_366) 0 :=
  losingMask a b_366 0 1961241636416474223488000
    (by decide +kernel) (by decide +kernel)

theorem node_366 : Excluded a [3,8,7,0,2,6,5,4,1] :=
  losing_excluded a [3,8,7,0,2,6,5,4,1] (by decide) b_366 (by decide +kernel) 1 0 2 cert_366 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_366 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1961241636416474223488000 1 2; decide +kernel)

theorem node_365 : Excluded a [3,8,7,0,2,6,5,4] :=
  branch_excluded a [3,8,7,0,2,6,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,6,5,4,0] (by decide +kernel))
      node_366
      (invalid_excluded a [3,8,7,0,2,6,5,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,4,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,4,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,4,8] (by decide +kernel)))

theorem node_363 : Excluded a [3,8,7,0,2,6,5] :=
  branch_excluded a [3,8,7,0,2,6,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,6,5,0] (by decide +kernel))
      node_364
      (invalid_excluded a [3,8,7,0,2,6,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,3] (by decide +kernel))
      node_365
      (invalid_excluded a [3,8,7,0,2,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,5,8] (by decide +kernel)))

theorem node_360 : Excluded a [3,8,7,0,2,6] :=
  branch_excluded a [3,8,7,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,6,0] (by decide +kernel))
      node_361
      (invalid_excluded a [3,8,7,0,2,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,3] (by decide +kernel))
      node_362
      node_363
      (invalid_excluded a [3,8,7,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6,8] (by decide +kernel)))

theorem node_357 : Excluded a [3,8,7,0,2] :=
  branch_excluded a [3,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,0] (by decide +kernel))
      node_358
      (invalid_excluded a [3,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,3] (by decide +kernel))
      node_359
      (invalid_excluded a [3,8,7,0,2,5] (by decide +kernel))
      node_360
      (invalid_excluded a [3,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,8] (by decide +kernel)))

theorem node_368 : Excluded a [3,8,7,0,6,1] :=
  source_excluded a [3,8,7,0,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_369 : Excluded a [3,8,7,0,6,2] :=
  predecessor_excluded a [3,8,7,0,6,2] 1 0 5 3 (by decide) (by decide +kernel)

theorem node_370 : Excluded a [3,8,7,0,6,4] :=
  source_excluded a [3,8,7,0,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_367 : Excluded a [3,8,7,0,6] :=
  branch_excluded a [3,8,7,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,6,0] (by decide +kernel))
      node_368
      node_369
      (invalid_excluded a [3,8,7,0,6,3] (by decide +kernel))
      node_370
      (invalid_excluded a [3,8,7,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,6,8] (by decide +kernel)))

theorem node_355 : Excluded a [3,8,7,0] :=
  branch_excluded a [3,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,0] (by decide +kernel))
      node_356
      node_357
      (invalid_excluded a [3,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,5] (by decide +kernel))
      node_367
      (invalid_excluded a [3,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,8] (by decide +kernel)))

theorem node_371 : Excluded a [3,8,7,1] :=
  source_excluded a [3,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_372 : Excluded a [3,8,7,2] :=
  predecessor_excluded a [3,8,7,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_373 : Excluded a [3,8,7,5] :=
  source_excluded a [3,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_375 : Excluded a [3,8,7,6,0] :=
  predecessor_excluded a [3,8,7,6,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_377 : Excluded a [3,8,7,6,1,0] :=
  source_excluded a [3,8,7,6,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_378 : Excluded a [3,8,7,6,1,2] :=
  predecessor_excluded a [3,8,7,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_379 : Excluded a [3,8,7,6,1,4] :=
  source_excluded a [3,8,7,6,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_376 : Excluded a [3,8,7,6,1] :=
  branch_excluded a [3,8,7,6,1] (by decide)
    (fin9_cases _
      node_377
      (invalid_excluded a [3,8,7,6,1,1] (by decide +kernel))
      node_378
      (invalid_excluded a [3,8,7,6,1,3] (by decide +kernel))
      node_379
      (invalid_excluded a [3,8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,8] (by decide +kernel)))

theorem node_381 : Excluded a [3,8,7,6,2,0] :=
  source_excluded a [3,8,7,6,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_382 : Excluded a [3,8,7,6,2,1] :=
  source_excluded a [3,8,7,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_383 : Excluded a [3,8,7,6,2,4] :=
  source_excluded a [3,8,7,6,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_380 : Excluded a [3,8,7,6,2] :=
  branch_excluded a [3,8,7,6,2] (by decide)
    (fin9_cases _
      node_381
      node_382
      (invalid_excluded a [3,8,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,3] (by decide +kernel))
      node_383
      (invalid_excluded a [3,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,8] (by decide +kernel)))

theorem node_374 : Excluded a [3,8,7,6] :=
  branch_excluded a [3,8,7,6] (by decide)
    (fin9_cases _
      node_375
      node_376
      node_380
      (invalid_excluded a [3,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,8] (by decide +kernel)))

theorem node_354 : Excluded a [3,8,7] :=
  branch_excluded a [3,8,7] (by decide)
    (fin9_cases _
      node_355
      node_371
      node_372
      (invalid_excluded a [3,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,4] (by decide +kernel))
      node_373
      node_374
      (invalid_excluded a [3,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,8] (by decide +kernel)))

theorem node_320 : Excluded a [3,8] :=
  branch_excluded a [3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,0] (by decide +kernel))
      node_321
      (invalid_excluded a [3,8,2] (by decide +kernel))
      (invalid_excluded a [3,8,3] (by decide +kernel))
      node_322
      node_352
      node_353
      node_354
      (invalid_excluded a [3,8,8] (by decide +kernel)))

theorem node_3 : Excluded a [3] :=
  branch_excluded a [3] (by decide)
    (fin9_cases _
      node_4
      (invalid_excluded a [3,1] (by decide +kernel))
      (invalid_excluded a [3,2] (by decide +kernel))
      (invalid_excluded a [3,3] (by decide +kernel))
      node_5
      node_6
      node_188
      node_254
      node_320)

theorem node_385 : Excluded a [4,0] :=
  source_excluded a [4,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_387 : Excluded a [4,3,1] :=
  source_excluded a [4,3,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_389 : Excluded a [4,3,5,0] :=
  source_excluded a [4,3,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_390 : Excluded a [4,3,5,1] :=
  source_excluded a [4,3,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_391 : Excluded a [4,3,5,2] :=
  source_excluded a [4,3,5,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_393 : Excluded a [4,3,5,6,0] :=
  source_excluded a [4,3,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_394 : Excluded a [4,3,5,6,1] :=
  source_excluded a [4,3,5,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_395 : Excluded a [4,3,5,6,2] :=
  source_excluded a [4,3,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_396 : Excluded a [4,3,5,6,7] :=
  predecessor_excluded a [4,3,5,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_398 : Excluded a [4,3,5,6,8,0] :=
  source_excluded a [4,3,5,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_399 : Excluded a [4,3,5,6,8,1] :=
  source_excluded a [4,3,5,6,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_400 : Excluded a [4,3,5,6,8,2] :=
  source_excluded a [4,3,5,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_403 : Excluded a [4,3,5,6,8,7,0,1] :=
  predecessor_excluded a [4,3,5,6,8,7,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_405 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_405 : LosingRegion (edgeOf a b_405) 0 :=
  losingMask a b_405 0 1512339026974287451980800
    (by decide +kernel) (by decide +kernel)

theorem node_405 : Excluded a [4,3,5,6,8,7,0,2,1] :=
  losing_excluded a [4,3,5,6,8,7,0,2,1] (by decide) b_405 (by decide +kernel) 1 0 7 cert_405 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_405 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1512339026974287451980800 1 7; decide +kernel)

theorem node_404 : Excluded a [4,3,5,6,8,7,0,2] :=
  branch_excluded a [4,3,5,6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,6,8,7,0,2,0] (by decide +kernel))
      node_405
      (invalid_excluded a [4,3,5,6,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,2,8] (by decide +kernel)))

theorem node_402 : Excluded a [4,3,5,6,8,7,0] :=
  branch_excluded a [4,3,5,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,6,8,7,0,0] (by decide +kernel))
      node_403
      node_404
      (invalid_excluded a [4,3,5,6,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,0,8] (by decide +kernel)))

def b_408 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_408 : LosingRegion (edgeOf a b_408) 0 :=
  losingMask a b_408 0 1210109877908713044577280
    (by decide +kernel) (by decide +kernel)

theorem node_408 : Excluded a [4,3,5,6,8,7,1,0,2] :=
  losing_excluded a [4,3,5,6,8,7,1,0,2] (by decide) b_408 (by decide +kernel) 1 0 2 cert_408 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_408 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1210109877908713044577280 1 2; decide +kernel)

theorem node_407 : Excluded a [4,3,5,6,8,7,1,0] :=
  branch_excluded a [4,3,5,6,8,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,6,8,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,0,1] (by decide +kernel))
      node_408
      (invalid_excluded a [4,3,5,6,8,7,1,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,0,8] (by decide +kernel)))

theorem node_409 : Excluded a [4,3,5,6,8,7,1,2] :=
  predecessor_excluded a [4,3,5,6,8,7,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_406 : Excluded a [4,3,5,6,8,7,1] :=
  branch_excluded a [4,3,5,6,8,7,1] (by decide)
    (fin9_cases _
      node_407
      (invalid_excluded a [4,3,5,6,8,7,1,1] (by decide +kernel))
      node_409
      (invalid_excluded a [4,3,5,6,8,7,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,1,8] (by decide +kernel)))

theorem node_411 : Excluded a [4,3,5,6,8,7,2,0] :=
  predecessor_excluded a [4,3,5,6,8,7,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_413 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_413 : LosingRegion (edgeOf a b_413) 0 :=
  losingMask a b_413 0 1212468764877266386715648
    (by decide +kernel) (by decide +kernel)

theorem node_413 : Excluded a [4,3,5,6,8,7,2,1,0] :=
  losing_excluded a [4,3,5,6,8,7,2,1,0] (by decide) b_413 (by decide +kernel) 1 0 6 cert_413 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_413 1 0 ∧ 6 ≠ 1 ∧ maskRegion 1212468764877266386715648 1 6; decide +kernel)

theorem node_412 : Excluded a [4,3,5,6,8,7,2,1] :=
  branch_excluded a [4,3,5,6,8,7,2,1] (by decide)
    (fin9_cases _
      node_413
      (invalid_excluded a [4,3,5,6,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,1,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,1,8] (by decide +kernel)))

theorem node_410 : Excluded a [4,3,5,6,8,7,2] :=
  branch_excluded a [4,3,5,6,8,7,2] (by decide)
    (fin9_cases _
      node_411
      node_412
      (invalid_excluded a [4,3,5,6,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,2,8] (by decide +kernel)))

theorem node_401 : Excluded a [4,3,5,6,8,7] :=
  branch_excluded a [4,3,5,6,8,7] (by decide)
    (fin9_cases _
      node_402
      node_406
      node_410
      (invalid_excluded a [4,3,5,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,7,8] (by decide +kernel)))

theorem node_397 : Excluded a [4,3,5,6,8] :=
  branch_excluded a [4,3,5,6,8] (by decide)
    (fin9_cases _
      node_398
      node_399
      node_400
      (invalid_excluded a [4,3,5,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,6] (by decide +kernel))
      node_401
      (invalid_excluded a [4,3,5,6,8,8] (by decide +kernel)))

theorem node_392 : Excluded a [4,3,5,6] :=
  branch_excluded a [4,3,5,6] (by decide)
    (fin9_cases _
      node_393
      node_394
      node_395
      (invalid_excluded a [4,3,5,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,6] (by decide +kernel))
      node_396
      node_397)

theorem node_415 : Excluded a [4,3,5,7,0] :=
  source_excluded a [4,3,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_416 : Excluded a [4,3,5,7,1] :=
  source_excluded a [4,3,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_417 : Excluded a [4,3,5,7,2] :=
  source_excluded a [4,3,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_419 : Excluded a [4,3,5,7,6,0] :=
  source_excluded a [4,3,5,7,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_420 : Excluded a [4,3,5,7,6,1] :=
  source_excluded a [4,3,5,7,6,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_421 : Excluded a [4,3,5,7,6,2] :=
  source_excluded a [4,3,5,7,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_424 : Excluded a [4,3,5,7,6,8,0,1] :=
  predecessor_excluded a [4,3,5,7,6,8,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_426 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_426 : LosingRegion (edgeOf a b_426) 0 :=
  losingMask a b_426 0 1512339036535073631437824
    (by decide +kernel) (by decide +kernel)

theorem node_426 : Excluded a [4,3,5,7,6,8,0,2,1] :=
  losing_excluded a [4,3,5,7,6,8,0,2,1] (by decide) b_426 (by decide +kernel) 1 0 7 cert_426 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_426 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1512339036535073631437824 1 7; decide +kernel)

theorem node_425 : Excluded a [4,3,5,7,6,8,0,2] :=
  branch_excluded a [4,3,5,7,6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,7,6,8,0,2,0] (by decide +kernel))
      node_426
      (invalid_excluded a [4,3,5,7,6,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,2,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,2,8] (by decide +kernel)))

theorem node_423 : Excluded a [4,3,5,7,6,8,0] :=
  branch_excluded a [4,3,5,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,7,6,8,0,0] (by decide +kernel))
      node_424
      node_425
      (invalid_excluded a [4,3,5,7,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,0,8] (by decide +kernel)))

def b_429 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_429 : LosingRegion (edgeOf a b_429) 0 :=
  losingMask a b_429 0 1210109884669021633250304
    (by decide +kernel) (by decide +kernel)

theorem node_429 : Excluded a [4,3,5,7,6,8,1,0,2] :=
  losing_excluded a [4,3,5,7,6,8,1,0,2] (by decide) b_429 (by decide +kernel) 1 0 8 cert_429 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_429 1 0 ∧ 8 ≠ 1 ∧ maskRegion 1210109884669021633250304 1 8; decide +kernel)

theorem node_428 : Excluded a [4,3,5,7,6,8,1,0] :=
  branch_excluded a [4,3,5,7,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,7,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,0,1] (by decide +kernel))
      node_429
      (invalid_excluded a [4,3,5,7,6,8,1,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,0,8] (by decide +kernel)))

theorem node_430 : Excluded a [4,3,5,7,6,8,1,2] :=
  predecessor_excluded a [4,3,5,7,6,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_427 : Excluded a [4,3,5,7,6,8,1] :=
  branch_excluded a [4,3,5,7,6,8,1] (by decide)
    (fin9_cases _
      node_428
      (invalid_excluded a [4,3,5,7,6,8,1,1] (by decide +kernel))
      node_430
      (invalid_excluded a [4,3,5,7,6,8,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,1,8] (by decide +kernel)))

theorem node_432 : Excluded a [4,3,5,7,6,8,2,0] :=
  predecessor_excluded a [4,3,5,7,6,8,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_434 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_434 : LosingRegion (edgeOf a b_434) 0 :=
  losingMask a b_434 0 1212468762058140047936512
    (by decide +kernel) (by decide +kernel)

theorem node_434 : Excluded a [4,3,5,7,6,8,2,1,0] :=
  losing_excluded a [4,3,5,7,6,8,2,1,0] (by decide) b_434 (by decide +kernel) 1 0 2 cert_434 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_434 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212468762058140047936512 1 2; decide +kernel)

theorem node_433 : Excluded a [4,3,5,7,6,8,2,1] :=
  branch_excluded a [4,3,5,7,6,8,2,1] (by decide)
    (fin9_cases _
      node_434
      (invalid_excluded a [4,3,5,7,6,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,1,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,1,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,1,8] (by decide +kernel)))

theorem node_431 : Excluded a [4,3,5,7,6,8,2] :=
  branch_excluded a [4,3,5,7,6,8,2] (by decide)
    (fin9_cases _
      node_432
      node_433
      (invalid_excluded a [4,3,5,7,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,2,8] (by decide +kernel)))

theorem node_422 : Excluded a [4,3,5,7,6,8] :=
  branch_excluded a [4,3,5,7,6,8] (by decide)
    (fin9_cases _
      node_423
      node_427
      node_431
      (invalid_excluded a [4,3,5,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,8,8] (by decide +kernel)))

theorem node_418 : Excluded a [4,3,5,7,6] :=
  branch_excluded a [4,3,5,7,6] (by decide)
    (fin9_cases _
      node_419
      node_420
      node_421
      (invalid_excluded a [4,3,5,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,6,7] (by decide +kernel))
      node_422)

theorem node_435 : Excluded a [4,3,5,7,8] :=
  predecessor_excluded a [4,3,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_414 : Excluded a [4,3,5,7] :=
  branch_excluded a [4,3,5,7] (by decide)
    (fin9_cases _
      node_415
      node_416
      node_417
      (invalid_excluded a [4,3,5,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,5] (by decide +kernel))
      node_418
      (invalid_excluded a [4,3,5,7,7] (by decide +kernel))
      node_435)

theorem node_437 : Excluded a [4,3,5,8,0] :=
  source_excluded a [4,3,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_438 : Excluded a [4,3,5,8,1] :=
  source_excluded a [4,3,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_439 : Excluded a [4,3,5,8,2] :=
  source_excluded a [4,3,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_440 : Excluded a [4,3,5,8,6] :=
  predecessor_excluded a [4,3,5,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_442 : Excluded a [4,3,5,8,7,0] :=
  source_excluded a [4,3,5,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_443 : Excluded a [4,3,5,8,7,1] :=
  source_excluded a [4,3,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_444 : Excluded a [4,3,5,8,7,2] :=
  source_excluded a [4,3,5,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_447 : Excluded a [4,3,5,8,7,6,0,1] :=
  predecessor_excluded a [4,3,5,8,7,6,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_449 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | 4 => 7
  | 5 => 6
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_449 : LosingRegion (edgeOf a b_449) 0 :=
  losingMask a b_449 0 1512339031459766612331520
    (by decide +kernel) (by decide +kernel)

theorem node_449 : Excluded a [4,3,5,8,7,6,0,2,1] :=
  losing_excluded a [4,3,5,8,7,6,0,2,1] (by decide) b_449 (by decide +kernel) 1 0 2 cert_449 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_449 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1512339031459766612331520 1 2; decide +kernel)

theorem node_448 : Excluded a [4,3,5,8,7,6,0,2] :=
  branch_excluded a [4,3,5,8,7,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,8,7,6,0,2,0] (by decide +kernel))
      node_449
      (invalid_excluded a [4,3,5,8,7,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,2,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,2,8] (by decide +kernel)))

theorem node_446 : Excluded a [4,3,5,8,7,6,0] :=
  branch_excluded a [4,3,5,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,8,7,6,0,0] (by decide +kernel))
      node_447
      node_448
      (invalid_excluded a [4,3,5,8,7,6,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,0,8] (by decide +kernel)))

def b_452 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | 4 => 7
  | 5 => 6
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_452 : LosingRegion (edgeOf a b_452) 0 :=
  losingMask a b_452 0 1210109887465655228302336
    (by decide +kernel) (by decide +kernel)

theorem node_452 : Excluded a [4,3,5,8,7,6,1,0,2] :=
  losing_excluded a [4,3,5,8,7,6,1,0,2] (by decide) b_452 (by decide +kernel) 1 0 8 cert_452 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_452 1 0 ∧ 8 ≠ 1 ∧ maskRegion 1210109887465655228302336 1 8; decide +kernel)

theorem node_451 : Excluded a [4,3,5,8,7,6,1,0] :=
  branch_excluded a [4,3,5,8,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,8,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,0,1] (by decide +kernel))
      node_452
      (invalid_excluded a [4,3,5,8,7,6,1,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,0,8] (by decide +kernel)))

theorem node_453 : Excluded a [4,3,5,8,7,6,1,2] :=
  predecessor_excluded a [4,3,5,8,7,6,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_450 : Excluded a [4,3,5,8,7,6,1] :=
  branch_excluded a [4,3,5,8,7,6,1] (by decide)
    (fin9_cases _
      node_451
      (invalid_excluded a [4,3,5,8,7,6,1,1] (by decide +kernel))
      node_453
      (invalid_excluded a [4,3,5,8,7,6,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,1,8] (by decide +kernel)))

theorem node_455 : Excluded a [4,3,5,8,7,6,2,0] :=
  predecessor_excluded a [4,3,5,8,7,6,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_457 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | 4 => 7
  | 5 => 6
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_457 : LosingRegion (edgeOf a b_457) 0 :=
  losingMask a b_457 0 1212468759815673198183424
    (by decide +kernel) (by decide +kernel)

theorem node_457 : Excluded a [4,3,5,8,7,6,2,1,0] :=
  losing_excluded a [4,3,5,8,7,6,2,1,0] (by decide) b_457 (by decide +kernel) 1 0 6 cert_457 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_457 1 0 ∧ 6 ≠ 1 ∧ maskRegion 1212468759815673198183424 1 6; decide +kernel)

theorem node_456 : Excluded a [4,3,5,8,7,6,2,1] :=
  branch_excluded a [4,3,5,8,7,6,2,1] (by decide)
    (fin9_cases _
      node_457
      (invalid_excluded a [4,3,5,8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,1,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,1,8] (by decide +kernel)))

theorem node_454 : Excluded a [4,3,5,8,7,6,2] :=
  branch_excluded a [4,3,5,8,7,6,2] (by decide)
    (fin9_cases _
      node_455
      node_456
      (invalid_excluded a [4,3,5,8,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,2,8] (by decide +kernel)))

theorem node_445 : Excluded a [4,3,5,8,7,6] :=
  branch_excluded a [4,3,5,8,7,6] (by decide)
    (fin9_cases _
      node_446
      node_450
      node_454
      (invalid_excluded a [4,3,5,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6,8] (by decide +kernel)))

theorem node_441 : Excluded a [4,3,5,8,7] :=
  branch_excluded a [4,3,5,8,7] (by decide)
    (fin9_cases _
      node_442
      node_443
      node_444
      (invalid_excluded a [4,3,5,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,5] (by decide +kernel))
      node_445
      (invalid_excluded a [4,3,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,8] (by decide +kernel)))

theorem node_436 : Excluded a [4,3,5,8] :=
  branch_excluded a [4,3,5,8] (by decide)
    (fin9_cases _
      node_437
      node_438
      node_439
      (invalid_excluded a [4,3,5,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,5] (by decide +kernel))
      node_440
      node_441
      (invalid_excluded a [4,3,5,8,8] (by decide +kernel)))

theorem node_388 : Excluded a [4,3,5] :=
  branch_excluded a [4,3,5] (by decide)
    (fin9_cases _
      node_389
      node_390
      node_391
      (invalid_excluded a [4,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,5] (by decide +kernel))
      node_392
      node_414
      node_436)

theorem node_459 : Excluded a [4,3,6,0] :=
  source_excluded a [4,3,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_460 : Excluded a [4,3,6,1] :=
  source_excluded a [4,3,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_461 : Excluded a [4,3,6,2] :=
  source_excluded a [4,3,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_462 : Excluded a [4,3,6,5] :=
  source_excluded a [4,3,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_465 : Excluded a [4,3,6,7,0,1] :=
  source_excluded a [4,3,6,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_466 : Excluded a [4,3,6,7,0,2] :=
  source_excluded a [4,3,6,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_468 : Excluded a [4,3,6,7,0,8,1] :=
  predecessor_excluded a [4,3,6,7,0,8,1] 3 1 2 6 (by decide) (by decide +kernel)

def b_471 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 6
  | 3 => 7
  | 4 => 0
  | 5 => 8
  | 6 => 2
  | 7 => 1
  | 8 => 5
  | _ => 0

def cert_471 : LosingRegion (edgeOf a b_471) 0 :=
  losingMask a b_471 0 2150513463966636646075392
    (by decide +kernel) (by decide +kernel)

theorem node_471 : Excluded a [4,3,6,7,0,8,2,1,5] :=
  losing_excluded a [4,3,6,7,0,8,2,1,5] (by decide) b_471 (by decide +kernel) 1 0 2 cert_471 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_471 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2150513463966636646075392 1 2; decide +kernel)

theorem node_470 : Excluded a [4,3,6,7,0,8,2,1] :=
  branch_excluded a [4,3,6,7,0,8,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,6,7,0,8,2,1,0] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,1,2] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,1,4] (by decide +kernel))
      node_471
      (invalid_excluded a [4,3,6,7,0,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,1,8] (by decide +kernel)))

theorem node_472 : Excluded a [4,3,6,7,0,8,2,5] :=
  source_excluded a [4,3,6,7,0,8,2,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_469 : Excluded a [4,3,6,7,0,8,2] :=
  branch_excluded a [4,3,6,7,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,6,7,0,8,2,0] (by decide +kernel))
      node_470
      (invalid_excluded a [4,3,6,7,0,8,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,4] (by decide +kernel))
      node_472
      (invalid_excluded a [4,3,6,7,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,8] (by decide +kernel)))

theorem node_473 : Excluded a [4,3,6,7,0,8,5] :=
  predecessor_excluded a [4,3,6,7,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_467 : Excluded a [4,3,6,7,0,8] :=
  branch_excluded a [4,3,6,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,6,7,0,8,0] (by decide +kernel))
      node_468
      node_469
      (invalid_excluded a [4,3,6,7,0,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,4] (by decide +kernel))
      node_473
      (invalid_excluded a [4,3,6,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,8] (by decide +kernel)))

theorem node_464 : Excluded a [4,3,6,7,0] :=
  branch_excluded a [4,3,6,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,6,7,0,0] (by decide +kernel))
      node_465
      node_466
      (invalid_excluded a [4,3,6,7,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,7] (by decide +kernel))
      node_467)

theorem node_474 : Excluded a [4,3,6,7,1] :=
  source_excluded a [4,3,6,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_475 : Excluded a [4,3,6,7,2] :=
  predecessor_excluded a [4,3,6,7,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_476 : Excluded a [4,3,6,7,8] :=
  predecessor_excluded a [4,3,6,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_463 : Excluded a [4,3,6,7] :=
  branch_excluded a [4,3,6,7] (by decide)
    (fin9_cases _
      node_464
      node_474
      node_475
      (invalid_excluded a [4,3,6,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,7] (by decide +kernel))
      node_476)

theorem node_479 : Excluded a [4,3,6,8,0,1] :=
  source_excluded a [4,3,6,8,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_480 : Excluded a [4,3,6,8,0,2] :=
  source_excluded a [4,3,6,8,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_481 : Excluded a [4,3,6,8,0,7] :=
  predecessor_excluded a [4,3,6,8,0,7] 0 8 5 3 (by decide) (by decide +kernel)

theorem node_478 : Excluded a [4,3,6,8,0] :=
  branch_excluded a [4,3,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,6,8,0,0] (by decide +kernel))
      node_479
      node_480
      (invalid_excluded a [4,3,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,0,6] (by decide +kernel))
      node_481
      (invalid_excluded a [4,3,6,8,0,8] (by decide +kernel)))

theorem node_482 : Excluded a [4,3,6,8,1] :=
  source_excluded a [4,3,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_483 : Excluded a [4,3,6,8,2] :=
  predecessor_excluded a [4,3,6,8,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_485 : Excluded a [4,3,6,8,7,0] :=
  predecessor_excluded a [4,3,6,8,7,0] 1 4 5 0 (by decide) (by decide +kernel)

theorem node_486 : Excluded a [4,3,6,8,7,1] :=
  source_excluded a [4,3,6,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_487 : Excluded a [4,3,6,8,7,2] :=
  source_excluded a [4,3,6,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_484 : Excluded a [4,3,6,8,7] :=
  branch_excluded a [4,3,6,8,7] (by decide)
    (fin9_cases _
      node_485
      node_486
      node_487
      (invalid_excluded a [4,3,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,8] (by decide +kernel)))

theorem node_477 : Excluded a [4,3,6,8] :=
  branch_excluded a [4,3,6,8] (by decide)
    (fin9_cases _
      node_478
      node_482
      node_483
      (invalid_excluded a [4,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,6] (by decide +kernel))
      node_484
      (invalid_excluded a [4,3,6,8,8] (by decide +kernel)))

theorem node_458 : Excluded a [4,3,6] :=
  branch_excluded a [4,3,6] (by decide)
    (fin9_cases _
      node_459
      node_460
      node_461
      (invalid_excluded a [4,3,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,4] (by decide +kernel))
      node_462
      (invalid_excluded a [4,3,6,6] (by decide +kernel))
      node_463
      node_477)

theorem node_489 : Excluded a [4,3,7,0] :=
  source_excluded a [4,3,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_490 : Excluded a [4,3,7,1] :=
  source_excluded a [4,3,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_491 : Excluded a [4,3,7,2] :=
  source_excluded a [4,3,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_492 : Excluded a [4,3,7,5] :=
  source_excluded a [4,3,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_495 : Excluded a [4,3,7,6,0,1] :=
  source_excluded a [4,3,7,6,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_496 : Excluded a [4,3,7,6,0,2] :=
  source_excluded a [4,3,7,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_497 : Excluded a [4,3,7,6,0,8] :=
  predecessor_excluded a [4,3,7,6,0,8] 0 6 5 3 (by decide) (by decide +kernel)

theorem node_494 : Excluded a [4,3,7,6,0] :=
  branch_excluded a [4,3,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,6,0,0] (by decide +kernel))
      node_495
      node_496
      (invalid_excluded a [4,3,7,6,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,7] (by decide +kernel))
      node_497)

theorem node_498 : Excluded a [4,3,7,6,1] :=
  source_excluded a [4,3,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_499 : Excluded a [4,3,7,6,2] :=
  predecessor_excluded a [4,3,7,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_501 : Excluded a [4,3,7,6,8,0] :=
  predecessor_excluded a [4,3,7,6,8,0] 1 4 5 0 (by decide) (by decide +kernel)

theorem node_502 : Excluded a [4,3,7,6,8,1] :=
  source_excluded a [4,3,7,6,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_503 : Excluded a [4,3,7,6,8,2] :=
  source_excluded a [4,3,7,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_500 : Excluded a [4,3,7,6,8] :=
  branch_excluded a [4,3,7,6,8] (by decide)
    (fin9_cases _
      node_501
      node_502
      node_503
      (invalid_excluded a [4,3,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,8] (by decide +kernel)))

theorem node_493 : Excluded a [4,3,7,6] :=
  branch_excluded a [4,3,7,6] (by decide)
    (fin9_cases _
      node_494
      node_498
      node_499
      (invalid_excluded a [4,3,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,7] (by decide +kernel))
      node_500)

theorem node_506 : Excluded a [4,3,7,8,0,1] :=
  source_excluded a [4,3,7,8,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_507 : Excluded a [4,3,7,8,0,2] :=
  source_excluded a [4,3,7,8,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_510 : Excluded a [4,3,7,8,0,6,1,2] :=
  predecessor_excluded a [4,3,7,8,0,6,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_511 : Excluded a [4,3,7,8,0,6,1,5] :=
  predecessor_excluded a [4,3,7,8,0,6,1,5] 0 6 7 5 (by decide) (by decide +kernel)

theorem node_509 : Excluded a [4,3,7,8,0,6,1] :=
  branch_excluded a [4,3,7,8,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,8,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,1,1] (by decide +kernel))
      node_510
      (invalid_excluded a [4,3,7,8,0,6,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,1,4] (by decide +kernel))
      node_511
      (invalid_excluded a [4,3,7,8,0,6,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,1,8] (by decide +kernel)))

theorem node_512 : Excluded a [4,3,7,8,0,6,2] :=
  source_excluded a [4,3,7,8,0,6,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_514 : Excluded a [4,3,7,8,0,6,5,1] :=
  predecessor_excluded a [4,3,7,8,0,6,5,1] 3 1 2 7 (by decide) (by decide +kernel)

def b_516 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 7
  | 3 => 8
  | 4 => 0
  | 5 => 6
  | 6 => 5
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_516 : LosingRegion (edgeOf a b_516) 0 :=
  losingMask a b_516 0 1847689425424009942535168
    (by decide +kernel) (by decide +kernel)

theorem node_516 : Excluded a [4,3,7,8,0,6,5,2,1] :=
  losing_excluded a [4,3,7,8,0,6,5,2,1] (by decide) b_516 (by decide +kernel) 1 0 2 cert_516 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_516 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1847689425424009942535168 1 2; decide +kernel)

theorem node_515 : Excluded a [4,3,7,8,0,6,5,2] :=
  branch_excluded a [4,3,7,8,0,6,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,8,0,6,5,2,0] (by decide +kernel))
      node_516
      (invalid_excluded a [4,3,7,8,0,6,5,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,2,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,2,5] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,2,8] (by decide +kernel)))

theorem node_513 : Excluded a [4,3,7,8,0,6,5] :=
  branch_excluded a [4,3,7,8,0,6,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,8,0,6,5,0] (by decide +kernel))
      node_514
      node_515
      (invalid_excluded a [4,3,7,8,0,6,5,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,5,8] (by decide +kernel)))

theorem node_508 : Excluded a [4,3,7,8,0,6] :=
  branch_excluded a [4,3,7,8,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,8,0,6,0] (by decide +kernel))
      node_509
      node_512
      (invalid_excluded a [4,3,7,8,0,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,4] (by decide +kernel))
      node_513
      (invalid_excluded a [4,3,7,8,0,6,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6,8] (by decide +kernel)))

theorem node_505 : Excluded a [4,3,7,8,0] :=
  branch_excluded a [4,3,7,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,8,0,0] (by decide +kernel))
      node_506
      node_507
      (invalid_excluded a [4,3,7,8,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,5] (by decide +kernel))
      node_508
      (invalid_excluded a [4,3,7,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,8] (by decide +kernel)))

theorem node_517 : Excluded a [4,3,7,8,1] :=
  source_excluded a [4,3,7,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_518 : Excluded a [4,3,7,8,2] :=
  predecessor_excluded a [4,3,7,8,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_519 : Excluded a [4,3,7,8,6] :=
  predecessor_excluded a [4,3,7,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_504 : Excluded a [4,3,7,8] :=
  branch_excluded a [4,3,7,8] (by decide)
    (fin9_cases _
      node_505
      node_517
      node_518
      (invalid_excluded a [4,3,7,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,5] (by decide +kernel))
      node_519
      (invalid_excluded a [4,3,7,8,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,8] (by decide +kernel)))

theorem node_488 : Excluded a [4,3,7] :=
  branch_excluded a [4,3,7] (by decide)
    (fin9_cases _
      node_489
      node_490
      node_491
      (invalid_excluded a [4,3,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,4] (by decide +kernel))
      node_492
      node_493
      (invalid_excluded a [4,3,7,7] (by decide +kernel))
      node_504)

theorem node_521 : Excluded a [4,3,8,0] :=
  source_excluded a [4,3,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_522 : Excluded a [4,3,8,1] :=
  source_excluded a [4,3,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_523 : Excluded a [4,3,8,2] :=
  source_excluded a [4,3,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_524 : Excluded a [4,3,8,5] :=
  source_excluded a [4,3,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_527 : Excluded a [4,3,8,6,0,1] :=
  source_excluded a [4,3,8,6,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_528 : Excluded a [4,3,8,6,0,2] :=
  source_excluded a [4,3,8,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_531 : Excluded a [4,3,8,6,0,7,1,2] :=
  source_excluded a [4,3,8,6,0,7,1,2] 7 0 2 (by decide) (by decide +kernel)

def b_533 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 8
  | 3 => 6
  | 4 => 0
  | 5 => 7
  | 6 => 1
  | 7 => 5
  | 8 => 2
  | _ => 0

def cert_533 : LosingRegion (edgeOf a b_533) 0 :=
  losingMask a b_533 0 1241462545714646879308800
    (by decide +kernel) (by decide +kernel)

theorem node_533 : Excluded a [4,3,8,6,0,7,1,5,2] :=
  losing_excluded a [4,3,8,6,0,7,1,5,2] (by decide) b_533 (by decide +kernel) 1 0 2 cert_533 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_533 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1241462545714646879308800 1 2; decide +kernel)

theorem node_532 : Excluded a [4,3,8,6,0,7,1,5] :=
  branch_excluded a [4,3,8,6,0,7,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,6,0,7,1,5,0] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,5,1] (by decide +kernel))
      node_533
      (invalid_excluded a [4,3,8,6,0,7,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,5,5] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,5,6] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,5,8] (by decide +kernel)))

theorem node_530 : Excluded a [4,3,8,6,0,7,1] :=
  branch_excluded a [4,3,8,6,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,6,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,1] (by decide +kernel))
      node_531
      (invalid_excluded a [4,3,8,6,0,7,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,4] (by decide +kernel))
      node_532
      (invalid_excluded a [4,3,8,6,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,1,8] (by decide +kernel)))

theorem node_534 : Excluded a [4,3,8,6,0,7,2] :=
  predecessor_excluded a [4,3,8,6,0,7,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_535 : Excluded a [4,3,8,6,0,7,5] :=
  source_excluded a [4,3,8,6,0,7,5] 6 0 5 (by decide) (by decide +kernel)

theorem node_529 : Excluded a [4,3,8,6,0,7] :=
  branch_excluded a [4,3,8,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,6,0,7,0] (by decide +kernel))
      node_530
      node_534
      (invalid_excluded a [4,3,8,6,0,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,4] (by decide +kernel))
      node_535
      (invalid_excluded a [4,3,8,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,7,8] (by decide +kernel)))

theorem node_526 : Excluded a [4,3,8,6,0] :=
  branch_excluded a [4,3,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,6,0,0] (by decide +kernel))
      node_527
      node_528
      (invalid_excluded a [4,3,8,6,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,6] (by decide +kernel))
      node_529
      (invalid_excluded a [4,3,8,6,0,8] (by decide +kernel)))

theorem node_536 : Excluded a [4,3,8,6,1] :=
  source_excluded a [4,3,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_537 : Excluded a [4,3,8,6,2] :=
  predecessor_excluded a [4,3,8,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_538 : Excluded a [4,3,8,6,7] :=
  predecessor_excluded a [4,3,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_525 : Excluded a [4,3,8,6] :=
  branch_excluded a [4,3,8,6] (by decide)
    (fin9_cases _
      node_526
      node_536
      node_537
      (invalid_excluded a [4,3,8,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,5] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,6] (by decide +kernel))
      node_538
      (invalid_excluded a [4,3,8,6,8] (by decide +kernel)))

theorem node_541 : Excluded a [4,3,8,7,0,1] :=
  source_excluded a [4,3,8,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_542 : Excluded a [4,3,8,7,0,2] :=
  source_excluded a [4,3,8,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_543 : Excluded a [4,3,8,7,0,6] :=
  predecessor_excluded a [4,3,8,7,0,6] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_540 : Excluded a [4,3,8,7,0] :=
  branch_excluded a [4,3,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,7,0,0] (by decide +kernel))
      node_541
      node_542
      (invalid_excluded a [4,3,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,5] (by decide +kernel))
      node_543
      (invalid_excluded a [4,3,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,8] (by decide +kernel)))

theorem node_544 : Excluded a [4,3,8,7,1] :=
  source_excluded a [4,3,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_545 : Excluded a [4,3,8,7,2] :=
  predecessor_excluded a [4,3,8,7,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_547 : Excluded a [4,3,8,7,6,0] :=
  predecessor_excluded a [4,3,8,7,6,0] 1 4 5 0 (by decide) (by decide +kernel)

theorem node_548 : Excluded a [4,3,8,7,6,1] :=
  source_excluded a [4,3,8,7,6,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_549 : Excluded a [4,3,8,7,6,2] :=
  source_excluded a [4,3,8,7,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_546 : Excluded a [4,3,8,7,6] :=
  branch_excluded a [4,3,8,7,6] (by decide)
    (fin9_cases _
      node_547
      node_548
      node_549
      (invalid_excluded a [4,3,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,6,8] (by decide +kernel)))

theorem node_539 : Excluded a [4,3,8,7] :=
  branch_excluded a [4,3,8,7] (by decide)
    (fin9_cases _
      node_540
      node_544
      node_545
      (invalid_excluded a [4,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,5] (by decide +kernel))
      node_546
      (invalid_excluded a [4,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,8] (by decide +kernel)))

theorem node_520 : Excluded a [4,3,8] :=
  branch_excluded a [4,3,8] (by decide)
    (fin9_cases _
      node_521
      node_522
      node_523
      (invalid_excluded a [4,3,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,4] (by decide +kernel))
      node_524
      node_525
      node_539
      (invalid_excluded a [4,3,8,8] (by decide +kernel)))

theorem node_386 : Excluded a [4,3] :=
  branch_excluded a [4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,0] (by decide +kernel))
      node_387
      (invalid_excluded a [4,3,2] (by decide +kernel))
      (invalid_excluded a [4,3,3] (by decide +kernel))
      (invalid_excluded a [4,3,4] (by decide +kernel))
      node_388
      node_458
      node_488
      node_520)

theorem node_550 : Excluded a [4,5] :=
  predecessor_excluded a [4,5] 2 5 0 1 (by decide) (by decide +kernel)

theorem node_552 : Excluded a [4,6,1] :=
  source_excluded a [4,6,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_553 : Excluded a [4,6,3] :=
  predecessor_excluded a [4,6,3] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_555 : Excluded a [4,6,5,0] :=
  source_excluded a [4,6,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_556 : Excluded a [4,6,5,1] :=
  source_excluded a [4,6,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_557 : Excluded a [4,6,5,2] :=
  predecessor_excluded a [4,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_559 : Excluded a [4,6,5,7,0] :=
  source_excluded a [4,6,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_560 : Excluded a [4,6,5,7,1] :=
  source_excluded a [4,6,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_561 : Excluded a [4,6,5,7,2] :=
  source_excluded a [4,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_562 : Excluded a [4,6,5,7,3] :=
  source_excluded a [4,6,5,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_563 : Excluded a [4,6,5,7,8] :=
  predecessor_excluded a [4,6,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_558 : Excluded a [4,6,5,7] :=
  branch_excluded a [4,6,5,7] (by decide)
    (fin9_cases _
      node_559
      node_560
      node_561
      node_562
      (invalid_excluded a [4,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,7] (by decide +kernel))
      node_563)

theorem node_565 : Excluded a [4,6,5,8,0] :=
  source_excluded a [4,6,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_566 : Excluded a [4,6,5,8,1] :=
  source_excluded a [4,6,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_567 : Excluded a [4,6,5,8,2] :=
  source_excluded a [4,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_568 : Excluded a [4,6,5,8,3] :=
  source_excluded a [4,6,5,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_570 : Excluded a [4,6,5,8,7,0] :=
  source_excluded a [4,6,5,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_571 : Excluded a [4,6,5,8,7,1] :=
  predecessor_excluded a [4,6,5,8,7,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_573 : Excluded a [4,6,5,8,7,2,0] :=
  predecessor_excluded a [4,6,5,8,7,2,0] 3 0 1 6 (by decide) (by decide +kernel)

def b_576 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 5
  | 3 => 8
  | 4 => 7
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 3
  | _ => 0

def cert_576 : LosingRegion (edgeOf a b_576) 0 :=
  losingMask a b_576 0 1521783753368795901592576
    (by decide +kernel) (by decide +kernel)

theorem node_576 : Excluded a [4,6,5,8,7,2,1,0,3] :=
  losing_excluded a [4,6,5,8,7,2,1,0,3] (by decide) b_576 (by decide +kernel) 3 0 0 cert_576 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_576 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1521783753368795901592576 3 0; decide +kernel)

theorem node_575 : Excluded a [4,6,5,8,7,2,1,0] :=
  branch_excluded a [4,6,5,8,7,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,5,8,7,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,0,2] (by decide +kernel))
      node_576
      (invalid_excluded a [4,6,5,8,7,2,1,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,0,8] (by decide +kernel)))

theorem node_577 : Excluded a [4,6,5,8,7,2,1,3] :=
  source_excluded a [4,6,5,8,7,2,1,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_574 : Excluded a [4,6,5,8,7,2,1] :=
  branch_excluded a [4,6,5,8,7,2,1] (by decide)
    (fin9_cases _
      node_575
      (invalid_excluded a [4,6,5,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,2] (by decide +kernel))
      node_577
      (invalid_excluded a [4,6,5,8,7,2,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,1,8] (by decide +kernel)))

theorem node_578 : Excluded a [4,6,5,8,7,2,3] :=
  predecessor_excluded a [4,6,5,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_572 : Excluded a [4,6,5,8,7,2] :=
  branch_excluded a [4,6,5,8,7,2] (by decide)
    (fin9_cases _
      node_573
      node_574
      (invalid_excluded a [4,6,5,8,7,2,2] (by decide +kernel))
      node_578
      (invalid_excluded a [4,6,5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,8] (by decide +kernel)))

theorem node_569 : Excluded a [4,6,5,8,7] :=
  branch_excluded a [4,6,5,8,7] (by decide)
    (fin9_cases _
      node_570
      node_571
      node_572
      (invalid_excluded a [4,6,5,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,8] (by decide +kernel)))

theorem node_564 : Excluded a [4,6,5,8] :=
  branch_excluded a [4,6,5,8] (by decide)
    (fin9_cases _
      node_565
      node_566
      node_567
      node_568
      (invalid_excluded a [4,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,6] (by decide +kernel))
      node_569
      (invalid_excluded a [4,6,5,8,8] (by decide +kernel)))

theorem node_554 : Excluded a [4,6,5] :=
  branch_excluded a [4,6,5] (by decide)
    (fin9_cases _
      node_555
      node_556
      node_557
      (invalid_excluded a [4,6,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,6] (by decide +kernel))
      node_558
      node_564)

theorem node_579 : Excluded a [4,6,7] :=
  predecessor_excluded a [4,6,7] 0 7 1 2 (by decide) (by decide +kernel)

theorem node_581 : Excluded a [4,6,8,0] :=
  source_excluded a [4,6,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_582 : Excluded a [4,6,8,1] :=
  source_excluded a [4,6,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_584 : Excluded a [4,6,8,2,0] :=
  predecessor_excluded a [4,6,8,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_585 : Excluded a [4,6,8,2,1] :=
  source_excluded a [4,6,8,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_586 : Excluded a [4,6,8,2,3] :=
  source_excluded a [4,6,8,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_588 : Excluded a [4,6,8,2,7,0] :=
  predecessor_excluded a [4,6,8,2,7,0] 1 4 5 0 (by decide) (by decide +kernel)

theorem node_589 : Excluded a [4,6,8,2,7,1] :=
  predecessor_excluded a [4,6,8,2,7,1] 0 2 5 3 (by decide) (by decide +kernel)

theorem node_587 : Excluded a [4,6,8,2,7] :=
  branch_excluded a [4,6,8,2,7] (by decide)
    (fin9_cases _
      node_588
      node_589
      (invalid_excluded a [4,6,8,2,7,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,8] (by decide +kernel)))

theorem node_583 : Excluded a [4,6,8,2] :=
  branch_excluded a [4,6,8,2] (by decide)
    (fin9_cases _
      node_584
      node_585
      (invalid_excluded a [4,6,8,2,2] (by decide +kernel))
      node_586
      (invalid_excluded a [4,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,6] (by decide +kernel))
      node_587
      (invalid_excluded a [4,6,8,2,8] (by decide +kernel)))

theorem node_590 : Excluded a [4,6,8,5] :=
  source_excluded a [4,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_593 : Excluded a [4,6,8,7,0,1] :=
  predecessor_excluded a [4,6,8,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

def b_597 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 8
  | 3 => 7
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_597 : LosingRegion (edgeOf a b_597) 0 :=
  losingMask a b_597 0 1465683583671736887954432
    (by decide +kernel) (by decide +kernel)

theorem node_597 : Excluded a [4,6,8,7,0,2,1,3,5] :=
  losing_excluded a [4,6,8,7,0,2,1,3,5] (by decide) b_597 (by decide +kernel) 1 0 2 cert_597 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_597 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1465683583671736887954432 1 2; decide +kernel)

theorem node_596 : Excluded a [4,6,8,7,0,2,1,3] :=
  branch_excluded a [4,6,8,7,0,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,0,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,3,4] (by decide +kernel))
      node_597
      (invalid_excluded a [4,6,8,7,0,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,3,8] (by decide +kernel)))

theorem node_598 : Excluded a [4,6,8,7,0,2,1,5] :=
  predecessor_excluded a [4,6,8,7,0,2,1,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_595 : Excluded a [4,6,8,7,0,2,1] :=
  branch_excluded a [4,6,8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,2] (by decide +kernel))
      node_596
      (invalid_excluded a [4,6,8,7,0,2,1,4] (by decide +kernel))
      node_598
      (invalid_excluded a [4,6,8,7,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,1,8] (by decide +kernel)))

theorem node_599 : Excluded a [4,6,8,7,0,2,3] :=
  source_excluded a [4,6,8,7,0,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_601 : Excluded a [4,6,8,7,0,2,5,1] :=
  predecessor_excluded a [4,6,8,7,0,2,5,1] 0 6 7 1 (by decide) (by decide +kernel)

theorem node_602 : Excluded a [4,6,8,7,0,2,5,3] :=
  predecessor_excluded a [4,6,8,7,0,2,5,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_600 : Excluded a [4,6,8,7,0,2,5] :=
  branch_excluded a [4,6,8,7,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,0,2,5,0] (by decide +kernel))
      node_601
      (invalid_excluded a [4,6,8,7,0,2,5,2] (by decide +kernel))
      node_602
      (invalid_excluded a [4,6,8,7,0,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,5,8] (by decide +kernel)))

theorem node_594 : Excluded a [4,6,8,7,0,2] :=
  branch_excluded a [4,6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,0,2,0] (by decide +kernel))
      node_595
      (invalid_excluded a [4,6,8,7,0,2,2] (by decide +kernel))
      node_599
      (invalid_excluded a [4,6,8,7,0,2,4] (by decide +kernel))
      node_600
      (invalid_excluded a [4,6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,2,8] (by decide +kernel)))

theorem node_592 : Excluded a [4,6,8,7,0] :=
  branch_excluded a [4,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,0,0] (by decide +kernel))
      node_593
      node_594
      (invalid_excluded a [4,6,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,8] (by decide +kernel)))

theorem node_603 : Excluded a [4,6,8,7,1] :=
  source_excluded a [4,6,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_604 : Excluded a [4,6,8,7,2] :=
  predecessor_excluded a [4,6,8,7,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_605 : Excluded a [4,6,8,7,3] :=
  source_excluded a [4,6,8,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_591 : Excluded a [4,6,8,7] :=
  branch_excluded a [4,6,8,7] (by decide)
    (fin9_cases _
      node_592
      node_603
      node_604
      node_605
      (invalid_excluded a [4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,8] (by decide +kernel)))

theorem node_580 : Excluded a [4,6,8] :=
  branch_excluded a [4,6,8] (by decide)
    (fin9_cases _
      node_581
      node_582
      node_583
      (invalid_excluded a [4,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,4] (by decide +kernel))
      node_590
      (invalid_excluded a [4,6,8,6] (by decide +kernel))
      node_591
      (invalid_excluded a [4,6,8,8] (by decide +kernel)))

theorem node_551 : Excluded a [4,6] :=
  branch_excluded a [4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,0] (by decide +kernel))
      node_552
      (invalid_excluded a [4,6,2] (by decide +kernel))
      node_553
      (invalid_excluded a [4,6,4] (by decide +kernel))
      node_554
      (invalid_excluded a [4,6,6] (by decide +kernel))
      node_579
      node_580)

theorem node_607 : Excluded a [4,7,1] :=
  source_excluded a [4,7,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_608 : Excluded a [4,7,3] :=
  predecessor_excluded a [4,7,3] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_610 : Excluded a [4,7,5,0] :=
  source_excluded a [4,7,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_611 : Excluded a [4,7,5,1] :=
  source_excluded a [4,7,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_612 : Excluded a [4,7,5,2] :=
  predecessor_excluded a [4,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_614 : Excluded a [4,7,5,6,0] :=
  source_excluded a [4,7,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_615 : Excluded a [4,7,5,6,1] :=
  source_excluded a [4,7,5,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_616 : Excluded a [4,7,5,6,2] :=
  source_excluded a [4,7,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_617 : Excluded a [4,7,5,6,3] :=
  source_excluded a [4,7,5,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_619 : Excluded a [4,7,5,6,8,0] :=
  source_excluded a [4,7,5,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_620 : Excluded a [4,7,5,6,8,1] :=
  predecessor_excluded a [4,7,5,6,8,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_623 : Excluded a [4,7,5,6,8,2,0,1] :=
  predecessor_excluded a [4,7,5,6,8,2,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_624 : Excluded a [4,7,5,6,8,2,0,3] :=
  predecessor_excluded a [4,7,5,6,8,2,0,3] 0 6 7 3 (by decide) (by decide +kernel)

theorem node_622 : Excluded a [4,7,5,6,8,2,0] :=
  branch_excluded a [4,7,5,6,8,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,5,6,8,2,0,0] (by decide +kernel))
      node_623
      (invalid_excluded a [4,7,5,6,8,2,0,2] (by decide +kernel))
      node_624
      (invalid_excluded a [4,7,5,6,8,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,0,8] (by decide +kernel)))

theorem node_625 : Excluded a [4,7,5,6,8,2,1] :=
  source_excluded a [4,7,5,6,8,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_627 : Excluded a [4,7,5,6,8,2,3,0] :=
  predecessor_excluded a [4,7,5,6,8,2,3,0] 3 0 1 7 (by decide) (by decide +kernel)

def b_629 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 7
  | 2 => 5
  | 3 => 6
  | 4 => 8
  | 5 => 2
  | 6 => 3
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_629 : LosingRegion (edgeOf a b_629) 0 :=
  losingMask a b_629 0 1210109907375586416788480
    (by decide +kernel) (by decide +kernel)

theorem node_629 : Excluded a [4,7,5,6,8,2,3,1,0] :=
  losing_excluded a [4,7,5,6,8,2,3,1,0] (by decide) b_629 (by decide +kernel) 3 0 0 cert_629 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_629 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1210109907375586416788480 3 0; decide +kernel)

theorem node_628 : Excluded a [4,7,5,6,8,2,3,1] :=
  branch_excluded a [4,7,5,6,8,2,3,1] (by decide)
    (fin9_cases _
      node_629
      (invalid_excluded a [4,7,5,6,8,2,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,8] (by decide +kernel)))

theorem node_626 : Excluded a [4,7,5,6,8,2,3] :=
  branch_excluded a [4,7,5,6,8,2,3] (by decide)
    (fin9_cases _
      node_627
      node_628
      (invalid_excluded a [4,7,5,6,8,2,3,2] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,8] (by decide +kernel)))

theorem node_621 : Excluded a [4,7,5,6,8,2] :=
  branch_excluded a [4,7,5,6,8,2] (by decide)
    (fin9_cases _
      node_622
      node_625
      (invalid_excluded a [4,7,5,6,8,2,2] (by decide +kernel))
      node_626
      (invalid_excluded a [4,7,5,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,8] (by decide +kernel)))

theorem node_618 : Excluded a [4,7,5,6,8] :=
  branch_excluded a [4,7,5,6,8] (by decide)
    (fin9_cases _
      node_619
      node_620
      node_621
      (invalid_excluded a [4,7,5,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,8] (by decide +kernel)))

theorem node_613 : Excluded a [4,7,5,6] :=
  branch_excluded a [4,7,5,6] (by decide)
    (fin9_cases _
      node_614
      node_615
      node_616
      node_617
      (invalid_excluded a [4,7,5,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,7] (by decide +kernel))
      node_618)

theorem node_631 : Excluded a [4,7,5,8,0] :=
  source_excluded a [4,7,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_632 : Excluded a [4,7,5,8,1] :=
  source_excluded a [4,7,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_633 : Excluded a [4,7,5,8,2] :=
  source_excluded a [4,7,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_634 : Excluded a [4,7,5,8,3] :=
  source_excluded a [4,7,5,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_635 : Excluded a [4,7,5,8,6] :=
  predecessor_excluded a [4,7,5,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_630 : Excluded a [4,7,5,8] :=
  branch_excluded a [4,7,5,8] (by decide)
    (fin9_cases _
      node_631
      node_632
      node_633
      node_634
      (invalid_excluded a [4,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,5] (by decide +kernel))
      node_635
      (invalid_excluded a [4,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,8] (by decide +kernel)))

theorem node_609 : Excluded a [4,7,5] :=
  branch_excluded a [4,7,5] (by decide)
    (fin9_cases _
      node_610
      node_611
      node_612
      (invalid_excluded a [4,7,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,5] (by decide +kernel))
      node_613
      (invalid_excluded a [4,7,5,7] (by decide +kernel))
      node_630)

theorem node_637 : Excluded a [4,7,6,0] :=
  source_excluded a [4,7,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_638 : Excluded a [4,7,6,1] :=
  source_excluded a [4,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_640 : Excluded a [4,7,6,2,0] :=
  predecessor_excluded a [4,7,6,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_641 : Excluded a [4,7,6,2,1] :=
  source_excluded a [4,7,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_642 : Excluded a [4,7,6,2,3] :=
  source_excluded a [4,7,6,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_644 : Excluded a [4,7,6,2,8,0] :=
  predecessor_excluded a [4,7,6,2,8,0] 1 4 5 0 (by decide) (by decide +kernel)

theorem node_645 : Excluded a [4,7,6,2,8,1] :=
  predecessor_excluded a [4,7,6,2,8,1] 0 2 5 3 (by decide) (by decide +kernel)

theorem node_643 : Excluded a [4,7,6,2,8] :=
  branch_excluded a [4,7,6,2,8] (by decide)
    (fin9_cases _
      node_644
      node_645
      (invalid_excluded a [4,7,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,8] (by decide +kernel)))

theorem node_639 : Excluded a [4,7,6,2] :=
  branch_excluded a [4,7,6,2] (by decide)
    (fin9_cases _
      node_640
      node_641
      (invalid_excluded a [4,7,6,2,2] (by decide +kernel))
      node_642
      (invalid_excluded a [4,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,7] (by decide +kernel))
      node_643)

theorem node_646 : Excluded a [4,7,6,5] :=
  source_excluded a [4,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_649 : Excluded a [4,7,6,8,0,1] :=
  predecessor_excluded a [4,7,6,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_651 : Excluded a [4,7,6,8,0,2,1] :=
  source_excluded a [4,7,6,8,0,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_652 : Excluded a [4,7,6,8,0,2,3] :=
  predecessor_excluded a [4,7,6,8,0,2,3] 0 8 6 3 (by decide) (by decide +kernel)

def b_655 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 7
  | 2 => 6
  | 3 => 8
  | 4 => 0
  | 5 => 2
  | 6 => 5
  | 7 => 1
  | 8 => 3
  | _ => 0

def cert_655 : LosingRegion (edgeOf a b_655) 0 :=
  losingMask a b_655 0 1499270474929545044577280
    (by decide +kernel) (by decide +kernel)

theorem node_655 : Excluded a [4,7,6,8,0,2,5,1,3] :=
  losing_excluded a [4,7,6,8,0,2,5,1,3] (by decide) b_655 (by decide +kernel) 1 0 2 cert_655 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_655 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1499270474929545044577280 1 2; decide +kernel)

theorem node_654 : Excluded a [4,7,6,8,0,2,5,1] :=
  branch_excluded a [4,7,6,8,0,2,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,0,2,5,1,0] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,1,2] (by decide +kernel))
      node_655
      (invalid_excluded a [4,7,6,8,0,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,1,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,1,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,1,8] (by decide +kernel)))

theorem node_656 : Excluded a [4,7,6,8,0,2,5,3] :=
  source_excluded a [4,7,6,8,0,2,5,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_653 : Excluded a [4,7,6,8,0,2,5] :=
  branch_excluded a [4,7,6,8,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,0,2,5,0] (by decide +kernel))
      node_654
      (invalid_excluded a [4,7,6,8,0,2,5,2] (by decide +kernel))
      node_656
      (invalid_excluded a [4,7,6,8,0,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,5,8] (by decide +kernel)))

theorem node_650 : Excluded a [4,7,6,8,0,2] :=
  branch_excluded a [4,7,6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,0,2,0] (by decide +kernel))
      node_651
      (invalid_excluded a [4,7,6,8,0,2,2] (by decide +kernel))
      node_652
      (invalid_excluded a [4,7,6,8,0,2,4] (by decide +kernel))
      node_653
      (invalid_excluded a [4,7,6,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,2,8] (by decide +kernel)))

theorem node_648 : Excluded a [4,7,6,8,0] :=
  branch_excluded a [4,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,0,0] (by decide +kernel))
      node_649
      node_650
      (invalid_excluded a [4,7,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,8] (by decide +kernel)))

theorem node_657 : Excluded a [4,7,6,8,1] :=
  source_excluded a [4,7,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_658 : Excluded a [4,7,6,8,2] :=
  predecessor_excluded a [4,7,6,8,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_659 : Excluded a [4,7,6,8,3] :=
  source_excluded a [4,7,6,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_647 : Excluded a [4,7,6,8] :=
  branch_excluded a [4,7,6,8] (by decide)
    (fin9_cases _
      node_648
      node_657
      node_658
      node_659
      (invalid_excluded a [4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,8] (by decide +kernel)))

theorem node_636 : Excluded a [4,7,6] :=
  branch_excluded a [4,7,6] (by decide)
    (fin9_cases _
      node_637
      node_638
      node_639
      (invalid_excluded a [4,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,4] (by decide +kernel))
      node_646
      (invalid_excluded a [4,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,7] (by decide +kernel))
      node_647)

theorem node_660 : Excluded a [4,7,8] :=
  predecessor_excluded a [4,7,8] 0 8 1 2 (by decide) (by decide +kernel)

theorem node_606 : Excluded a [4,7] :=
  branch_excluded a [4,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,0] (by decide +kernel))
      node_607
      (invalid_excluded a [4,7,2] (by decide +kernel))
      node_608
      (invalid_excluded a [4,7,4] (by decide +kernel))
      node_609
      node_636
      (invalid_excluded a [4,7,7] (by decide +kernel))
      node_660)

theorem node_662 : Excluded a [4,8,1] :=
  source_excluded a [4,8,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_663 : Excluded a [4,8,3] :=
  predecessor_excluded a [4,8,3] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_665 : Excluded a [4,8,5,0] :=
  source_excluded a [4,8,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_666 : Excluded a [4,8,5,1] :=
  source_excluded a [4,8,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_667 : Excluded a [4,8,5,2] :=
  predecessor_excluded a [4,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_669 : Excluded a [4,8,5,6,0] :=
  source_excluded a [4,8,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_670 : Excluded a [4,8,5,6,1] :=
  source_excluded a [4,8,5,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_671 : Excluded a [4,8,5,6,2] :=
  source_excluded a [4,8,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_672 : Excluded a [4,8,5,6,3] :=
  source_excluded a [4,8,5,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_673 : Excluded a [4,8,5,6,7] :=
  predecessor_excluded a [4,8,5,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_668 : Excluded a [4,8,5,6] :=
  branch_excluded a [4,8,5,6] (by decide)
    (fin9_cases _
      node_669
      node_670
      node_671
      node_672
      (invalid_excluded a [4,8,5,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,6,6] (by decide +kernel))
      node_673
      (invalid_excluded a [4,8,5,6,8] (by decide +kernel)))

theorem node_675 : Excluded a [4,8,5,7,0] :=
  source_excluded a [4,8,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_676 : Excluded a [4,8,5,7,1] :=
  source_excluded a [4,8,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_677 : Excluded a [4,8,5,7,2] :=
  source_excluded a [4,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_678 : Excluded a [4,8,5,7,3] :=
  source_excluded a [4,8,5,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_680 : Excluded a [4,8,5,7,6,0] :=
  source_excluded a [4,8,5,7,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_681 : Excluded a [4,8,5,7,6,1] :=
  predecessor_excluded a [4,8,5,7,6,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_684 : Excluded a [4,8,5,7,6,2,0,1] :=
  source_excluded a [4,8,5,7,6,2,0,1] 7 0 1 (by decide) (by decide +kernel)

def b_686 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 5
  | 3 => 7
  | 4 => 6
  | 5 => 2
  | 6 => 0
  | 7 => 3
  | 8 => 1
  | _ => 0

def cert_686 : LosingRegion (edgeOf a b_686) 0 :=
  losingMask a b_686 0 1212487195498110579115008
    (by decide +kernel) (by decide +kernel)

theorem node_686 : Excluded a [4,8,5,7,6,2,0,3,1] :=
  losing_excluded a [4,8,5,7,6,2,0,3,1] (by decide) b_686 (by decide +kernel) 3 0 0 cert_686 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_686 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1212487195498110579115008 3 0; decide +kernel)

theorem node_685 : Excluded a [4,8,5,7,6,2,0,3] :=
  branch_excluded a [4,8,5,7,6,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,5,7,6,2,0,3,0] (by decide +kernel))
      node_686
      (invalid_excluded a [4,8,5,7,6,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,3,8] (by decide +kernel)))

theorem node_683 : Excluded a [4,8,5,7,6,2,0] :=
  branch_excluded a [4,8,5,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,5,7,6,2,0,0] (by decide +kernel))
      node_684
      (invalid_excluded a [4,8,5,7,6,2,0,2] (by decide +kernel))
      node_685
      (invalid_excluded a [4,8,5,7,6,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,0,8] (by decide +kernel)))

theorem node_687 : Excluded a [4,8,5,7,6,2,1] :=
  predecessor_excluded a [4,8,5,7,6,2,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_688 : Excluded a [4,8,5,7,6,2,3] :=
  source_excluded a [4,8,5,7,6,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_682 : Excluded a [4,8,5,7,6,2] :=
  branch_excluded a [4,8,5,7,6,2] (by decide)
    (fin9_cases _
      node_683
      node_687
      (invalid_excluded a [4,8,5,7,6,2,2] (by decide +kernel))
      node_688
      (invalid_excluded a [4,8,5,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,2,8] (by decide +kernel)))

theorem node_679 : Excluded a [4,8,5,7,6] :=
  branch_excluded a [4,8,5,7,6] (by decide)
    (fin9_cases _
      node_680
      node_681
      node_682
      (invalid_excluded a [4,8,5,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,8] (by decide +kernel)))

theorem node_674 : Excluded a [4,8,5,7] :=
  branch_excluded a [4,8,5,7] (by decide)
    (fin9_cases _
      node_675
      node_676
      node_677
      node_678
      (invalid_excluded a [4,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,5] (by decide +kernel))
      node_679
      (invalid_excluded a [4,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,8] (by decide +kernel)))

theorem node_664 : Excluded a [4,8,5] :=
  branch_excluded a [4,8,5] (by decide)
    (fin9_cases _
      node_665
      node_666
      node_667
      (invalid_excluded a [4,8,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,5] (by decide +kernel))
      node_668
      node_674
      (invalid_excluded a [4,8,5,8] (by decide +kernel)))

theorem node_689 : Excluded a [4,8,6] :=
  predecessor_excluded a [4,8,6] 0 6 1 2 (by decide) (by decide +kernel)

theorem node_691 : Excluded a [4,8,7,0] :=
  source_excluded a [4,8,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_692 : Excluded a [4,8,7,1] :=
  source_excluded a [4,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_694 : Excluded a [4,8,7,2,0] :=
  predecessor_excluded a [4,8,7,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_695 : Excluded a [4,8,7,2,1] :=
  source_excluded a [4,8,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_696 : Excluded a [4,8,7,2,3] :=
  source_excluded a [4,8,7,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_698 : Excluded a [4,8,7,2,6,0] :=
  predecessor_excluded a [4,8,7,2,6,0] 1 4 5 0 (by decide) (by decide +kernel)

theorem node_699 : Excluded a [4,8,7,2,6,1] :=
  predecessor_excluded a [4,8,7,2,6,1] 0 2 5 3 (by decide) (by decide +kernel)

theorem node_697 : Excluded a [4,8,7,2,6] :=
  branch_excluded a [4,8,7,2,6] (by decide)
    (fin9_cases _
      node_698
      node_699
      (invalid_excluded a [4,8,7,2,6,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,6,8] (by decide +kernel)))

theorem node_693 : Excluded a [4,8,7,2] :=
  branch_excluded a [4,8,7,2] (by decide)
    (fin9_cases _
      node_694
      node_695
      (invalid_excluded a [4,8,7,2,2] (by decide +kernel))
      node_696
      (invalid_excluded a [4,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,5] (by decide +kernel))
      node_697
      (invalid_excluded a [4,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,8] (by decide +kernel)))

theorem node_700 : Excluded a [4,8,7,5] :=
  source_excluded a [4,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_703 : Excluded a [4,8,7,6,0,1] :=
  predecessor_excluded a [4,8,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_705 : Excluded a [4,8,7,6,0,2,1] :=
  predecessor_excluded a [4,8,7,6,0,2,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_707 : Excluded a [4,8,7,6,0,2,3,1] :=
  source_excluded a [4,8,7,6,0,2,3,1] 7 0 1 (by decide) (by decide +kernel)

def b_709 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 7
  | 3 => 6
  | 4 => 0
  | 5 => 2
  | 6 => 3
  | 7 => 5
  | 8 => 1
  | _ => 0

def cert_709 : LosingRegion (edgeOf a b_709) 0 :=
  losingMask a b_709 0 2074799792758035766594560
    (by decide +kernel) (by decide +kernel)

theorem node_709 : Excluded a [4,8,7,6,0,2,3,5,1] :=
  losing_excluded a [4,8,7,6,0,2,3,5,1] (by decide) b_709 (by decide +kernel) 1 0 2 cert_709 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_709 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2074799792758035766594560 1 2; decide +kernel)

theorem node_708 : Excluded a [4,8,7,6,0,2,3,5] :=
  branch_excluded a [4,8,7,6,0,2,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,6,0,2,3,5,0] (by decide +kernel))
      node_709
      (invalid_excluded a [4,8,7,6,0,2,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,5,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,5,8] (by decide +kernel)))

theorem node_706 : Excluded a [4,8,7,6,0,2,3] :=
  branch_excluded a [4,8,7,6,0,2,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,6,0,2,3,0] (by decide +kernel))
      node_707
      (invalid_excluded a [4,8,7,6,0,2,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,4] (by decide +kernel))
      node_708
      (invalid_excluded a [4,8,7,6,0,2,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,3,8] (by decide +kernel)))

theorem node_710 : Excluded a [4,8,7,6,0,2,5] :=
  predecessor_excluded a [4,8,7,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_704 : Excluded a [4,8,7,6,0,2] :=
  branch_excluded a [4,8,7,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,6,0,2,0] (by decide +kernel))
      node_705
      (invalid_excluded a [4,8,7,6,0,2,2] (by decide +kernel))
      node_706
      (invalid_excluded a [4,8,7,6,0,2,4] (by decide +kernel))
      node_710
      (invalid_excluded a [4,8,7,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,2,8] (by decide +kernel)))

theorem node_702 : Excluded a [4,8,7,6,0] :=
  branch_excluded a [4,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,6,0,0] (by decide +kernel))
      node_703
      node_704
      (invalid_excluded a [4,8,7,6,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,8] (by decide +kernel)))

theorem node_711 : Excluded a [4,8,7,6,1] :=
  source_excluded a [4,8,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_712 : Excluded a [4,8,7,6,2] :=
  predecessor_excluded a [4,8,7,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_713 : Excluded a [4,8,7,6,3] :=
  source_excluded a [4,8,7,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_701 : Excluded a [4,8,7,6] :=
  branch_excluded a [4,8,7,6] (by decide)
    (fin9_cases _
      node_702
      node_711
      node_712
      node_713
      (invalid_excluded a [4,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,8] (by decide +kernel)))

theorem node_690 : Excluded a [4,8,7] :=
  branch_excluded a [4,8,7] (by decide)
    (fin9_cases _
      node_691
      node_692
      node_693
      (invalid_excluded a [4,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,4] (by decide +kernel))
      node_700
      node_701
      (invalid_excluded a [4,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,8] (by decide +kernel)))

theorem node_661 : Excluded a [4,8] :=
  branch_excluded a [4,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,0] (by decide +kernel))
      node_662
      (invalid_excluded a [4,8,2] (by decide +kernel))
      node_663
      (invalid_excluded a [4,8,4] (by decide +kernel))
      node_664
      node_689
      node_690
      (invalid_excluded a [4,8,8] (by decide +kernel)))

theorem node_384 : Excluded a [4] :=
  branch_excluded a [4] (by decide)
    (fin9_cases _
      node_385
      (invalid_excluded a [4,1] (by decide +kernel))
      (invalid_excluded a [4,2] (by decide +kernel))
      node_386
      (invalid_excluded a [4,4] (by decide +kernel))
      node_550
      node_551
      node_606
      node_661)

theorem node_715 : Excluded a [5,0] :=
  source_excluded a [5,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_716 : Excluded a [5,3] :=
  predecessor_excluded a [5,3] 2 3 0 1 (by decide) (by decide +kernel)

theorem node_718 : Excluded a [5,4,1] :=
  source_excluded a [5,4,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_720 : Excluded a [5,4,3,0] :=
  source_excluded a [5,4,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_721 : Excluded a [5,4,3,1] :=
  source_excluded a [5,4,3,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_722 : Excluded a [5,4,3,2] :=
  source_excluded a [5,4,3,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_724 : Excluded a [5,4,3,6,0] :=
  source_excluded a [5,4,3,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_725 : Excluded a [5,4,3,6,1] :=
  source_excluded a [5,4,3,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_726 : Excluded a [5,4,3,6,2] :=
  source_excluded a [5,4,3,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_727 : Excluded a [5,4,3,6,7] :=
  predecessor_excluded a [5,4,3,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_729 : Excluded a [5,4,3,6,8,0] :=
  source_excluded a [5,4,3,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_730 : Excluded a [5,4,3,6,8,1] :=
  source_excluded a [5,4,3,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_731 : Excluded a [5,4,3,6,8,2] :=
  source_excluded a [5,4,3,6,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_734 : Excluded a [5,4,3,6,8,7,0,1] :=
  predecessor_excluded a [5,4,3,6,8,7,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_736 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_736 : LosingRegion (edgeOf a b_736) 0 :=
  losingMask a b_736 0 1512339026974287451982848
    (by decide +kernel) (by decide +kernel)

theorem node_736 : Excluded a [5,4,3,6,8,7,0,2,1] :=
  losing_excluded a [5,4,3,6,8,7,0,2,1] (by decide) b_736 (by decide +kernel) 1 0 2 cert_736 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_736 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1512339026974287451982848 1 2; decide +kernel)

theorem node_735 : Excluded a [5,4,3,6,8,7,0,2] :=
  branch_excluded a [5,4,3,6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,6,8,7,0,2,0] (by decide +kernel))
      node_736
      (invalid_excluded a [5,4,3,6,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,2,8] (by decide +kernel)))

theorem node_733 : Excluded a [5,4,3,6,8,7,0] :=
  branch_excluded a [5,4,3,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,6,8,7,0,0] (by decide +kernel))
      node_734
      node_735
      (invalid_excluded a [5,4,3,6,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,0,8] (by decide +kernel)))

def b_739 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_739 : LosingRegion (edgeOf a b_739) 0 :=
  losingMask a b_739 0 1210109877908713044575232
    (by decide +kernel) (by decide +kernel)

theorem node_739 : Excluded a [5,4,3,6,8,7,1,0,2] :=
  losing_excluded a [5,4,3,6,8,7,1,0,2] (by decide) b_739 (by decide +kernel) 1 0 8 cert_739 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_739 1 0 ∧ 8 ≠ 1 ∧ maskRegion 1210109877908713044575232 1 8; decide +kernel)

theorem node_738 : Excluded a [5,4,3,6,8,7,1,0] :=
  branch_excluded a [5,4,3,6,8,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,6,8,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,0,1] (by decide +kernel))
      node_739
      (invalid_excluded a [5,4,3,6,8,7,1,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,0,8] (by decide +kernel)))

theorem node_740 : Excluded a [5,4,3,6,8,7,1,2] :=
  predecessor_excluded a [5,4,3,6,8,7,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_737 : Excluded a [5,4,3,6,8,7,1] :=
  branch_excluded a [5,4,3,6,8,7,1] (by decide)
    (fin9_cases _
      node_738
      (invalid_excluded a [5,4,3,6,8,7,1,1] (by decide +kernel))
      node_740
      (invalid_excluded a [5,4,3,6,8,7,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,1,8] (by decide +kernel)))

theorem node_742 : Excluded a [5,4,3,6,8,7,2,0] :=
  predecessor_excluded a [5,4,3,6,8,7,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_744 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 6
  | 4 => 8
  | 5 => 7
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_744 : LosingRegion (edgeOf a b_744) 0 :=
  losingMask a b_744 0 1212468764877266386715648
    (by decide +kernel) (by decide +kernel)

theorem node_744 : Excluded a [5,4,3,6,8,7,2,1,0] :=
  losing_excluded a [5,4,3,6,8,7,2,1,0] (by decide) b_744 (by decide +kernel) 1 0 6 cert_744 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_744 1 0 ∧ 6 ≠ 1 ∧ maskRegion 1212468764877266386715648 1 6; decide +kernel)

theorem node_743 : Excluded a [5,4,3,6,8,7,2,1] :=
  branch_excluded a [5,4,3,6,8,7,2,1] (by decide)
    (fin9_cases _
      node_744
      (invalid_excluded a [5,4,3,6,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,1,8] (by decide +kernel)))

theorem node_741 : Excluded a [5,4,3,6,8,7,2] :=
  branch_excluded a [5,4,3,6,8,7,2] (by decide)
    (fin9_cases _
      node_742
      node_743
      (invalid_excluded a [5,4,3,6,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,2,8] (by decide +kernel)))

theorem node_732 : Excluded a [5,4,3,6,8,7] :=
  branch_excluded a [5,4,3,6,8,7] (by decide)
    (fin9_cases _
      node_733
      node_737
      node_741
      (invalid_excluded a [5,4,3,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,7,8] (by decide +kernel)))

theorem node_728 : Excluded a [5,4,3,6,8] :=
  branch_excluded a [5,4,3,6,8] (by decide)
    (fin9_cases _
      node_729
      node_730
      node_731
      (invalid_excluded a [5,4,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,6] (by decide +kernel))
      node_732
      (invalid_excluded a [5,4,3,6,8,8] (by decide +kernel)))

theorem node_723 : Excluded a [5,4,3,6] :=
  branch_excluded a [5,4,3,6] (by decide)
    (fin9_cases _
      node_724
      node_725
      node_726
      (invalid_excluded a [5,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,6] (by decide +kernel))
      node_727
      node_728)

theorem node_746 : Excluded a [5,4,3,7,0] :=
  source_excluded a [5,4,3,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_747 : Excluded a [5,4,3,7,1] :=
  source_excluded a [5,4,3,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_748 : Excluded a [5,4,3,7,2] :=
  source_excluded a [5,4,3,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_750 : Excluded a [5,4,3,7,6,0] :=
  source_excluded a [5,4,3,7,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_751 : Excluded a [5,4,3,7,6,1] :=
  source_excluded a [5,4,3,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_752 : Excluded a [5,4,3,7,6,2] :=
  source_excluded a [5,4,3,7,6,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_755 : Excluded a [5,4,3,7,6,8,0,1] :=
  predecessor_excluded a [5,4,3,7,6,8,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_757 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_757 : LosingRegion (edgeOf a b_757) 0 :=
  losingMask a b_757 0 1512339036535073631437824
    (by decide +kernel) (by decide +kernel)

theorem node_757 : Excluded a [5,4,3,7,6,8,0,2,1] :=
  losing_excluded a [5,4,3,7,6,8,0,2,1] (by decide) b_757 (by decide +kernel) 1 0 7 cert_757 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_757 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1512339036535073631437824 1 7; decide +kernel)

theorem node_756 : Excluded a [5,4,3,7,6,8,0,2] :=
  branch_excluded a [5,4,3,7,6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,7,6,8,0,2,0] (by decide +kernel))
      node_757
      (invalid_excluded a [5,4,3,7,6,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,2,8] (by decide +kernel)))

theorem node_754 : Excluded a [5,4,3,7,6,8,0] :=
  branch_excluded a [5,4,3,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,7,6,8,0,0] (by decide +kernel))
      node_755
      node_756
      (invalid_excluded a [5,4,3,7,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,0,8] (by decide +kernel)))

def b_760 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_760 : LosingRegion (edgeOf a b_760) 0 :=
  losingMask a b_760 0 1210109884669021633252352
    (by decide +kernel) (by decide +kernel)

theorem node_760 : Excluded a [5,4,3,7,6,8,1,0,2] :=
  losing_excluded a [5,4,3,7,6,8,1,0,2] (by decide) b_760 (by decide +kernel) 1 0 2 cert_760 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_760 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1210109884669021633252352 1 2; decide +kernel)

theorem node_759 : Excluded a [5,4,3,7,6,8,1,0] :=
  branch_excluded a [5,4,3,7,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,7,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,0,1] (by decide +kernel))
      node_760
      (invalid_excluded a [5,4,3,7,6,8,1,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,0,8] (by decide +kernel)))

theorem node_761 : Excluded a [5,4,3,7,6,8,1,2] :=
  predecessor_excluded a [5,4,3,7,6,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_758 : Excluded a [5,4,3,7,6,8,1] :=
  branch_excluded a [5,4,3,7,6,8,1] (by decide)
    (fin9_cases _
      node_759
      (invalid_excluded a [5,4,3,7,6,8,1,1] (by decide +kernel))
      node_761
      (invalid_excluded a [5,4,3,7,6,8,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,1,8] (by decide +kernel)))

theorem node_763 : Excluded a [5,4,3,7,6,8,2,0] :=
  predecessor_excluded a [5,4,3,7,6,8,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_765 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_765 : LosingRegion (edgeOf a b_765) 0 :=
  losingMask a b_765 0 1212468762058140047934464
    (by decide +kernel) (by decide +kernel)

theorem node_765 : Excluded a [5,4,3,7,6,8,2,1,0] :=
  losing_excluded a [5,4,3,7,6,8,2,1,0] (by decide) b_765 (by decide +kernel) 1 0 6 cert_765 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_765 1 0 ∧ 6 ≠ 1 ∧ maskRegion 1212468762058140047934464 1 6; decide +kernel)

theorem node_764 : Excluded a [5,4,3,7,6,8,2,1] :=
  branch_excluded a [5,4,3,7,6,8,2,1] (by decide)
    (fin9_cases _
      node_765
      (invalid_excluded a [5,4,3,7,6,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,1,8] (by decide +kernel)))

theorem node_762 : Excluded a [5,4,3,7,6,8,2] :=
  branch_excluded a [5,4,3,7,6,8,2] (by decide)
    (fin9_cases _
      node_763
      node_764
      (invalid_excluded a [5,4,3,7,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,2,8] (by decide +kernel)))

theorem node_753 : Excluded a [5,4,3,7,6,8] :=
  branch_excluded a [5,4,3,7,6,8] (by decide)
    (fin9_cases _
      node_754
      node_758
      node_762
      (invalid_excluded a [5,4,3,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,8,8] (by decide +kernel)))

theorem node_749 : Excluded a [5,4,3,7,6] :=
  branch_excluded a [5,4,3,7,6] (by decide)
    (fin9_cases _
      node_750
      node_751
      node_752
      (invalid_excluded a [5,4,3,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,6,7] (by decide +kernel))
      node_753)

theorem node_766 : Excluded a [5,4,3,7,8] :=
  predecessor_excluded a [5,4,3,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_745 : Excluded a [5,4,3,7] :=
  branch_excluded a [5,4,3,7] (by decide)
    (fin9_cases _
      node_746
      node_747
      node_748
      (invalid_excluded a [5,4,3,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,5] (by decide +kernel))
      node_749
      (invalid_excluded a [5,4,3,7,7] (by decide +kernel))
      node_766)

theorem node_768 : Excluded a [5,4,3,8,0] :=
  source_excluded a [5,4,3,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_769 : Excluded a [5,4,3,8,1] :=
  source_excluded a [5,4,3,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_770 : Excluded a [5,4,3,8,2] :=
  source_excluded a [5,4,3,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_771 : Excluded a [5,4,3,8,6] :=
  predecessor_excluded a [5,4,3,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_773 : Excluded a [5,4,3,8,7,0] :=
  source_excluded a [5,4,3,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_774 : Excluded a [5,4,3,8,7,1] :=
  source_excluded a [5,4,3,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_775 : Excluded a [5,4,3,8,7,2] :=
  source_excluded a [5,4,3,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_778 : Excluded a [5,4,3,8,7,6,0,1] :=
  predecessor_excluded a [5,4,3,8,7,6,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_780 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 8
  | 4 => 7
  | 5 => 6
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_780 : LosingRegion (edgeOf a b_780) 0 :=
  losingMask a b_780 0 1512339031459766612329472
    (by decide +kernel) (by decide +kernel)

theorem node_780 : Excluded a [5,4,3,8,7,6,0,2,1] :=
  losing_excluded a [5,4,3,8,7,6,0,2,1] (by decide) b_780 (by decide +kernel) 1 0 7 cert_780 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_780 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1512339031459766612329472 1 7; decide +kernel)

theorem node_779 : Excluded a [5,4,3,8,7,6,0,2] :=
  branch_excluded a [5,4,3,8,7,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,8,7,6,0,2,0] (by decide +kernel))
      node_780
      (invalid_excluded a [5,4,3,8,7,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,2,8] (by decide +kernel)))

theorem node_777 : Excluded a [5,4,3,8,7,6,0] :=
  branch_excluded a [5,4,3,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,8,7,6,0,0] (by decide +kernel))
      node_778
      node_779
      (invalid_excluded a [5,4,3,8,7,6,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,0,8] (by decide +kernel)))

def b_783 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 8
  | 4 => 7
  | 5 => 6
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_783 : LosingRegion (edgeOf a b_783) 0 :=
  losingMask a b_783 0 1210109887465655228302336
    (by decide +kernel) (by decide +kernel)

theorem node_783 : Excluded a [5,4,3,8,7,6,1,0,2] :=
  losing_excluded a [5,4,3,8,7,6,1,0,2] (by decide) b_783 (by decide +kernel) 1 0 8 cert_783 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_783 1 0 ∧ 8 ≠ 1 ∧ maskRegion 1210109887465655228302336 1 8; decide +kernel)

theorem node_782 : Excluded a [5,4,3,8,7,6,1,0] :=
  branch_excluded a [5,4,3,8,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,8,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,0,1] (by decide +kernel))
      node_783
      (invalid_excluded a [5,4,3,8,7,6,1,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,0,8] (by decide +kernel)))

theorem node_784 : Excluded a [5,4,3,8,7,6,1,2] :=
  predecessor_excluded a [5,4,3,8,7,6,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_781 : Excluded a [5,4,3,8,7,6,1] :=
  branch_excluded a [5,4,3,8,7,6,1] (by decide)
    (fin9_cases _
      node_782
      (invalid_excluded a [5,4,3,8,7,6,1,1] (by decide +kernel))
      node_784
      (invalid_excluded a [5,4,3,8,7,6,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,1,8] (by decide +kernel)))

theorem node_786 : Excluded a [5,4,3,8,7,6,2,0] :=
  predecessor_excluded a [5,4,3,8,7,6,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_788 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 8
  | 4 => 7
  | 5 => 6
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_788 : LosingRegion (edgeOf a b_788) 0 :=
  losingMask a b_788 0 1212468759815673198185472
    (by decide +kernel) (by decide +kernel)

theorem node_788 : Excluded a [5,4,3,8,7,6,2,1,0] :=
  losing_excluded a [5,4,3,8,7,6,2,1,0] (by decide) b_788 (by decide +kernel) 1 0 2 cert_788 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_788 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212468759815673198185472 1 2; decide +kernel)

theorem node_787 : Excluded a [5,4,3,8,7,6,2,1] :=
  branch_excluded a [5,4,3,8,7,6,2,1] (by decide)
    (fin9_cases _
      node_788
      (invalid_excluded a [5,4,3,8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,1,8] (by decide +kernel)))

theorem node_785 : Excluded a [5,4,3,8,7,6,2] :=
  branch_excluded a [5,4,3,8,7,6,2] (by decide)
    (fin9_cases _
      node_786
      node_787
      (invalid_excluded a [5,4,3,8,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,2,8] (by decide +kernel)))

theorem node_776 : Excluded a [5,4,3,8,7,6] :=
  branch_excluded a [5,4,3,8,7,6] (by decide)
    (fin9_cases _
      node_777
      node_781
      node_785
      (invalid_excluded a [5,4,3,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6,8] (by decide +kernel)))

theorem node_772 : Excluded a [5,4,3,8,7] :=
  branch_excluded a [5,4,3,8,7] (by decide)
    (fin9_cases _
      node_773
      node_774
      node_775
      (invalid_excluded a [5,4,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,5] (by decide +kernel))
      node_776
      (invalid_excluded a [5,4,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,8] (by decide +kernel)))

theorem node_767 : Excluded a [5,4,3,8] :=
  branch_excluded a [5,4,3,8] (by decide)
    (fin9_cases _
      node_768
      node_769
      node_770
      (invalid_excluded a [5,4,3,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,5] (by decide +kernel))
      node_771
      node_772
      (invalid_excluded a [5,4,3,8,8] (by decide +kernel)))

theorem node_719 : Excluded a [5,4,3] :=
  branch_excluded a [5,4,3] (by decide)
    (fin9_cases _
      node_720
      node_721
      node_722
      (invalid_excluded a [5,4,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,5] (by decide +kernel))
      node_723
      node_745
      node_767)

theorem node_790 : Excluded a [5,4,6,0] :=
  predecessor_excluded a [5,4,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_791 : Excluded a [5,4,6,1] :=
  source_excluded a [5,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_792 : Excluded a [5,4,6,2] :=
  source_excluded a [5,4,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_794 : Excluded a [5,4,6,7,0] :=
  source_excluded a [5,4,6,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_795 : Excluded a [5,4,6,7,1] :=
  source_excluded a [5,4,6,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_796 : Excluded a [5,4,6,7,2] :=
  source_excluded a [5,4,6,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_797 : Excluded a [5,4,6,7,3] :=
  source_excluded a [5,4,6,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_798 : Excluded a [5,4,6,7,8] :=
  predecessor_excluded a [5,4,6,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_793 : Excluded a [5,4,6,7] :=
  branch_excluded a [5,4,6,7] (by decide)
    (fin9_cases _
      node_794
      node_795
      node_796
      node_797
      (invalid_excluded a [5,4,6,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,7] (by decide +kernel))
      node_798)

theorem node_800 : Excluded a [5,4,6,8,0] :=
  source_excluded a [5,4,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_801 : Excluded a [5,4,6,8,1] :=
  source_excluded a [5,4,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_802 : Excluded a [5,4,6,8,2] :=
  source_excluded a [5,4,6,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_803 : Excluded a [5,4,6,8,3] :=
  source_excluded a [5,4,6,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_806 : Excluded a [5,4,6,8,7,0,1] :=
  predecessor_excluded a [5,4,6,8,7,0,1] 3 1 2 6 (by decide) (by decide +kernel)

def b_809 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 6
  | 3 => 8
  | 4 => 7
  | 5 => 0
  | 6 => 2
  | 7 => 1
  | 8 => 3
  | _ => 0

def cert_809 : LosingRegion (edgeOf a b_809) 0 :=
  losingMask a b_809 0 2150513462878193954327552
    (by decide +kernel) (by decide +kernel)

theorem node_809 : Excluded a [5,4,6,8,7,0,2,1,3] :=
  losing_excluded a [5,4,6,8,7,0,2,1,3] (by decide) b_809 (by decide +kernel) 1 0 2 cert_809 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_809 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2150513462878193954327552 1 2; decide +kernel)

theorem node_808 : Excluded a [5,4,6,8,7,0,2,1] :=
  branch_excluded a [5,4,6,8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,6,8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,2] (by decide +kernel))
      node_809
      (invalid_excluded a [5,4,6,8,7,0,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,8] (by decide +kernel)))

theorem node_810 : Excluded a [5,4,6,8,7,0,2,3] :=
  source_excluded a [5,4,6,8,7,0,2,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_807 : Excluded a [5,4,6,8,7,0,2] :=
  branch_excluded a [5,4,6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,6,8,7,0,2,0] (by decide +kernel))
      node_808
      (invalid_excluded a [5,4,6,8,7,0,2,2] (by decide +kernel))
      node_810
      (invalid_excluded a [5,4,6,8,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,8] (by decide +kernel)))

theorem node_811 : Excluded a [5,4,6,8,7,0,3] :=
  predecessor_excluded a [5,4,6,8,7,0,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_805 : Excluded a [5,4,6,8,7,0] :=
  branch_excluded a [5,4,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,6,8,7,0,0] (by decide +kernel))
      node_806
      node_807
      node_811
      (invalid_excluded a [5,4,6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,8] (by decide +kernel)))

theorem node_812 : Excluded a [5,4,6,8,7,1] :=
  source_excluded a [5,4,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_813 : Excluded a [5,4,6,8,7,2] :=
  predecessor_excluded a [5,4,6,8,7,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_804 : Excluded a [5,4,6,8,7] :=
  branch_excluded a [5,4,6,8,7] (by decide)
    (fin9_cases _
      node_805
      node_812
      node_813
      (invalid_excluded a [5,4,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,8] (by decide +kernel)))

theorem node_799 : Excluded a [5,4,6,8] :=
  branch_excluded a [5,4,6,8] (by decide)
    (fin9_cases _
      node_800
      node_801
      node_802
      node_803
      (invalid_excluded a [5,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,6] (by decide +kernel))
      node_804
      (invalid_excluded a [5,4,6,8,8] (by decide +kernel)))

theorem node_789 : Excluded a [5,4,6] :=
  branch_excluded a [5,4,6] (by decide)
    (fin9_cases _
      node_790
      node_791
      node_792
      (invalid_excluded a [5,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,6] (by decide +kernel))
      node_793
      node_799)

theorem node_815 : Excluded a [5,4,7,0] :=
  predecessor_excluded a [5,4,7,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_816 : Excluded a [5,4,7,1] :=
  source_excluded a [5,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_817 : Excluded a [5,4,7,2] :=
  source_excluded a [5,4,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_819 : Excluded a [5,4,7,6,0] :=
  source_excluded a [5,4,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_820 : Excluded a [5,4,7,6,1] :=
  source_excluded a [5,4,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_821 : Excluded a [5,4,7,6,2] :=
  source_excluded a [5,4,7,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_822 : Excluded a [5,4,7,6,3] :=
  source_excluded a [5,4,7,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_826 : Excluded a [5,4,7,6,8,0,1,2] :=
  predecessor_excluded a [5,4,7,6,8,0,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_827 : Excluded a [5,4,7,6,8,0,1,3] :=
  predecessor_excluded a [5,4,7,6,8,0,1,3] 0 6 7 3 (by decide) (by decide +kernel)

theorem node_825 : Excluded a [5,4,7,6,8,0,1] :=
  branch_excluded a [5,4,7,6,8,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,7,6,8,0,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,1,1] (by decide +kernel))
      node_826
      node_827
      (invalid_excluded a [5,4,7,6,8,0,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,1,8] (by decide +kernel)))

theorem node_828 : Excluded a [5,4,7,6,8,0,2] :=
  source_excluded a [5,4,7,6,8,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_830 : Excluded a [5,4,7,6,8,0,3,1] :=
  predecessor_excluded a [5,4,7,6,8,0,3,1] 3 1 2 7 (by decide) (by decide +kernel)

def b_832 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 7
  | 3 => 6
  | 4 => 8
  | 5 => 0
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_832 : LosingRegion (edgeOf a b_832) 0 :=
  losingMask a b_832 0 1847689424335567250787328
    (by decide +kernel) (by decide +kernel)

theorem node_832 : Excluded a [5,4,7,6,8,0,3,2,1] :=
  losing_excluded a [5,4,7,6,8,0,3,2,1] (by decide) b_832 (by decide +kernel) 1 0 2 cert_832 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_832 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1847689424335567250787328 1 2; decide +kernel)

theorem node_831 : Excluded a [5,4,7,6,8,0,3,2] :=
  branch_excluded a [5,4,7,6,8,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,7,6,8,0,3,2,0] (by decide +kernel))
      node_832
      (invalid_excluded a [5,4,7,6,8,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,8] (by decide +kernel)))

theorem node_829 : Excluded a [5,4,7,6,8,0,3] :=
  branch_excluded a [5,4,7,6,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,7,6,8,0,3,0] (by decide +kernel))
      node_830
      node_831
      (invalid_excluded a [5,4,7,6,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,8] (by decide +kernel)))

theorem node_824 : Excluded a [5,4,7,6,8,0] :=
  branch_excluded a [5,4,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,7,6,8,0,0] (by decide +kernel))
      node_825
      node_828
      node_829
      (invalid_excluded a [5,4,7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,8] (by decide +kernel)))

theorem node_833 : Excluded a [5,4,7,6,8,1] :=
  source_excluded a [5,4,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_834 : Excluded a [5,4,7,6,8,2] :=
  predecessor_excluded a [5,4,7,6,8,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_823 : Excluded a [5,4,7,6,8] :=
  branch_excluded a [5,4,7,6,8] (by decide)
    (fin9_cases _
      node_824
      node_833
      node_834
      (invalid_excluded a [5,4,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,8] (by decide +kernel)))

theorem node_818 : Excluded a [5,4,7,6] :=
  branch_excluded a [5,4,7,6] (by decide)
    (fin9_cases _
      node_819
      node_820
      node_821
      node_822
      (invalid_excluded a [5,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,7] (by decide +kernel))
      node_823)

theorem node_836 : Excluded a [5,4,7,8,0] :=
  source_excluded a [5,4,7,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_837 : Excluded a [5,4,7,8,1] :=
  source_excluded a [5,4,7,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_838 : Excluded a [5,4,7,8,2] :=
  source_excluded a [5,4,7,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_839 : Excluded a [5,4,7,8,3] :=
  source_excluded a [5,4,7,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_840 : Excluded a [5,4,7,8,6] :=
  predecessor_excluded a [5,4,7,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_835 : Excluded a [5,4,7,8] :=
  branch_excluded a [5,4,7,8] (by decide)
    (fin9_cases _
      node_836
      node_837
      node_838
      node_839
      (invalid_excluded a [5,4,7,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,8,5] (by decide +kernel))
      node_840
      (invalid_excluded a [5,4,7,8,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,8,8] (by decide +kernel)))

theorem node_814 : Excluded a [5,4,7] :=
  branch_excluded a [5,4,7] (by decide)
    (fin9_cases _
      node_815
      node_816
      node_817
      (invalid_excluded a [5,4,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,5] (by decide +kernel))
      node_818
      (invalid_excluded a [5,4,7,7] (by decide +kernel))
      node_835)

theorem node_842 : Excluded a [5,4,8,0] :=
  predecessor_excluded a [5,4,8,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_843 : Excluded a [5,4,8,1] :=
  source_excluded a [5,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_844 : Excluded a [5,4,8,2] :=
  source_excluded a [5,4,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_846 : Excluded a [5,4,8,6,0] :=
  source_excluded a [5,4,8,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_847 : Excluded a [5,4,8,6,1] :=
  source_excluded a [5,4,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_848 : Excluded a [5,4,8,6,2] :=
  source_excluded a [5,4,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_849 : Excluded a [5,4,8,6,3] :=
  source_excluded a [5,4,8,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_850 : Excluded a [5,4,8,6,7] :=
  predecessor_excluded a [5,4,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_845 : Excluded a [5,4,8,6] :=
  branch_excluded a [5,4,8,6] (by decide)
    (fin9_cases _
      node_846
      node_847
      node_848
      node_849
      (invalid_excluded a [5,4,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,6,6] (by decide +kernel))
      node_850
      (invalid_excluded a [5,4,8,6,8] (by decide +kernel)))

theorem node_852 : Excluded a [5,4,8,7,0] :=
  source_excluded a [5,4,8,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_853 : Excluded a [5,4,8,7,1] :=
  source_excluded a [5,4,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_854 : Excluded a [5,4,8,7,2] :=
  source_excluded a [5,4,8,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_855 : Excluded a [5,4,8,7,3] :=
  source_excluded a [5,4,8,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_859 : Excluded a [5,4,8,7,6,0,1,2] :=
  source_excluded a [5,4,8,7,6,0,1,2] 7 0 2 (by decide) (by decide +kernel)

def b_861 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 8
  | 3 => 7
  | 4 => 6
  | 5 => 0
  | 6 => 1
  | 7 => 3
  | 8 => 2
  | _ => 0

def cert_861 : LosingRegion (edgeOf a b_861) 0 :=
  losingMask a b_861 0 1241462544626204187560960
    (by decide +kernel) (by decide +kernel)

theorem node_861 : Excluded a [5,4,8,7,6,0,1,3,2] :=
  losing_excluded a [5,4,8,7,6,0,1,3,2] (by decide) b_861 (by decide +kernel) 1 0 2 cert_861 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_861 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1241462544626204187560960 1 2; decide +kernel)

theorem node_860 : Excluded a [5,4,8,7,6,0,1,3] :=
  branch_excluded a [5,4,8,7,6,0,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,8,7,6,0,1,3,0] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,3,1] (by decide +kernel))
      node_861
      (invalid_excluded a [5,4,8,7,6,0,1,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,3,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,3,8] (by decide +kernel)))

theorem node_858 : Excluded a [5,4,8,7,6,0,1] :=
  branch_excluded a [5,4,8,7,6,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,8,7,6,0,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,1] (by decide +kernel))
      node_859
      node_860
      (invalid_excluded a [5,4,8,7,6,0,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,1,8] (by decide +kernel)))

theorem node_862 : Excluded a [5,4,8,7,6,0,2] :=
  predecessor_excluded a [5,4,8,7,6,0,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_863 : Excluded a [5,4,8,7,6,0,3] :=
  source_excluded a [5,4,8,7,6,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_857 : Excluded a [5,4,8,7,6,0] :=
  branch_excluded a [5,4,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,8,7,6,0,0] (by decide +kernel))
      node_858
      node_862
      node_863
      (invalid_excluded a [5,4,8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,0,8] (by decide +kernel)))

theorem node_864 : Excluded a [5,4,8,7,6,1] :=
  source_excluded a [5,4,8,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_865 : Excluded a [5,4,8,7,6,2] :=
  predecessor_excluded a [5,4,8,7,6,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_856 : Excluded a [5,4,8,7,6] :=
  branch_excluded a [5,4,8,7,6] (by decide)
    (fin9_cases _
      node_857
      node_864
      node_865
      (invalid_excluded a [5,4,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,8] (by decide +kernel)))

theorem node_851 : Excluded a [5,4,8,7] :=
  branch_excluded a [5,4,8,7] (by decide)
    (fin9_cases _
      node_852
      node_853
      node_854
      node_855
      (invalid_excluded a [5,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,5] (by decide +kernel))
      node_856
      (invalid_excluded a [5,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,8] (by decide +kernel)))

theorem node_841 : Excluded a [5,4,8] :=
  branch_excluded a [5,4,8] (by decide)
    (fin9_cases _
      node_842
      node_843
      node_844
      (invalid_excluded a [5,4,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,5] (by decide +kernel))
      node_845
      node_851
      (invalid_excluded a [5,4,8,8] (by decide +kernel)))

theorem node_717 : Excluded a [5,4] :=
  branch_excluded a [5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0] (by decide +kernel))
      node_718
      (invalid_excluded a [5,4,2] (by decide +kernel))
      node_719
      (invalid_excluded a [5,4,4] (by decide +kernel))
      (invalid_excluded a [5,4,5] (by decide +kernel))
      node_789
      node_814
      node_841)

theorem node_867 : Excluded a [5,6,1] :=
  source_excluded a [5,6,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_869 : Excluded a [5,6,3,0] :=
  source_excluded a [5,6,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_870 : Excluded a [5,6,3,1] :=
  predecessor_excluded a [5,6,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_872 : Excluded a [5,6,3,2,0] :=
  source_excluded a [5,6,3,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_873 : Excluded a [5,6,3,2,1] :=
  source_excluded a [5,6,3,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_875 : Excluded a [5,6,3,2,7,0] :=
  source_excluded a [5,6,3,2,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_876 : Excluded a [5,6,3,2,7,1] :=
  source_excluded a [5,6,3,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_877 : Excluded a [5,6,3,2,7,4] :=
  source_excluded a [5,6,3,2,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_878 : Excluded a [5,6,3,2,7,8] :=
  predecessor_excluded a [5,6,3,2,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_874 : Excluded a [5,6,3,2,7] :=
  branch_excluded a [5,6,3,2,7] (by decide)
    (fin9_cases _
      node_875
      node_876
      (invalid_excluded a [5,6,3,2,7,2] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,7,3] (by decide +kernel))
      node_877
      (invalid_excluded a [5,6,3,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,7,7] (by decide +kernel))
      node_878)

theorem node_880 : Excluded a [5,6,3,2,8,0] :=
  source_excluded a [5,6,3,2,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_881 : Excluded a [5,6,3,2,8,1] :=
  source_excluded a [5,6,3,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_882 : Excluded a [5,6,3,2,8,4] :=
  source_excluded a [5,6,3,2,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_884 : Excluded a [5,6,3,2,8,7,0] :=
  predecessor_excluded a [5,6,3,2,8,7,0] 3 0 1 6 (by decide) (by decide +kernel)

def b_887 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 6
  | 2 => 3
  | 3 => 2
  | 4 => 8
  | 5 => 7
  | 6 => 1
  | 7 => 0
  | 8 => 4
  | _ => 0

def cert_887 : LosingRegion (edgeOf a b_887) 0 :=
  losingMask a b_887 0 1521783755427245280199680
    (by decide +kernel) (by decide +kernel)

theorem node_887 : Excluded a [5,6,3,2,8,7,1,0,4] :=
  losing_excluded a [5,6,3,2,8,7,1,0,4] (by decide) b_887 (by decide +kernel) 3 0 1 cert_887 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_887 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1521783755427245280199680 3 1; decide +kernel)

theorem node_886 : Excluded a [5,6,3,2,8,7,1,0] :=
  branch_excluded a [5,6,3,2,8,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,6,3,2,8,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,0,1] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,0,2] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,0,3] (by decide +kernel))
      node_887
      (invalid_excluded a [5,6,3,2,8,7,1,0,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,0,8] (by decide +kernel)))

theorem node_888 : Excluded a [5,6,3,2,8,7,1,4] :=
  source_excluded a [5,6,3,2,8,7,1,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_885 : Excluded a [5,6,3,2,8,7,1] :=
  branch_excluded a [5,6,3,2,8,7,1] (by decide)
    (fin9_cases _
      node_886
      (invalid_excluded a [5,6,3,2,8,7,1,1] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,2] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,3] (by decide +kernel))
      node_888
      (invalid_excluded a [5,6,3,2,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,1,8] (by decide +kernel)))

theorem node_889 : Excluded a [5,6,3,2,8,7,4] :=
  predecessor_excluded a [5,6,3,2,8,7,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_883 : Excluded a [5,6,3,2,8,7] :=
  branch_excluded a [5,6,3,2,8,7] (by decide)
    (fin9_cases _
      node_884
      node_885
      (invalid_excluded a [5,6,3,2,8,7,2] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,3] (by decide +kernel))
      node_889
      (invalid_excluded a [5,6,3,2,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,7,8] (by decide +kernel)))

theorem node_879 : Excluded a [5,6,3,2,8] :=
  branch_excluded a [5,6,3,2,8] (by decide)
    (fin9_cases _
      node_880
      node_881
      (invalid_excluded a [5,6,3,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,3] (by decide +kernel))
      node_882
      (invalid_excluded a [5,6,3,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,8,6] (by decide +kernel))
      node_883
      (invalid_excluded a [5,6,3,2,8,8] (by decide +kernel)))

theorem node_871 : Excluded a [5,6,3,2] :=
  branch_excluded a [5,6,3,2] (by decide)
    (fin9_cases _
      node_872
      node_873
      (invalid_excluded a [5,6,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,3] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,4] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,2,6] (by decide +kernel))
      node_874
      node_879)

theorem node_891 : Excluded a [5,6,3,7,0] :=
  source_excluded a [5,6,3,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_892 : Excluded a [5,6,3,7,1] :=
  source_excluded a [5,6,3,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_893 : Excluded a [5,6,3,7,2] :=
  predecessor_excluded a [5,6,3,7,2] 0 3 4 2 (by decide) (by decide +kernel)

theorem node_894 : Excluded a [5,6,3,7,8] :=
  predecessor_excluded a [5,6,3,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_890 : Excluded a [5,6,3,7] :=
  branch_excluded a [5,6,3,7] (by decide)
    (fin9_cases _
      node_891
      node_892
      node_893
      (invalid_excluded a [5,6,3,7,3] (by decide +kernel))
      (invalid_excluded a [5,6,3,7,4] (by decide +kernel))
      (invalid_excluded a [5,6,3,7,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,7,6] (by decide +kernel))
      (invalid_excluded a [5,6,3,7,7] (by decide +kernel))
      node_894)

theorem node_896 : Excluded a [5,6,3,8,0] :=
  source_excluded a [5,6,3,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_897 : Excluded a [5,6,3,8,1] :=
  source_excluded a [5,6,3,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_898 : Excluded a [5,6,3,8,2] :=
  predecessor_excluded a [5,6,3,8,2] 0 3 4 2 (by decide) (by decide +kernel)

theorem node_900 : Excluded a [5,6,3,8,7,0] :=
  source_excluded a [5,6,3,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_901 : Excluded a [5,6,3,8,7,1] :=
  source_excluded a [5,6,3,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_902 : Excluded a [5,6,3,8,7,2] :=
  source_excluded a [5,6,3,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_903 : Excluded a [5,6,3,8,7,4] :=
  source_excluded a [5,6,3,8,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_899 : Excluded a [5,6,3,8,7] :=
  branch_excluded a [5,6,3,8,7] (by decide)
    (fin9_cases _
      node_900
      node_901
      node_902
      (invalid_excluded a [5,6,3,8,7,3] (by decide +kernel))
      node_903
      (invalid_excluded a [5,6,3,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,6,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,6,3,8,7,8] (by decide +kernel)))

theorem node_895 : Excluded a [5,6,3,8] :=
  branch_excluded a [5,6,3,8] (by decide)
    (fin9_cases _
      node_896
      node_897
      node_898
      (invalid_excluded a [5,6,3,8,3] (by decide +kernel))
      (invalid_excluded a [5,6,3,8,4] (by decide +kernel))
      (invalid_excluded a [5,6,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,8,6] (by decide +kernel))
      node_899
      (invalid_excluded a [5,6,3,8,8] (by decide +kernel)))

theorem node_868 : Excluded a [5,6,3] :=
  branch_excluded a [5,6,3] (by decide)
    (fin9_cases _
      node_869
      node_870
      node_871
      (invalid_excluded a [5,6,3,3] (by decide +kernel))
      (invalid_excluded a [5,6,3,4] (by decide +kernel))
      (invalid_excluded a [5,6,3,5] (by decide +kernel))
      (invalid_excluded a [5,6,3,6] (by decide +kernel))
      node_890
      node_895)

theorem node_904 : Excluded a [5,6,4] :=
  predecessor_excluded a [5,6,4] 1 5 2 0 (by decide) (by decide +kernel)

theorem node_905 : Excluded a [5,6,7] :=
  predecessor_excluded a [5,6,7] 0 7 1 2 (by decide) (by decide +kernel)

theorem node_907 : Excluded a [5,6,8,0] :=
  predecessor_excluded a [5,6,8,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_909 : Excluded a [5,6,8,1,0] :=
  source_excluded a [5,6,8,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_910 : Excluded a [5,6,8,1,2] :=
  predecessor_excluded a [5,6,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_911 : Excluded a [5,6,8,1,3] :=
  source_excluded a [5,6,8,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_913 : Excluded a [5,6,8,1,7,0] :=
  predecessor_excluded a [5,6,8,1,7,0] 2 1 5 3 (by decide) (by decide +kernel)

theorem node_914 : Excluded a [5,6,8,1,7,2] :=
  predecessor_excluded a [5,6,8,1,7,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_915 : Excluded a [5,6,8,1,7,4] :=
  source_excluded a [5,6,8,1,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_912 : Excluded a [5,6,8,1,7] :=
  branch_excluded a [5,6,8,1,7] (by decide)
    (fin9_cases _
      node_913
      (invalid_excluded a [5,6,8,1,7,1] (by decide +kernel))
      node_914
      (invalid_excluded a [5,6,8,1,7,3] (by decide +kernel))
      node_915
      (invalid_excluded a [5,6,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,6,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [5,6,8,1,7,8] (by decide +kernel)))

theorem node_908 : Excluded a [5,6,8,1] :=
  branch_excluded a [5,6,8,1] (by decide)
    (fin9_cases _
      node_909
      (invalid_excluded a [5,6,8,1,1] (by decide +kernel))
      node_910
      node_911
      (invalid_excluded a [5,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,1,6] (by decide +kernel))
      node_912
      (invalid_excluded a [5,6,8,1,8] (by decide +kernel)))

theorem node_917 : Excluded a [5,6,8,2,0] :=
  source_excluded a [5,6,8,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_918 : Excluded a [5,6,8,2,1] :=
  source_excluded a [5,6,8,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_919 : Excluded a [5,6,8,2,3] :=
  source_excluded a [5,6,8,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_923 : Excluded a [5,6,8,2,7,0,1,3] :=
  predecessor_excluded a [5,6,8,2,7,0,1,3] 0 3 4 7 (by decide) (by decide +kernel)

def b_925 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 6
  | 2 => 8
  | 3 => 2
  | 4 => 7
  | 5 => 0
  | 6 => 1
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_925 : LosingRegion (edgeOf a b_925) 0 :=
  losingMask a b_925 0 1427904507555120159923200
    (by decide +kernel) (by decide +kernel)

theorem node_925 : Excluded a [5,6,8,2,7,0,1,4,3] :=
  losing_excluded a [5,6,8,2,7,0,1,4,3] (by decide) b_925 (by decide +kernel) 1 0 2 cert_925 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_925 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1427904507555120159923200 1 2; decide +kernel)

theorem node_924 : Excluded a [5,6,8,2,7,0,1,4] :=
  branch_excluded a [5,6,8,2,7,0,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,6,8,2,7,0,1,4,0] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,4,1] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,4,2] (by decide +kernel))
      node_925
      (invalid_excluded a [5,6,8,2,7,0,1,4,4] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,4,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,4,6] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,4,7] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,4,8] (by decide +kernel)))

theorem node_922 : Excluded a [5,6,8,2,7,0,1] :=
  branch_excluded a [5,6,8,2,7,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,6,8,2,7,0,1,0] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,1] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,2] (by decide +kernel))
      node_923
      node_924
      (invalid_excluded a [5,6,8,2,7,0,1,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,6] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,7] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,1,8] (by decide +kernel)))

theorem node_927 : Excluded a [5,6,8,2,7,0,3,1] :=
  predecessor_excluded a [5,6,8,2,7,0,3,1] 0 6 7 1 (by decide) (by decide +kernel)

theorem node_928 : Excluded a [5,6,8,2,7,0,3,4] :=
  predecessor_excluded a [5,6,8,2,7,0,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_926 : Excluded a [5,6,8,2,7,0,3] :=
  branch_excluded a [5,6,8,2,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,6,8,2,7,0,3,0] (by decide +kernel))
      node_927
      (invalid_excluded a [5,6,8,2,7,0,3,2] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,3,3] (by decide +kernel))
      node_928
      (invalid_excluded a [5,6,8,2,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,3,8] (by decide +kernel)))

theorem node_929 : Excluded a [5,6,8,2,7,0,4] :=
  source_excluded a [5,6,8,2,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_921 : Excluded a [5,6,8,2,7,0] :=
  branch_excluded a [5,6,8,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,6,8,2,7,0,0] (by decide +kernel))
      node_922
      (invalid_excluded a [5,6,8,2,7,0,2] (by decide +kernel))
      node_926
      node_929
      (invalid_excluded a [5,6,8,2,7,0,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,0,8] (by decide +kernel)))

theorem node_930 : Excluded a [5,6,8,2,7,1] :=
  source_excluded a [5,6,8,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_931 : Excluded a [5,6,8,2,7,4] :=
  source_excluded a [5,6,8,2,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_920 : Excluded a [5,6,8,2,7] :=
  branch_excluded a [5,6,8,2,7] (by decide)
    (fin9_cases _
      node_921
      node_930
      (invalid_excluded a [5,6,8,2,7,2] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,3] (by decide +kernel))
      node_931
      (invalid_excluded a [5,6,8,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,7] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,7,8] (by decide +kernel)))

theorem node_916 : Excluded a [5,6,8,2] :=
  branch_excluded a [5,6,8,2] (by decide)
    (fin9_cases _
      node_917
      node_918
      (invalid_excluded a [5,6,8,2,2] (by decide +kernel))
      node_919
      (invalid_excluded a [5,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,2,6] (by decide +kernel))
      node_920
      (invalid_excluded a [5,6,8,2,8] (by decide +kernel)))

theorem node_933 : Excluded a [5,6,8,7,0] :=
  source_excluded a [5,6,8,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_934 : Excluded a [5,6,8,7,1] :=
  source_excluded a [5,6,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_936 : Excluded a [5,6,8,7,2,0] :=
  predecessor_excluded a [5,6,8,7,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_937 : Excluded a [5,6,8,7,2,1] :=
  source_excluded a [5,6,8,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_938 : Excluded a [5,6,8,7,2,4] :=
  source_excluded a [5,6,8,7,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_935 : Excluded a [5,6,8,7,2] :=
  branch_excluded a [5,6,8,7,2] (by decide)
    (fin9_cases _
      node_936
      node_937
      (invalid_excluded a [5,6,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [5,6,8,7,2,3] (by decide +kernel))
      node_938
      (invalid_excluded a [5,6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [5,6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,6,8,7,2,8] (by decide +kernel)))

theorem node_939 : Excluded a [5,6,8,7,3] :=
  source_excluded a [5,6,8,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_932 : Excluded a [5,6,8,7] :=
  branch_excluded a [5,6,8,7] (by decide)
    (fin9_cases _
      node_933
      node_934
      node_935
      node_939
      (invalid_excluded a [5,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,6,8,7,8] (by decide +kernel)))

theorem node_906 : Excluded a [5,6,8] :=
  branch_excluded a [5,6,8] (by decide)
    (fin9_cases _
      node_907
      node_908
      node_916
      (invalid_excluded a [5,6,8,3] (by decide +kernel))
      (invalid_excluded a [5,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,6,8,6] (by decide +kernel))
      node_932
      (invalid_excluded a [5,6,8,8] (by decide +kernel)))

theorem node_866 : Excluded a [5,6] :=
  branch_excluded a [5,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,6,0] (by decide +kernel))
      node_867
      (invalid_excluded a [5,6,2] (by decide +kernel))
      node_868
      node_904
      (invalid_excluded a [5,6,5] (by decide +kernel))
      (invalid_excluded a [5,6,6] (by decide +kernel))
      node_905
      node_906)

theorem node_941 : Excluded a [5,7,1] :=
  source_excluded a [5,7,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_943 : Excluded a [5,7,3,0] :=
  source_excluded a [5,7,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_944 : Excluded a [5,7,3,1] :=
  predecessor_excluded a [5,7,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_946 : Excluded a [5,7,3,2,0] :=
  source_excluded a [5,7,3,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_947 : Excluded a [5,7,3,2,1] :=
  source_excluded a [5,7,3,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_949 : Excluded a [5,7,3,2,6,0] :=
  source_excluded a [5,7,3,2,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_950 : Excluded a [5,7,3,2,6,1] :=
  source_excluded a [5,7,3,2,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_951 : Excluded a [5,7,3,2,6,4] :=
  source_excluded a [5,7,3,2,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_954 : Excluded a [5,7,3,2,6,8,0,1] :=
  predecessor_excluded a [5,7,3,2,6,8,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_955 : Excluded a [5,7,3,2,6,8,0,4] :=
  predecessor_excluded a [5,7,3,2,6,8,0,4] 0 6 7 4 (by decide) (by decide +kernel)

theorem node_953 : Excluded a [5,7,3,2,6,8,0] :=
  branch_excluded a [5,7,3,2,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,3,2,6,8,0,0] (by decide +kernel))
      node_954
      (invalid_excluded a [5,7,3,2,6,8,0,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,0,3] (by decide +kernel))
      node_955
      (invalid_excluded a [5,7,3,2,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,0,8] (by decide +kernel)))

theorem node_956 : Excluded a [5,7,3,2,6,8,1] :=
  source_excluded a [5,7,3,2,6,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_958 : Excluded a [5,7,3,2,6,8,4,0] :=
  predecessor_excluded a [5,7,3,2,6,8,4,0] 3 0 1 7 (by decide) (by decide +kernel)

def b_960 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 7
  | 2 => 3
  | 3 => 2
  | 4 => 6
  | 5 => 8
  | 6 => 4
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_960 : LosingRegion (edgeOf a b_960) 0 :=
  losingMask a b_960 0 1210109911672658649416704
    (by decide +kernel) (by decide +kernel)

theorem node_960 : Excluded a [5,7,3,2,6,8,4,1,0] :=
  losing_excluded a [5,7,3,2,6,8,4,1,0] (by decide) b_960 (by decide +kernel) 3 0 1 cert_960 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_960 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1210109911672658649416704 3 1; decide +kernel)

theorem node_959 : Excluded a [5,7,3,2,6,8,4,1] :=
  branch_excluded a [5,7,3,2,6,8,4,1] (by decide)
    (fin9_cases _
      node_960
      (invalid_excluded a [5,7,3,2,6,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,1,8] (by decide +kernel)))

theorem node_957 : Excluded a [5,7,3,2,6,8,4] :=
  branch_excluded a [5,7,3,2,6,8,4] (by decide)
    (fin9_cases _
      node_958
      node_959
      (invalid_excluded a [5,7,3,2,6,8,4,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,4,8] (by decide +kernel)))

theorem node_952 : Excluded a [5,7,3,2,6,8] :=
  branch_excluded a [5,7,3,2,6,8] (by decide)
    (fin9_cases _
      node_953
      node_956
      (invalid_excluded a [5,7,3,2,6,8,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,3] (by decide +kernel))
      node_957
      (invalid_excluded a [5,7,3,2,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,8,8] (by decide +kernel)))

theorem node_948 : Excluded a [5,7,3,2,6] :=
  branch_excluded a [5,7,3,2,6] (by decide)
    (fin9_cases _
      node_949
      node_950
      (invalid_excluded a [5,7,3,2,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,3] (by decide +kernel))
      node_951
      (invalid_excluded a [5,7,3,2,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,6,7] (by decide +kernel))
      node_952)

theorem node_962 : Excluded a [5,7,3,2,8,0] :=
  source_excluded a [5,7,3,2,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_963 : Excluded a [5,7,3,2,8,1] :=
  source_excluded a [5,7,3,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_964 : Excluded a [5,7,3,2,8,4] :=
  source_excluded a [5,7,3,2,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_965 : Excluded a [5,7,3,2,8,6] :=
  predecessor_excluded a [5,7,3,2,8,6] 0 6 4 5 (by decide) (by decide +kernel)

theorem node_961 : Excluded a [5,7,3,2,8] :=
  branch_excluded a [5,7,3,2,8] (by decide)
    (fin9_cases _
      node_962
      node_963
      (invalid_excluded a [5,7,3,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,3] (by decide +kernel))
      node_964
      (invalid_excluded a [5,7,3,2,8,5] (by decide +kernel))
      node_965
      (invalid_excluded a [5,7,3,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,8] (by decide +kernel)))

theorem node_945 : Excluded a [5,7,3,2] :=
  branch_excluded a [5,7,3,2] (by decide)
    (fin9_cases _
      node_946
      node_947
      (invalid_excluded a [5,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,5] (by decide +kernel))
      node_948
      (invalid_excluded a [5,7,3,2,7] (by decide +kernel))
      node_961)

theorem node_967 : Excluded a [5,7,3,6,0] :=
  source_excluded a [5,7,3,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_968 : Excluded a [5,7,3,6,1] :=
  source_excluded a [5,7,3,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_969 : Excluded a [5,7,3,6,2] :=
  predecessor_excluded a [5,7,3,6,2] 0 3 4 2 (by decide) (by decide +kernel)

theorem node_971 : Excluded a [5,7,3,6,8,0] :=
  source_excluded a [5,7,3,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_972 : Excluded a [5,7,3,6,8,1] :=
  source_excluded a [5,7,3,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_973 : Excluded a [5,7,3,6,8,2] :=
  source_excluded a [5,7,3,6,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_974 : Excluded a [5,7,3,6,8,4] :=
  source_excluded a [5,7,3,6,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_970 : Excluded a [5,7,3,6,8] :=
  branch_excluded a [5,7,3,6,8] (by decide)
    (fin9_cases _
      node_971
      node_972
      node_973
      (invalid_excluded a [5,7,3,6,8,3] (by decide +kernel))
      node_974
      (invalid_excluded a [5,7,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,8,8] (by decide +kernel)))

theorem node_966 : Excluded a [5,7,3,6] :=
  branch_excluded a [5,7,3,6] (by decide)
    (fin9_cases _
      node_967
      node_968
      node_969
      (invalid_excluded a [5,7,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,7] (by decide +kernel))
      node_970)

theorem node_976 : Excluded a [5,7,3,8,0] :=
  source_excluded a [5,7,3,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_977 : Excluded a [5,7,3,8,1] :=
  source_excluded a [5,7,3,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_978 : Excluded a [5,7,3,8,2] :=
  predecessor_excluded a [5,7,3,8,2] 0 3 4 2 (by decide) (by decide +kernel)

theorem node_979 : Excluded a [5,7,3,8,6] :=
  predecessor_excluded a [5,7,3,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_975 : Excluded a [5,7,3,8] :=
  branch_excluded a [5,7,3,8] (by decide)
    (fin9_cases _
      node_976
      node_977
      node_978
      (invalid_excluded a [5,7,3,8,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,5] (by decide +kernel))
      node_979
      (invalid_excluded a [5,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,8] (by decide +kernel)))

theorem node_942 : Excluded a [5,7,3] :=
  branch_excluded a [5,7,3] (by decide)
    (fin9_cases _
      node_943
      node_944
      node_945
      (invalid_excluded a [5,7,3,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,5] (by decide +kernel))
      node_966
      (invalid_excluded a [5,7,3,7] (by decide +kernel))
      node_975)

theorem node_980 : Excluded a [5,7,4] :=
  predecessor_excluded a [5,7,4] 1 5 2 0 (by decide) (by decide +kernel)

theorem node_982 : Excluded a [5,7,6,0] :=
  predecessor_excluded a [5,7,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_984 : Excluded a [5,7,6,1,0] :=
  source_excluded a [5,7,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_985 : Excluded a [5,7,6,1,2] :=
  predecessor_excluded a [5,7,6,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_986 : Excluded a [5,7,6,1,3] :=
  source_excluded a [5,7,6,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_988 : Excluded a [5,7,6,1,8,0] :=
  predecessor_excluded a [5,7,6,1,8,0] 2 1 5 3 (by decide) (by decide +kernel)

theorem node_989 : Excluded a [5,7,6,1,8,2] :=
  predecessor_excluded a [5,7,6,1,8,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_990 : Excluded a [5,7,6,1,8,4] :=
  source_excluded a [5,7,6,1,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_987 : Excluded a [5,7,6,1,8] :=
  branch_excluded a [5,7,6,1,8] (by decide)
    (fin9_cases _
      node_988
      (invalid_excluded a [5,7,6,1,8,1] (by decide +kernel))
      node_989
      (invalid_excluded a [5,7,6,1,8,3] (by decide +kernel))
      node_990
      (invalid_excluded a [5,7,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,8] (by decide +kernel)))

theorem node_983 : Excluded a [5,7,6,1] :=
  branch_excluded a [5,7,6,1] (by decide)
    (fin9_cases _
      node_984
      (invalid_excluded a [5,7,6,1,1] (by decide +kernel))
      node_985
      node_986
      (invalid_excluded a [5,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,7] (by decide +kernel))
      node_987)

theorem node_992 : Excluded a [5,7,6,2,0] :=
  source_excluded a [5,7,6,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_993 : Excluded a [5,7,6,2,1] :=
  source_excluded a [5,7,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_994 : Excluded a [5,7,6,2,3] :=
  source_excluded a [5,7,6,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_997 : Excluded a [5,7,6,2,8,0,1] :=
  source_excluded a [5,7,6,2,8,0,1] 6 0 1 (by decide) (by decide +kernel)

def b_1000 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 7
  | 2 => 6
  | 3 => 2
  | 4 => 8
  | 5 => 0
  | 6 => 3
  | 7 => 1
  | 8 => 4
  | _ => 0

def cert_1000 : LosingRegion (edgeOf a b_1000) 0 :=
  losingMask a b_1000 0 1499196543699590640049152
    (by decide +kernel) (by decide +kernel)

theorem node_1000 : Excluded a [5,7,6,2,8,0,3,1,4] :=
  losing_excluded a [5,7,6,2,8,0,3,1,4] (by decide) b_1000 (by decide +kernel) 1 0 2 cert_1000 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1000 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1499196543699590640049152 1 2; decide +kernel)

theorem node_999 : Excluded a [5,7,6,2,8,0,3,1] :=
  branch_excluded a [5,7,6,2,8,0,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,2,8,0,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,1,1] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,1,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,1,3] (by decide +kernel))
      node_1000
      (invalid_excluded a [5,7,6,2,8,0,3,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,1,8] (by decide +kernel)))

theorem node_1001 : Excluded a [5,7,6,2,8,0,3,4] :=
  source_excluded a [5,7,6,2,8,0,3,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_998 : Excluded a [5,7,6,2,8,0,3] :=
  branch_excluded a [5,7,6,2,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,2,8,0,3,0] (by decide +kernel))
      node_999
      (invalid_excluded a [5,7,6,2,8,0,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,3] (by decide +kernel))
      node_1001
      (invalid_excluded a [5,7,6,2,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,3,8] (by decide +kernel)))

theorem node_1002 : Excluded a [5,7,6,2,8,0,4] :=
  predecessor_excluded a [5,7,6,2,8,0,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_996 : Excluded a [5,7,6,2,8,0] :=
  branch_excluded a [5,7,6,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,2,8,0,0] (by decide +kernel))
      node_997
      (invalid_excluded a [5,7,6,2,8,0,2] (by decide +kernel))
      node_998
      node_1002
      (invalid_excluded a [5,7,6,2,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,0,8] (by decide +kernel)))

theorem node_1003 : Excluded a [5,7,6,2,8,1] :=
  source_excluded a [5,7,6,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1004 : Excluded a [5,7,6,2,8,4] :=
  source_excluded a [5,7,6,2,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_995 : Excluded a [5,7,6,2,8] :=
  branch_excluded a [5,7,6,2,8] (by decide)
    (fin9_cases _
      node_996
      node_1003
      (invalid_excluded a [5,7,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,3] (by decide +kernel))
      node_1004
      (invalid_excluded a [5,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,8] (by decide +kernel)))

theorem node_991 : Excluded a [5,7,6,2] :=
  branch_excluded a [5,7,6,2] (by decide)
    (fin9_cases _
      node_992
      node_993
      (invalid_excluded a [5,7,6,2,2] (by decide +kernel))
      node_994
      (invalid_excluded a [5,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,7] (by decide +kernel))
      node_995)

theorem node_1006 : Excluded a [5,7,6,8,0] :=
  source_excluded a [5,7,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1007 : Excluded a [5,7,6,8,1] :=
  source_excluded a [5,7,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1009 : Excluded a [5,7,6,8,2,0] :=
  predecessor_excluded a [5,7,6,8,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1010 : Excluded a [5,7,6,8,2,1] :=
  source_excluded a [5,7,6,8,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1011 : Excluded a [5,7,6,8,2,4] :=
  source_excluded a [5,7,6,8,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1008 : Excluded a [5,7,6,8,2] :=
  branch_excluded a [5,7,6,8,2] (by decide)
    (fin9_cases _
      node_1009
      node_1010
      (invalid_excluded a [5,7,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,2,3] (by decide +kernel))
      node_1011
      (invalid_excluded a [5,7,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,2,8] (by decide +kernel)))

theorem node_1012 : Excluded a [5,7,6,8,3] :=
  source_excluded a [5,7,6,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1005 : Excluded a [5,7,6,8] :=
  branch_excluded a [5,7,6,8] (by decide)
    (fin9_cases _
      node_1006
      node_1007
      node_1008
      node_1012
      (invalid_excluded a [5,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,8] (by decide +kernel)))

theorem node_981 : Excluded a [5,7,6] :=
  branch_excluded a [5,7,6] (by decide)
    (fin9_cases _
      node_982
      node_983
      node_991
      (invalid_excluded a [5,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,7] (by decide +kernel))
      node_1005)

theorem node_1013 : Excluded a [5,7,8] :=
  predecessor_excluded a [5,7,8] 0 8 1 2 (by decide) (by decide +kernel)

theorem node_940 : Excluded a [5,7] :=
  branch_excluded a [5,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0] (by decide +kernel))
      node_941
      (invalid_excluded a [5,7,2] (by decide +kernel))
      node_942
      node_980
      (invalid_excluded a [5,7,5] (by decide +kernel))
      node_981
      (invalid_excluded a [5,7,7] (by decide +kernel))
      node_1013)

theorem node_1015 : Excluded a [5,8,1] :=
  source_excluded a [5,8,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1017 : Excluded a [5,8,3,0] :=
  source_excluded a [5,8,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1018 : Excluded a [5,8,3,1] :=
  predecessor_excluded a [5,8,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_1020 : Excluded a [5,8,3,2,0] :=
  source_excluded a [5,8,3,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1021 : Excluded a [5,8,3,2,1] :=
  source_excluded a [5,8,3,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1023 : Excluded a [5,8,3,2,6,0] :=
  source_excluded a [5,8,3,2,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1024 : Excluded a [5,8,3,2,6,1] :=
  source_excluded a [5,8,3,2,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1025 : Excluded a [5,8,3,2,6,4] :=
  source_excluded a [5,8,3,2,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1026 : Excluded a [5,8,3,2,6,7] :=
  predecessor_excluded a [5,8,3,2,6,7] 0 7 4 5 (by decide) (by decide +kernel)

theorem node_1022 : Excluded a [5,8,3,2,6] :=
  branch_excluded a [5,8,3,2,6] (by decide)
    (fin9_cases _
      node_1023
      node_1024
      (invalid_excluded a [5,8,3,2,6,2] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,6,3] (by decide +kernel))
      node_1025
      (invalid_excluded a [5,8,3,2,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,6,6] (by decide +kernel))
      node_1026
      (invalid_excluded a [5,8,3,2,6,8] (by decide +kernel)))

theorem node_1028 : Excluded a [5,8,3,2,7,0] :=
  source_excluded a [5,8,3,2,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1029 : Excluded a [5,8,3,2,7,1] :=
  source_excluded a [5,8,3,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1030 : Excluded a [5,8,3,2,7,4] :=
  source_excluded a [5,8,3,2,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1033 : Excluded a [5,8,3,2,7,6,0,1] :=
  source_excluded a [5,8,3,2,7,6,0,1] 7 0 1 (by decide) (by decide +kernel)

def b_1035 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 8
  | 2 => 3
  | 3 => 2
  | 4 => 7
  | 5 => 6
  | 6 => 0
  | 7 => 4
  | 8 => 1
  | _ => 0

def cert_1035 : LosingRegion (edgeOf a b_1035) 0 :=
  losingMask a b_1035 0 1212487204303154715821056
    (by decide +kernel) (by decide +kernel)

theorem node_1035 : Excluded a [5,8,3,2,7,6,0,4,1] :=
  losing_excluded a [5,8,3,2,7,6,0,4,1] (by decide) b_1035 (by decide +kernel) 3 0 1 cert_1035 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1035 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1212487204303154715821056 3 1; decide +kernel)

theorem node_1034 : Excluded a [5,8,3,2,7,6,0,4] :=
  branch_excluded a [5,8,3,2,7,6,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,3,2,7,6,0,4,0] (by decide +kernel))
      node_1035
      (invalid_excluded a [5,8,3,2,7,6,0,4,2] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,4,5] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,4,6] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,4,8] (by decide +kernel)))

theorem node_1032 : Excluded a [5,8,3,2,7,6,0] :=
  branch_excluded a [5,8,3,2,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,3,2,7,6,0,0] (by decide +kernel))
      node_1033
      (invalid_excluded a [5,8,3,2,7,6,0,2] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,3] (by decide +kernel))
      node_1034
      (invalid_excluded a [5,8,3,2,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,0,8] (by decide +kernel)))

theorem node_1036 : Excluded a [5,8,3,2,7,6,1] :=
  predecessor_excluded a [5,8,3,2,7,6,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1037 : Excluded a [5,8,3,2,7,6,4] :=
  source_excluded a [5,8,3,2,7,6,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1031 : Excluded a [5,8,3,2,7,6] :=
  branch_excluded a [5,8,3,2,7,6] (by decide)
    (fin9_cases _
      node_1032
      node_1036
      (invalid_excluded a [5,8,3,2,7,6,2] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,3] (by decide +kernel))
      node_1037
      (invalid_excluded a [5,8,3,2,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,6,8] (by decide +kernel)))

theorem node_1027 : Excluded a [5,8,3,2,7] :=
  branch_excluded a [5,8,3,2,7] (by decide)
    (fin9_cases _
      node_1028
      node_1029
      (invalid_excluded a [5,8,3,2,7,2] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,3] (by decide +kernel))
      node_1030
      (invalid_excluded a [5,8,3,2,7,5] (by decide +kernel))
      node_1031
      (invalid_excluded a [5,8,3,2,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,7,8] (by decide +kernel)))

theorem node_1019 : Excluded a [5,8,3,2] :=
  branch_excluded a [5,8,3,2] (by decide)
    (fin9_cases _
      node_1020
      node_1021
      (invalid_excluded a [5,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,3,2,5] (by decide +kernel))
      node_1022
      node_1027
      (invalid_excluded a [5,8,3,2,8] (by decide +kernel)))

theorem node_1039 : Excluded a [5,8,3,6,0] :=
  source_excluded a [5,8,3,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1040 : Excluded a [5,8,3,6,1] :=
  source_excluded a [5,8,3,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1041 : Excluded a [5,8,3,6,2] :=
  predecessor_excluded a [5,8,3,6,2] 0 3 4 2 (by decide) (by decide +kernel)

theorem node_1042 : Excluded a [5,8,3,6,7] :=
  predecessor_excluded a [5,8,3,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1038 : Excluded a [5,8,3,6] :=
  branch_excluded a [5,8,3,6] (by decide)
    (fin9_cases _
      node_1039
      node_1040
      node_1041
      (invalid_excluded a [5,8,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,8,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,3,6,6] (by decide +kernel))
      node_1042
      (invalid_excluded a [5,8,3,6,8] (by decide +kernel)))

theorem node_1044 : Excluded a [5,8,3,7,0] :=
  source_excluded a [5,8,3,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1045 : Excluded a [5,8,3,7,1] :=
  source_excluded a [5,8,3,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1046 : Excluded a [5,8,3,7,2] :=
  predecessor_excluded a [5,8,3,7,2] 0 3 4 2 (by decide) (by decide +kernel)

theorem node_1048 : Excluded a [5,8,3,7,6,0] :=
  source_excluded a [5,8,3,7,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1049 : Excluded a [5,8,3,7,6,1] :=
  source_excluded a [5,8,3,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1050 : Excluded a [5,8,3,7,6,2] :=
  source_excluded a [5,8,3,7,6,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1051 : Excluded a [5,8,3,7,6,4] :=
  source_excluded a [5,8,3,7,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1047 : Excluded a [5,8,3,7,6] :=
  branch_excluded a [5,8,3,7,6] (by decide)
    (fin9_cases _
      node_1048
      node_1049
      node_1050
      (invalid_excluded a [5,8,3,7,6,3] (by decide +kernel))
      node_1051
      (invalid_excluded a [5,8,3,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,3,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,3,7,6,8] (by decide +kernel)))

theorem node_1043 : Excluded a [5,8,3,7] :=
  branch_excluded a [5,8,3,7] (by decide)
    (fin9_cases _
      node_1044
      node_1045
      node_1046
      (invalid_excluded a [5,8,3,7,3] (by decide +kernel))
      (invalid_excluded a [5,8,3,7,4] (by decide +kernel))
      (invalid_excluded a [5,8,3,7,5] (by decide +kernel))
      node_1047
      (invalid_excluded a [5,8,3,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,3,7,8] (by decide +kernel)))

theorem node_1016 : Excluded a [5,8,3] :=
  branch_excluded a [5,8,3] (by decide)
    (fin9_cases _
      node_1017
      node_1018
      node_1019
      (invalid_excluded a [5,8,3,3] (by decide +kernel))
      (invalid_excluded a [5,8,3,4] (by decide +kernel))
      (invalid_excluded a [5,8,3,5] (by decide +kernel))
      node_1038
      node_1043
      (invalid_excluded a [5,8,3,8] (by decide +kernel)))

theorem node_1052 : Excluded a [5,8,4] :=
  predecessor_excluded a [5,8,4] 1 5 2 0 (by decide) (by decide +kernel)

theorem node_1053 : Excluded a [5,8,6] :=
  predecessor_excluded a [5,8,6] 0 6 1 2 (by decide) (by decide +kernel)

theorem node_1055 : Excluded a [5,8,7,0] :=
  predecessor_excluded a [5,8,7,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1057 : Excluded a [5,8,7,1,0] :=
  source_excluded a [5,8,7,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1058 : Excluded a [5,8,7,1,2] :=
  predecessor_excluded a [5,8,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1059 : Excluded a [5,8,7,1,3] :=
  source_excluded a [5,8,7,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1061 : Excluded a [5,8,7,1,6,0] :=
  predecessor_excluded a [5,8,7,1,6,0] 2 1 5 3 (by decide) (by decide +kernel)

theorem node_1062 : Excluded a [5,8,7,1,6,2] :=
  predecessor_excluded a [5,8,7,1,6,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_1063 : Excluded a [5,8,7,1,6,4] :=
  source_excluded a [5,8,7,1,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1060 : Excluded a [5,8,7,1,6] :=
  branch_excluded a [5,8,7,1,6] (by decide)
    (fin9_cases _
      node_1061
      (invalid_excluded a [5,8,7,1,6,1] (by decide +kernel))
      node_1062
      (invalid_excluded a [5,8,7,1,6,3] (by decide +kernel))
      node_1063
      (invalid_excluded a [5,8,7,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,6,8] (by decide +kernel)))

theorem node_1056 : Excluded a [5,8,7,1] :=
  branch_excluded a [5,8,7,1] (by decide)
    (fin9_cases _
      node_1057
      (invalid_excluded a [5,8,7,1,1] (by decide +kernel))
      node_1058
      node_1059
      (invalid_excluded a [5,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,5] (by decide +kernel))
      node_1060
      (invalid_excluded a [5,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,8] (by decide +kernel)))

theorem node_1065 : Excluded a [5,8,7,2,0] :=
  source_excluded a [5,8,7,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1066 : Excluded a [5,8,7,2,1] :=
  source_excluded a [5,8,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1067 : Excluded a [5,8,7,2,3] :=
  source_excluded a [5,8,7,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1070 : Excluded a [5,8,7,2,6,0,1] :=
  predecessor_excluded a [5,8,7,2,6,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1071 : Excluded a [5,8,7,2,6,0,3] :=
  predecessor_excluded a [5,8,7,2,6,0,3] 0 3 4 6 (by decide) (by decide +kernel)

theorem node_1073 : Excluded a [5,8,7,2,6,0,4,1] :=
  source_excluded a [5,8,7,2,6,0,4,1] 7 0 1 (by decide) (by decide +kernel)

def b_1075 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 8
  | 2 => 7
  | 3 => 2
  | 4 => 6
  | 5 => 0
  | 6 => 4
  | 7 => 3
  | 8 => 1
  | _ => 0

def cert_1075 : LosingRegion (edgeOf a b_1075) 0 :=
  losingMask a b_1075 0 2036947073780312276212736
    (by decide +kernel) (by decide +kernel)

theorem node_1075 : Excluded a [5,8,7,2,6,0,4,3,1] :=
  losing_excluded a [5,8,7,2,6,0,4,3,1] (by decide) b_1075 (by decide +kernel) 1 0 2 cert_1075 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1075 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2036947073780312276212736 1 2; decide +kernel)

theorem node_1074 : Excluded a [5,8,7,2,6,0,4,3] :=
  branch_excluded a [5,8,7,2,6,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,2,6,0,4,3,0] (by decide +kernel))
      node_1075
      (invalid_excluded a [5,8,7,2,6,0,4,3,2] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,3,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,3,8] (by decide +kernel)))

theorem node_1072 : Excluded a [5,8,7,2,6,0,4] :=
  branch_excluded a [5,8,7,2,6,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,2,6,0,4,0] (by decide +kernel))
      node_1073
      (invalid_excluded a [5,8,7,2,6,0,4,2] (by decide +kernel))
      node_1074
      (invalid_excluded a [5,8,7,2,6,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,4,8] (by decide +kernel)))

theorem node_1069 : Excluded a [5,8,7,2,6,0] :=
  branch_excluded a [5,8,7,2,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,2,6,0,0] (by decide +kernel))
      node_1070
      (invalid_excluded a [5,8,7,2,6,0,2] (by decide +kernel))
      node_1071
      node_1072
      (invalid_excluded a [5,8,7,2,6,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,0,8] (by decide +kernel)))

theorem node_1076 : Excluded a [5,8,7,2,6,1] :=
  source_excluded a [5,8,7,2,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1077 : Excluded a [5,8,7,2,6,4] :=
  source_excluded a [5,8,7,2,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1068 : Excluded a [5,8,7,2,6] :=
  branch_excluded a [5,8,7,2,6] (by decide)
    (fin9_cases _
      node_1069
      node_1076
      (invalid_excluded a [5,8,7,2,6,2] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,3] (by decide +kernel))
      node_1077
      (invalid_excluded a [5,8,7,2,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,6,8] (by decide +kernel)))

theorem node_1064 : Excluded a [5,8,7,2] :=
  branch_excluded a [5,8,7,2] (by decide)
    (fin9_cases _
      node_1065
      node_1066
      (invalid_excluded a [5,8,7,2,2] (by decide +kernel))
      node_1067
      (invalid_excluded a [5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,5] (by decide +kernel))
      node_1068
      (invalid_excluded a [5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,8] (by decide +kernel)))

theorem node_1079 : Excluded a [5,8,7,6,0] :=
  source_excluded a [5,8,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1080 : Excluded a [5,8,7,6,1] :=
  source_excluded a [5,8,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1082 : Excluded a [5,8,7,6,2,0] :=
  predecessor_excluded a [5,8,7,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1083 : Excluded a [5,8,7,6,2,1] :=
  source_excluded a [5,8,7,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1084 : Excluded a [5,8,7,6,2,4] :=
  source_excluded a [5,8,7,6,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1081 : Excluded a [5,8,7,6,2] :=
  branch_excluded a [5,8,7,6,2] (by decide)
    (fin9_cases _
      node_1082
      node_1083
      (invalid_excluded a [5,8,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,3] (by decide +kernel))
      node_1084
      (invalid_excluded a [5,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,8] (by decide +kernel)))

theorem node_1085 : Excluded a [5,8,7,6,3] :=
  source_excluded a [5,8,7,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1078 : Excluded a [5,8,7,6] :=
  branch_excluded a [5,8,7,6] (by decide)
    (fin9_cases _
      node_1079
      node_1080
      node_1081
      node_1085
      (invalid_excluded a [5,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,8] (by decide +kernel)))

theorem node_1054 : Excluded a [5,8,7] :=
  branch_excluded a [5,8,7] (by decide)
    (fin9_cases _
      node_1055
      node_1056
      node_1064
      (invalid_excluded a [5,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,5] (by decide +kernel))
      node_1078
      (invalid_excluded a [5,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,8] (by decide +kernel)))

theorem node_1014 : Excluded a [5,8] :=
  branch_excluded a [5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0] (by decide +kernel))
      node_1015
      (invalid_excluded a [5,8,2] (by decide +kernel))
      node_1016
      node_1052
      (invalid_excluded a [5,8,5] (by decide +kernel))
      node_1053
      node_1054
      (invalid_excluded a [5,8,8] (by decide +kernel)))

theorem node_714 : Excluded a [5] :=
  branch_excluded a [5] (by decide)
    (fin9_cases _
      node_715
      (invalid_excluded a [5,1] (by decide +kernel))
      (invalid_excluded a [5,2] (by decide +kernel))
      node_716
      node_717
      (invalid_excluded a [5,5] (by decide +kernel))
      node_866
      node_940
      node_1014)

theorem node_1087 : Excluded a [6,0] :=
  source_excluded a [6,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_1089 : Excluded a [6,3,1] :=
  source_excluded a [6,3,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1090 : Excluded a [6,3,4] :=
  predecessor_excluded a [6,3,4] 0 4 1 2 (by decide) (by decide +kernel)

theorem node_1092 : Excluded a [6,3,5,0] :=
  predecessor_excluded a [6,3,5,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1094 : Excluded a [6,3,5,1,0] :=
  source_excluded a [6,3,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1095 : Excluded a [6,3,5,1,2] :=
  source_excluded a [6,3,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1097 : Excluded a [6,3,5,1,7,0] :=
  source_excluded a [6,3,5,1,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1098 : Excluded a [6,3,5,1,7,2] :=
  source_excluded a [6,3,5,1,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1099 : Excluded a [6,3,5,1,7,4] :=
  source_excluded a [6,3,5,1,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1100 : Excluded a [6,3,5,1,7,8] :=
  predecessor_excluded a [6,3,5,1,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1096 : Excluded a [6,3,5,1,7] :=
  branch_excluded a [6,3,5,1,7] (by decide)
    (fin9_cases _
      node_1097
      (invalid_excluded a [6,3,5,1,7,1] (by decide +kernel))
      node_1098
      (invalid_excluded a [6,3,5,1,7,3] (by decide +kernel))
      node_1099
      (invalid_excluded a [6,3,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,7,7] (by decide +kernel))
      node_1100)

theorem node_1102 : Excluded a [6,3,5,1,8,0] :=
  source_excluded a [6,3,5,1,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1103 : Excluded a [6,3,5,1,8,2] :=
  source_excluded a [6,3,5,1,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1104 : Excluded a [6,3,5,1,8,4] :=
  source_excluded a [6,3,5,1,8,4] 5 0 3 (by decide) (by decide +kernel)

def b_1108 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 3
  | 2 => 5
  | 3 => 1
  | 4 => 8
  | 5 => 7
  | 6 => 0
  | 7 => 2
  | 8 => 4
  | _ => 0

def cert_1108 : LosingRegion (edgeOf a b_1108) 0 :=
  losingMask a b_1108 0 1517098287156192645024768
    (by decide +kernel) (by decide +kernel)

theorem node_1108 : Excluded a [6,3,5,1,8,7,0,2,4] :=
  losing_excluded a [6,3,5,1,8,7,0,2,4] (by decide) b_1108 (by decide +kernel) 1 0 2 cert_1108 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1108 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1517098287156192645024768 1 2; decide +kernel)

theorem node_1107 : Excluded a [6,3,5,1,8,7,0,2] :=
  branch_excluded a [6,3,5,1,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,1,8,7,0,2,0] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,2,1] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,2,3] (by decide +kernel))
      node_1108
      (invalid_excluded a [6,3,5,1,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,2,8] (by decide +kernel)))

theorem node_1109 : Excluded a [6,3,5,1,8,7,0,4] :=
  source_excluded a [6,3,5,1,8,7,0,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_1106 : Excluded a [6,3,5,1,8,7,0] :=
  branch_excluded a [6,3,5,1,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,1,8,7,0,0] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,1] (by decide +kernel))
      node_1107
      (invalid_excluded a [6,3,5,1,8,7,0,3] (by decide +kernel))
      node_1109
      (invalid_excluded a [6,3,5,1,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,0,8] (by decide +kernel)))

theorem node_1110 : Excluded a [6,3,5,1,8,7,2] :=
  predecessor_excluded a [6,3,5,1,8,7,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1111 : Excluded a [6,3,5,1,8,7,4] :=
  predecessor_excluded a [6,3,5,1,8,7,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1105 : Excluded a [6,3,5,1,8,7] :=
  branch_excluded a [6,3,5,1,8,7] (by decide)
    (fin9_cases _
      node_1106
      (invalid_excluded a [6,3,5,1,8,7,1] (by decide +kernel))
      node_1110
      (invalid_excluded a [6,3,5,1,8,7,3] (by decide +kernel))
      node_1111
      (invalid_excluded a [6,3,5,1,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,7,8] (by decide +kernel)))

theorem node_1101 : Excluded a [6,3,5,1,8] :=
  branch_excluded a [6,3,5,1,8] (by decide)
    (fin9_cases _
      node_1102
      (invalid_excluded a [6,3,5,1,8,1] (by decide +kernel))
      node_1103
      (invalid_excluded a [6,3,5,1,8,3] (by decide +kernel))
      node_1104
      (invalid_excluded a [6,3,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,8,6] (by decide +kernel))
      node_1105
      (invalid_excluded a [6,3,5,1,8,8] (by decide +kernel)))

theorem node_1093 : Excluded a [6,3,5,1] :=
  branch_excluded a [6,3,5,1] (by decide)
    (fin9_cases _
      node_1094
      (invalid_excluded a [6,3,5,1,1] (by decide +kernel))
      node_1095
      (invalid_excluded a [6,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,1,6] (by decide +kernel))
      node_1096
      node_1101)

theorem node_1112 : Excluded a [6,3,5,2] :=
  source_excluded a [6,3,5,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1114 : Excluded a [6,3,5,7,0] :=
  source_excluded a [6,3,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1115 : Excluded a [6,3,5,7,1] :=
  predecessor_excluded a [6,3,5,7,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1116 : Excluded a [6,3,5,7,2] :=
  source_excluded a [6,3,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1117 : Excluded a [6,3,5,7,8] :=
  predecessor_excluded a [6,3,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1113 : Excluded a [6,3,5,7] :=
  branch_excluded a [6,3,5,7] (by decide)
    (fin9_cases _
      node_1114
      node_1115
      node_1116
      (invalid_excluded a [6,3,5,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,7] (by decide +kernel))
      node_1117)

theorem node_1119 : Excluded a [6,3,5,8,0] :=
  source_excluded a [6,3,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1120 : Excluded a [6,3,5,8,1] :=
  predecessor_excluded a [6,3,5,8,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1121 : Excluded a [6,3,5,8,2] :=
  source_excluded a [6,3,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1123 : Excluded a [6,3,5,8,7,0] :=
  source_excluded a [6,3,5,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1124 : Excluded a [6,3,5,8,7,1] :=
  source_excluded a [6,3,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1125 : Excluded a [6,3,5,8,7,2] :=
  source_excluded a [6,3,5,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1126 : Excluded a [6,3,5,8,7,4] :=
  source_excluded a [6,3,5,8,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1122 : Excluded a [6,3,5,8,7] :=
  branch_excluded a [6,3,5,8,7] (by decide)
    (fin9_cases _
      node_1123
      node_1124
      node_1125
      (invalid_excluded a [6,3,5,8,7,3] (by decide +kernel))
      node_1126
      (invalid_excluded a [6,3,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,8] (by decide +kernel)))

theorem node_1118 : Excluded a [6,3,5,8] :=
  branch_excluded a [6,3,5,8] (by decide)
    (fin9_cases _
      node_1119
      node_1120
      node_1121
      (invalid_excluded a [6,3,5,8,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,6] (by decide +kernel))
      node_1122
      (invalid_excluded a [6,3,5,8,8] (by decide +kernel)))

theorem node_1091 : Excluded a [6,3,5] :=
  branch_excluded a [6,3,5] (by decide)
    (fin9_cases _
      node_1092
      node_1093
      node_1112
      (invalid_excluded a [6,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,6] (by decide +kernel))
      node_1113
      node_1118)

theorem node_1128 : Excluded a [6,3,7,0] :=
  predecessor_excluded a [6,3,7,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1131 : Excluded a [6,3,7,1,0,2] :=
  source_excluded a [6,3,7,1,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1132 : Excluded a [6,3,7,1,0,4] :=
  source_excluded a [6,3,7,1,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1134 : Excluded a [6,3,7,1,0,8,2] :=
  source_excluded a [6,3,7,1,0,8,2] 6 0 2 (by decide) (by decide +kernel)

def b_1137 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 3
  | 2 => 7
  | 3 => 1
  | 4 => 0
  | 5 => 8
  | 6 => 4
  | 7 => 2
  | 8 => 5
  | _ => 0

def cert_1137 : LosingRegion (edgeOf a b_1137) 0 :=
  losingMask a b_1137 0 1413224808746499355706368
    (by decide +kernel) (by decide +kernel)

theorem node_1137 : Excluded a [6,3,7,1,0,8,4,2,5] :=
  losing_excluded a [6,3,7,1,0,8,4,2,5] (by decide) b_1137 (by decide +kernel) 5 0 1 cert_1137 (by change 5 ≠ 0 ∧ ¬ edgeOf a b_1137 5 0 ∧ 1 ≠ 5 ∧ maskRegion 1413224808746499355706368 5 1; decide +kernel)

theorem node_1136 : Excluded a [6,3,7,1,0,8,4,2] :=
  branch_excluded a [6,3,7,1,0,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,1,0,8,4,2,0] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,2,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,2,4] (by decide +kernel))
      node_1137
      (invalid_excluded a [6,3,7,1,0,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,2,8] (by decide +kernel)))

theorem node_1138 : Excluded a [6,3,7,1,0,8,4,5] :=
  source_excluded a [6,3,7,1,0,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_1135 : Excluded a [6,3,7,1,0,8,4] :=
  branch_excluded a [6,3,7,1,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,1,0,8,4,0] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,1] (by decide +kernel))
      node_1136
      (invalid_excluded a [6,3,7,1,0,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,4] (by decide +kernel))
      node_1138
      (invalid_excluded a [6,3,7,1,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,4,8] (by decide +kernel)))

theorem node_1139 : Excluded a [6,3,7,1,0,8,5] :=
  predecessor_excluded a [6,3,7,1,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1133 : Excluded a [6,3,7,1,0,8] :=
  branch_excluded a [6,3,7,1,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,1,0,8,0] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,1] (by decide +kernel))
      node_1134
      (invalid_excluded a [6,3,7,1,0,8,3] (by decide +kernel))
      node_1135
      node_1139
      (invalid_excluded a [6,3,7,1,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,8,8] (by decide +kernel)))

theorem node_1130 : Excluded a [6,3,7,1,0] :=
  branch_excluded a [6,3,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,1] (by decide +kernel))
      node_1131
      (invalid_excluded a [6,3,7,1,0,3] (by decide +kernel))
      node_1132
      (invalid_excluded a [6,3,7,1,0,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,0,7] (by decide +kernel))
      node_1133)

theorem node_1140 : Excluded a [6,3,7,1,2] :=
  predecessor_excluded a [6,3,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1142 : Excluded a [6,3,7,1,8,0] :=
  predecessor_excluded a [6,3,7,1,8,0] 2 1 5 3 (by decide) (by decide +kernel)

theorem node_1143 : Excluded a [6,3,7,1,8,2] :=
  source_excluded a [6,3,7,1,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1144 : Excluded a [6,3,7,1,8,4] :=
  source_excluded a [6,3,7,1,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1141 : Excluded a [6,3,7,1,8] :=
  branch_excluded a [6,3,7,1,8] (by decide)
    (fin9_cases _
      node_1142
      (invalid_excluded a [6,3,7,1,8,1] (by decide +kernel))
      node_1143
      (invalid_excluded a [6,3,7,1,8,3] (by decide +kernel))
      node_1144
      (invalid_excluded a [6,3,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,8,8] (by decide +kernel)))

theorem node_1129 : Excluded a [6,3,7,1] :=
  branch_excluded a [6,3,7,1] (by decide)
    (fin9_cases _
      node_1130
      (invalid_excluded a [6,3,7,1,1] (by decide +kernel))
      node_1140
      (invalid_excluded a [6,3,7,1,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,7] (by decide +kernel))
      node_1141)

theorem node_1145 : Excluded a [6,3,7,2] :=
  source_excluded a [6,3,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1146 : Excluded a [6,3,7,5] :=
  source_excluded a [6,3,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1149 : Excluded a [6,3,7,8,0,1] :=
  source_excluded a [6,3,7,8,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1150 : Excluded a [6,3,7,8,0,2] :=
  source_excluded a [6,3,7,8,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1151 : Excluded a [6,3,7,8,0,4] :=
  source_excluded a [6,3,7,8,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1148 : Excluded a [6,3,7,8,0] :=
  branch_excluded a [6,3,7,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,8,0,0] (by decide +kernel))
      node_1149
      node_1150
      (invalid_excluded a [6,3,7,8,0,3] (by decide +kernel))
      node_1151
      (invalid_excluded a [6,3,7,8,0,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,0,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,0,8] (by decide +kernel)))

theorem node_1152 : Excluded a [6,3,7,8,1] :=
  predecessor_excluded a [6,3,7,8,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1154 : Excluded a [6,3,7,8,2,0] :=
  predecessor_excluded a [6,3,7,8,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1155 : Excluded a [6,3,7,8,2,1] :=
  source_excluded a [6,3,7,8,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1156 : Excluded a [6,3,7,8,2,4] :=
  source_excluded a [6,3,7,8,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1153 : Excluded a [6,3,7,8,2] :=
  branch_excluded a [6,3,7,8,2] (by decide)
    (fin9_cases _
      node_1154
      node_1155
      (invalid_excluded a [6,3,7,8,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,3] (by decide +kernel))
      node_1156
      (invalid_excluded a [6,3,7,8,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,8] (by decide +kernel)))

theorem node_1147 : Excluded a [6,3,7,8] :=
  branch_excluded a [6,3,7,8] (by decide)
    (fin9_cases _
      node_1148
      node_1152
      node_1153
      (invalid_excluded a [6,3,7,8,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,4] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,8] (by decide +kernel)))

theorem node_1127 : Excluded a [6,3,7] :=
  branch_excluded a [6,3,7] (by decide)
    (fin9_cases _
      node_1128
      node_1129
      node_1145
      (invalid_excluded a [6,3,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,4] (by decide +kernel))
      node_1146
      (invalid_excluded a [6,3,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,7] (by decide +kernel))
      node_1147)

theorem node_1157 : Excluded a [6,3,8] :=
  predecessor_excluded a [6,3,8] 1 6 2 0 (by decide) (by decide +kernel)

theorem node_1088 : Excluded a [6,3] :=
  branch_excluded a [6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,0] (by decide +kernel))
      node_1089
      (invalid_excluded a [6,3,2] (by decide +kernel))
      (invalid_excluded a [6,3,3] (by decide +kernel))
      node_1090
      node_1091
      (invalid_excluded a [6,3,6] (by decide +kernel))
      node_1127
      node_1157)

theorem node_1159 : Excluded a [6,4,1] :=
  source_excluded a [6,4,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1161 : Excluded a [6,4,3,0] :=
  source_excluded a [6,4,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1162 : Excluded a [6,4,3,1] :=
  source_excluded a [6,4,3,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1163 : Excluded a [6,4,3,2] :=
  source_excluded a [6,4,3,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1164 : Excluded a [6,4,3,5] :=
  source_excluded a [6,4,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1166 : Excluded a [6,4,3,7,0] :=
  predecessor_excluded a [6,4,3,7,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1168 : Excluded a [6,4,3,7,1,0] :=
  source_excluded a [6,4,3,7,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1169 : Excluded a [6,4,3,7,1,2] :=
  source_excluded a [6,4,3,7,1,2] 5 0 2 (by decide) (by decide +kernel)

def b_1173 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 3
  | 3 => 7
  | 4 => 1
  | 5 => 8
  | 6 => 0
  | 7 => 2
  | 8 => 5
  | _ => 0

def cert_1173 : LosingRegion (edgeOf a b_1173) 0 :=
  losingMask a b_1173 0 1517098296111298107214848
    (by decide +kernel) (by decide +kernel)

theorem node_1173 : Excluded a [6,4,3,7,1,8,0,2,5] :=
  losing_excluded a [6,4,3,7,1,8,0,2,5] (by decide) b_1173 (by decide +kernel) 1 0 2 cert_1173 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1173 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1517098296111298107214848 1 2; decide +kernel)

theorem node_1172 : Excluded a [6,4,3,7,1,8,0,2] :=
  branch_excluded a [6,4,3,7,1,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,3,7,1,8,0,2,0] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,2,1] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,2,4] (by decide +kernel))
      node_1173
      (invalid_excluded a [6,4,3,7,1,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,2,8] (by decide +kernel)))

theorem node_1174 : Excluded a [6,4,3,7,1,8,0,5] :=
  source_excluded a [6,4,3,7,1,8,0,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_1171 : Excluded a [6,4,3,7,1,8,0] :=
  branch_excluded a [6,4,3,7,1,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,3,7,1,8,0,0] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,1] (by decide +kernel))
      node_1172
      (invalid_excluded a [6,4,3,7,1,8,0,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,4] (by decide +kernel))
      node_1174
      (invalid_excluded a [6,4,3,7,1,8,0,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,7] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,8] (by decide +kernel)))

theorem node_1175 : Excluded a [6,4,3,7,1,8,2] :=
  predecessor_excluded a [6,4,3,7,1,8,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1176 : Excluded a [6,4,3,7,1,8,5] :=
  predecessor_excluded a [6,4,3,7,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1170 : Excluded a [6,4,3,7,1,8] :=
  branch_excluded a [6,4,3,7,1,8] (by decide)
    (fin9_cases _
      node_1171
      (invalid_excluded a [6,4,3,7,1,8,1] (by decide +kernel))
      node_1175
      (invalid_excluded a [6,4,3,7,1,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,4] (by decide +kernel))
      node_1176
      (invalid_excluded a [6,4,3,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,8] (by decide +kernel)))

theorem node_1167 : Excluded a [6,4,3,7,1] :=
  branch_excluded a [6,4,3,7,1] (by decide)
    (fin9_cases _
      node_1168
      (invalid_excluded a [6,4,3,7,1,1] (by decide +kernel))
      node_1169
      (invalid_excluded a [6,4,3,7,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,7] (by decide +kernel))
      node_1170)

theorem node_1177 : Excluded a [6,4,3,7,2] :=
  source_excluded a [6,4,3,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1178 : Excluded a [6,4,3,7,8] :=
  predecessor_excluded a [6,4,3,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1165 : Excluded a [6,4,3,7] :=
  branch_excluded a [6,4,3,7] (by decide)
    (fin9_cases _
      node_1166
      node_1167
      node_1177
      (invalid_excluded a [6,4,3,7,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,7] (by decide +kernel))
      node_1178)

theorem node_1180 : Excluded a [6,4,3,8,0] :=
  predecessor_excluded a [6,4,3,8,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1182 : Excluded a [6,4,3,8,1,0] :=
  source_excluded a [6,4,3,8,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1183 : Excluded a [6,4,3,8,1,2] :=
  source_excluded a [6,4,3,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1184 : Excluded a [6,4,3,8,1,7] :=
  predecessor_excluded a [6,4,3,8,1,7] 0 8 5 3 (by decide) (by decide +kernel)

theorem node_1181 : Excluded a [6,4,3,8,1] :=
  branch_excluded a [6,4,3,8,1] (by decide)
    (fin9_cases _
      node_1182
      (invalid_excluded a [6,4,3,8,1,1] (by decide +kernel))
      node_1183
      (invalid_excluded a [6,4,3,8,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,1,6] (by decide +kernel))
      node_1184
      (invalid_excluded a [6,4,3,8,1,8] (by decide +kernel)))

theorem node_1185 : Excluded a [6,4,3,8,2] :=
  source_excluded a [6,4,3,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1187 : Excluded a [6,4,3,8,7,0] :=
  source_excluded a [6,4,3,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1188 : Excluded a [6,4,3,8,7,1] :=
  predecessor_excluded a [6,4,3,8,7,1] 0 4 5 1 (by decide) (by decide +kernel)

theorem node_1189 : Excluded a [6,4,3,8,7,2] :=
  source_excluded a [6,4,3,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1186 : Excluded a [6,4,3,8,7] :=
  branch_excluded a [6,4,3,8,7] (by decide)
    (fin9_cases _
      node_1187
      node_1188
      node_1189
      (invalid_excluded a [6,4,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,8] (by decide +kernel)))

theorem node_1179 : Excluded a [6,4,3,8] :=
  branch_excluded a [6,4,3,8] (by decide)
    (fin9_cases _
      node_1180
      node_1181
      node_1185
      (invalid_excluded a [6,4,3,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,6] (by decide +kernel))
      node_1186
      (invalid_excluded a [6,4,3,8,8] (by decide +kernel)))

theorem node_1160 : Excluded a [6,4,3] :=
  branch_excluded a [6,4,3] (by decide)
    (fin9_cases _
      node_1161
      node_1162
      node_1163
      (invalid_excluded a [6,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,4] (by decide +kernel))
      node_1164
      (invalid_excluded a [6,4,3,6] (by decide +kernel))
      node_1165
      node_1179)

theorem node_1190 : Excluded a [6,4,5] :=
  predecessor_excluded a [6,4,5] 0 5 1 2 (by decide) (by decide +kernel)

theorem node_1193 : Excluded a [6,4,7,0,1] :=
  predecessor_excluded a [6,4,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1194 : Excluded a [6,4,7,0,2] :=
  source_excluded a [6,4,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1195 : Excluded a [6,4,7,0,3] :=
  source_excluded a [6,4,7,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1197 : Excluded a [6,4,7,0,8,1] :=
  predecessor_excluded a [6,4,7,0,8,1] 0 4 5 1 (by decide) (by decide +kernel)

theorem node_1198 : Excluded a [6,4,7,0,8,2] :=
  predecessor_excluded a [6,4,7,0,8,2] 1 0 5 3 (by decide) (by decide +kernel)

theorem node_1196 : Excluded a [6,4,7,0,8] :=
  branch_excluded a [6,4,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,8,0] (by decide +kernel))
      node_1197
      node_1198
      (invalid_excluded a [6,4,7,0,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,8] (by decide +kernel)))

theorem node_1192 : Excluded a [6,4,7,0] :=
  branch_excluded a [6,4,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,0] (by decide +kernel))
      node_1193
      node_1194
      node_1195
      (invalid_excluded a [6,4,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,7] (by decide +kernel))
      node_1196)

theorem node_1199 : Excluded a [6,4,7,1] :=
  source_excluded a [6,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1200 : Excluded a [6,4,7,2] :=
  source_excluded a [6,4,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1201 : Excluded a [6,4,7,5] :=
  source_excluded a [6,4,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1203 : Excluded a [6,4,7,8,0] :=
  predecessor_excluded a [6,4,7,8,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1206 : Excluded a [6,4,7,8,1,0,2] :=
  source_excluded a [6,4,7,8,1,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1207 : Excluded a [6,4,7,8,1,0,3] :=
  predecessor_excluded a [6,4,7,8,1,0,3] 0 8 6 3 (by decide) (by decide +kernel)

def b_1210 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 7
  | 3 => 8
  | 4 => 1
  | 5 => 0
  | 6 => 5
  | 7 => 2
  | 8 => 3
  | _ => 0

def cert_1210 : LosingRegion (edgeOf a b_1210) 0 :=
  losingMask a b_1210 0 1337667088783931803173888
    (by decide +kernel) (by decide +kernel)

theorem node_1210 : Excluded a [6,4,7,8,1,0,5,2,3] :=
  losing_excluded a [6,4,7,8,1,0,5,2,3] (by decide) b_1210 (by decide +kernel) 3 0 1 cert_1210 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1210 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1337667088783931803173888 3 1; decide +kernel)

theorem node_1209 : Excluded a [6,4,7,8,1,0,5,2] :=
  branch_excluded a [6,4,7,8,1,0,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,8,1,0,5,2,0] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,2,1] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,2,2] (by decide +kernel))
      node_1210
      (invalid_excluded a [6,4,7,8,1,0,5,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,2,8] (by decide +kernel)))

theorem node_1211 : Excluded a [6,4,7,8,1,0,5,3] :=
  source_excluded a [6,4,7,8,1,0,5,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_1208 : Excluded a [6,4,7,8,1,0,5] :=
  branch_excluded a [6,4,7,8,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,8,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,1] (by decide +kernel))
      node_1209
      node_1211
      (invalid_excluded a [6,4,7,8,1,0,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,5,8] (by decide +kernel)))

theorem node_1205 : Excluded a [6,4,7,8,1,0] :=
  branch_excluded a [6,4,7,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,1] (by decide +kernel))
      node_1206
      node_1207
      (invalid_excluded a [6,4,7,8,1,0,4] (by decide +kernel))
      node_1208
      (invalid_excluded a [6,4,7,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,0,8] (by decide +kernel)))

theorem node_1212 : Excluded a [6,4,7,8,1,2] :=
  predecessor_excluded a [6,4,7,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1204 : Excluded a [6,4,7,8,1] :=
  branch_excluded a [6,4,7,8,1] (by decide)
    (fin9_cases _
      node_1205
      (invalid_excluded a [6,4,7,8,1,1] (by decide +kernel))
      node_1212
      (invalid_excluded a [6,4,7,8,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,8] (by decide +kernel)))

theorem node_1213 : Excluded a [6,4,7,8,2] :=
  source_excluded a [6,4,7,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1214 : Excluded a [6,4,7,8,3] :=
  source_excluded a [6,4,7,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1202 : Excluded a [6,4,7,8] :=
  branch_excluded a [6,4,7,8] (by decide)
    (fin9_cases _
      node_1203
      node_1204
      node_1213
      node_1214
      (invalid_excluded a [6,4,7,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,8] (by decide +kernel)))

theorem node_1191 : Excluded a [6,4,7] :=
  branch_excluded a [6,4,7] (by decide)
    (fin9_cases _
      node_1192
      node_1199
      node_1200
      (invalid_excluded a [6,4,7,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,4] (by decide +kernel))
      node_1201
      (invalid_excluded a [6,4,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,7] (by decide +kernel))
      node_1202)

theorem node_1215 : Excluded a [6,4,8] :=
  predecessor_excluded a [6,4,8] 1 6 2 0 (by decide) (by decide +kernel)

theorem node_1158 : Excluded a [6,4] :=
  branch_excluded a [6,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0] (by decide +kernel))
      node_1159
      (invalid_excluded a [6,4,2] (by decide +kernel))
      node_1160
      (invalid_excluded a [6,4,4] (by decide +kernel))
      node_1190
      (invalid_excluded a [6,4,6] (by decide +kernel))
      node_1191
      node_1215)

theorem node_1217 : Excluded a [6,5,1] :=
  source_excluded a [6,5,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1218 : Excluded a [6,5,3] :=
  predecessor_excluded a [6,5,3] 0 3 1 2 (by decide) (by decide +kernel)

theorem node_1220 : Excluded a [6,5,4,0] :=
  source_excluded a [6,5,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1221 : Excluded a [6,5,4,1] :=
  predecessor_excluded a [6,5,4,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1222 : Excluded a [6,5,4,2] :=
  source_excluded a [6,5,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_1224 : Excluded a [6,5,4,7,0] :=
  source_excluded a [6,5,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1225 : Excluded a [6,5,4,7,1] :=
  source_excluded a [6,5,4,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1226 : Excluded a [6,5,4,7,2] :=
  source_excluded a [6,5,4,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1227 : Excluded a [6,5,4,7,3] :=
  source_excluded a [6,5,4,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1228 : Excluded a [6,5,4,7,8] :=
  predecessor_excluded a [6,5,4,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1223 : Excluded a [6,5,4,7] :=
  branch_excluded a [6,5,4,7] (by decide)
    (fin9_cases _
      node_1224
      node_1225
      node_1226
      node_1227
      (invalid_excluded a [6,5,4,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,7] (by decide +kernel))
      node_1228)

theorem node_1230 : Excluded a [6,5,4,8,0] :=
  source_excluded a [6,5,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1231 : Excluded a [6,5,4,8,1] :=
  source_excluded a [6,5,4,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1232 : Excluded a [6,5,4,8,2] :=
  source_excluded a [6,5,4,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1233 : Excluded a [6,5,4,8,3] :=
  source_excluded a [6,5,4,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1235 : Excluded a [6,5,4,8,7,0] :=
  predecessor_excluded a [6,5,4,8,7,0] 3 0 1 5 (by decide) (by decide +kernel)

def b_1239 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 5
  | 2 => 4
  | 3 => 8
  | 4 => 7
  | 5 => 1
  | 6 => 0
  | 7 => 2
  | 8 => 3
  | _ => 0

def cert_1239 : LosingRegion (edgeOf a b_1239) 0 :=
  losingMask a b_1239 0 1517098287736833300302848
    (by decide +kernel) (by decide +kernel)

theorem node_1239 : Excluded a [6,5,4,8,7,1,0,2,3] :=
  losing_excluded a [6,5,4,8,7,1,0,2,3] (by decide) b_1239 (by decide +kernel) 1 0 2 cert_1239 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1239 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1517098287736833300302848 1 2; decide +kernel)

theorem node_1238 : Excluded a [6,5,4,8,7,1,0,2] :=
  branch_excluded a [6,5,4,8,7,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,4,8,7,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,2,2] (by decide +kernel))
      node_1239
      (invalid_excluded a [6,5,4,8,7,1,0,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,2,8] (by decide +kernel)))

theorem node_1240 : Excluded a [6,5,4,8,7,1,0,3] :=
  source_excluded a [6,5,4,8,7,1,0,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_1237 : Excluded a [6,5,4,8,7,1,0] :=
  branch_excluded a [6,5,4,8,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,4,8,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,1] (by decide +kernel))
      node_1238
      node_1240
      (invalid_excluded a [6,5,4,8,7,1,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,0,8] (by decide +kernel)))

theorem node_1241 : Excluded a [6,5,4,8,7,1,2] :=
  predecessor_excluded a [6,5,4,8,7,1,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1242 : Excluded a [6,5,4,8,7,1,3] :=
  predecessor_excluded a [6,5,4,8,7,1,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1236 : Excluded a [6,5,4,8,7,1] :=
  branch_excluded a [6,5,4,8,7,1] (by decide)
    (fin9_cases _
      node_1237
      (invalid_excluded a [6,5,4,8,7,1,1] (by decide +kernel))
      node_1241
      node_1242
      (invalid_excluded a [6,5,4,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,1,8] (by decide +kernel)))

theorem node_1243 : Excluded a [6,5,4,8,7,2] :=
  source_excluded a [6,5,4,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1234 : Excluded a [6,5,4,8,7] :=
  branch_excluded a [6,5,4,8,7] (by decide)
    (fin9_cases _
      node_1235
      node_1236
      node_1243
      (invalid_excluded a [6,5,4,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,8] (by decide +kernel)))

theorem node_1229 : Excluded a [6,5,4,8] :=
  branch_excluded a [6,5,4,8] (by decide)
    (fin9_cases _
      node_1230
      node_1231
      node_1232
      node_1233
      (invalid_excluded a [6,5,4,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,6] (by decide +kernel))
      node_1234
      (invalid_excluded a [6,5,4,8,8] (by decide +kernel)))

theorem node_1219 : Excluded a [6,5,4] :=
  branch_excluded a [6,5,4] (by decide)
    (fin9_cases _
      node_1220
      node_1221
      node_1222
      (invalid_excluded a [6,5,4,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,6] (by decide +kernel))
      node_1223
      node_1229)

theorem node_1246 : Excluded a [6,5,7,0,1] :=
  source_excluded a [6,5,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1247 : Excluded a [6,5,7,0,2] :=
  source_excluded a [6,5,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1248 : Excluded a [6,5,7,0,3] :=
  source_excluded a [6,5,7,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1251 : Excluded a [6,5,7,0,8,1,2] :=
  source_excluded a [6,5,7,0,8,1,2] 6 0 2 (by decide) (by decide +kernel)

def b_1254 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 5
  | 2 => 7
  | 3 => 0
  | 4 => 8
  | 5 => 1
  | 6 => 3
  | 7 => 2
  | 8 => 4
  | _ => 0

def cert_1254 : LosingRegion (edgeOf a b_1254) 0 :=
  losingMask a b_1254 0 1451004172605513486304256
    (by decide +kernel) (by decide +kernel)

theorem node_1254 : Excluded a [6,5,7,0,8,1,3,2,4] :=
  losing_excluded a [6,5,7,0,8,1,3,2,4] (by decide) b_1254 (by decide +kernel) 4 0 1 cert_1254 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1254 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1451004172605513486304256 4 1; decide +kernel)

theorem node_1253 : Excluded a [6,5,7,0,8,1,3,2] :=
  branch_excluded a [6,5,7,0,8,1,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,1,3,2,0] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,2,3] (by decide +kernel))
      node_1254
      (invalid_excluded a [6,5,7,0,8,1,3,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,2,8] (by decide +kernel)))

theorem node_1255 : Excluded a [6,5,7,0,8,1,3,4] :=
  source_excluded a [6,5,7,0,8,1,3,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_1252 : Excluded a [6,5,7,0,8,1,3] :=
  branch_excluded a [6,5,7,0,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,1] (by decide +kernel))
      node_1253
      (invalid_excluded a [6,5,7,0,8,1,3,3] (by decide +kernel))
      node_1255
      (invalid_excluded a [6,5,7,0,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,3,8] (by decide +kernel)))

theorem node_1256 : Excluded a [6,5,7,0,8,1,4] :=
  predecessor_excluded a [6,5,7,0,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1250 : Excluded a [6,5,7,0,8,1] :=
  branch_excluded a [6,5,7,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,1] (by decide +kernel))
      node_1251
      node_1252
      node_1256
      (invalid_excluded a [6,5,7,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,1,8] (by decide +kernel)))

theorem node_1257 : Excluded a [6,5,7,0,8,2] :=
  source_excluded a [6,5,7,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1258 : Excluded a [6,5,7,0,8,4] :=
  source_excluded a [6,5,7,0,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1249 : Excluded a [6,5,7,0,8] :=
  branch_excluded a [6,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,0] (by decide +kernel))
      node_1250
      node_1257
      (invalid_excluded a [6,5,7,0,8,3] (by decide +kernel))
      node_1258
      (invalid_excluded a [6,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,8] (by decide +kernel)))

theorem node_1245 : Excluded a [6,5,7,0] :=
  branch_excluded a [6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,0] (by decide +kernel))
      node_1246
      node_1247
      node_1248
      (invalid_excluded a [6,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,7] (by decide +kernel))
      node_1249)

theorem node_1259 : Excluded a [6,5,7,1] :=
  predecessor_excluded a [6,5,7,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1261 : Excluded a [6,5,7,2,0] :=
  predecessor_excluded a [6,5,7,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1262 : Excluded a [6,5,7,2,1] :=
  source_excluded a [6,5,7,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1263 : Excluded a [6,5,7,2,3] :=
  source_excluded a [6,5,7,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1265 : Excluded a [6,5,7,2,8,0] :=
  predecessor_excluded a [6,5,7,2,8,0] 3 0 1 5 (by decide) (by decide +kernel)

theorem node_1266 : Excluded a [6,5,7,2,8,1] :=
  predecessor_excluded a [6,5,7,2,8,1] 0 2 5 3 (by decide) (by decide +kernel)

theorem node_1267 : Excluded a [6,5,7,2,8,4] :=
  source_excluded a [6,5,7,2,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1264 : Excluded a [6,5,7,2,8] :=
  branch_excluded a [6,5,7,2,8] (by decide)
    (fin9_cases _
      node_1265
      node_1266
      (invalid_excluded a [6,5,7,2,8,2] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,3] (by decide +kernel))
      node_1267
      (invalid_excluded a [6,5,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,8] (by decide +kernel)))

theorem node_1260 : Excluded a [6,5,7,2] :=
  branch_excluded a [6,5,7,2] (by decide)
    (fin9_cases _
      node_1261
      node_1262
      (invalid_excluded a [6,5,7,2,2] (by decide +kernel))
      node_1263
      (invalid_excluded a [6,5,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,7] (by decide +kernel))
      node_1264)

theorem node_1270 : Excluded a [6,5,7,8,0,1] :=
  predecessor_excluded a [6,5,7,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1271 : Excluded a [6,5,7,8,0,2] :=
  source_excluded a [6,5,7,8,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1272 : Excluded a [6,5,7,8,0,4] :=
  source_excluded a [6,5,7,8,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1269 : Excluded a [6,5,7,8,0] :=
  branch_excluded a [6,5,7,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,8,0,0] (by decide +kernel))
      node_1270
      node_1271
      (invalid_excluded a [6,5,7,8,0,3] (by decide +kernel))
      node_1272
      (invalid_excluded a [6,5,7,8,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,0,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,0,8] (by decide +kernel)))

theorem node_1273 : Excluded a [6,5,7,8,1] :=
  source_excluded a [6,5,7,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1274 : Excluded a [6,5,7,8,2] :=
  source_excluded a [6,5,7,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1275 : Excluded a [6,5,7,8,3] :=
  source_excluded a [6,5,7,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1268 : Excluded a [6,5,7,8] :=
  branch_excluded a [6,5,7,8] (by decide)
    (fin9_cases _
      node_1269
      node_1273
      node_1274
      node_1275
      (invalid_excluded a [6,5,7,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,8] (by decide +kernel)))

theorem node_1244 : Excluded a [6,5,7] :=
  branch_excluded a [6,5,7] (by decide)
    (fin9_cases _
      node_1245
      node_1259
      node_1260
      (invalid_excluded a [6,5,7,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,7] (by decide +kernel))
      node_1268)

theorem node_1276 : Excluded a [6,5,8] :=
  predecessor_excluded a [6,5,8] 1 6 2 0 (by decide) (by decide +kernel)

theorem node_1216 : Excluded a [6,5] :=
  branch_excluded a [6,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0] (by decide +kernel))
      node_1217
      (invalid_excluded a [6,5,2] (by decide +kernel))
      node_1218
      node_1219
      (invalid_excluded a [6,5,5] (by decide +kernel))
      (invalid_excluded a [6,5,6] (by decide +kernel))
      node_1244
      node_1276)

theorem node_1277 : Excluded a [6,7] :=
  predecessor_excluded a [6,7] 2 7 0 1 (by decide) (by decide +kernel)

theorem node_1279 : Excluded a [6,8,1] :=
  source_excluded a [6,8,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1281 : Excluded a [6,8,3,0] :=
  source_excluded a [6,8,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1282 : Excluded a [6,8,3,1] :=
  predecessor_excluded a [6,8,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_1284 : Excluded a [6,8,3,2,0] :=
  predecessor_excluded a [6,8,3,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1286 : Excluded a [6,8,3,2,1,0] :=
  source_excluded a [6,8,3,2,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1287 : Excluded a [6,8,3,2,1,4] :=
  source_excluded a [6,8,3,2,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1290 : Excluded a [6,8,3,2,1,7,0,4] :=
  predecessor_excluded a [6,8,3,2,1,7,0,4] 0 4 5 7 (by decide) (by decide +kernel)

def b_1292 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 7
  | 6 => 0
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_1292 : LosingRegion (edgeOf a b_1292) 0 :=
  losingMask a b_1292 0 1520077430418177268911104
    (by decide +kernel) (by decide +kernel)

theorem node_1292 : Excluded a [6,8,3,2,1,7,0,5,4] :=
  losing_excluded a [6,8,3,2,1,7,0,5,4] (by decide) b_1292 (by decide +kernel) 1 0 2 cert_1292 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1292 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1520077430418177268911104 1 2; decide +kernel)

theorem node_1291 : Excluded a [6,8,3,2,1,7,0,5] :=
  branch_excluded a [6,8,3,2,1,7,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,3,2,1,7,0,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,5,3] (by decide +kernel))
      node_1292
      (invalid_excluded a [6,8,3,2,1,7,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,5,8] (by decide +kernel)))

theorem node_1289 : Excluded a [6,8,3,2,1,7,0] :=
  branch_excluded a [6,8,3,2,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,3,2,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,2] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,3] (by decide +kernel))
      node_1290
      node_1291
      (invalid_excluded a [6,8,3,2,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,0,8] (by decide +kernel)))

theorem node_1294 : Excluded a [6,8,3,2,1,7,4,0] :=
  predecessor_excluded a [6,8,3,2,1,7,4,0] 1 6 7 0 (by decide) (by decide +kernel)

theorem node_1295 : Excluded a [6,8,3,2,1,7,4,5] :=
  predecessor_excluded a [6,8,3,2,1,7,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1293 : Excluded a [6,8,3,2,1,7,4] :=
  branch_excluded a [6,8,3,2,1,7,4] (by decide)
    (fin9_cases _
      node_1294
      (invalid_excluded a [6,8,3,2,1,7,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,4,2] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,4,3] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,4,4] (by decide +kernel))
      node_1295
      (invalid_excluded a [6,8,3,2,1,7,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,4,8] (by decide +kernel)))

theorem node_1296 : Excluded a [6,8,3,2,1,7,5] :=
  source_excluded a [6,8,3,2,1,7,5] 6 0 5 (by decide) (by decide +kernel)

theorem node_1288 : Excluded a [6,8,3,2,1,7] :=
  branch_excluded a [6,8,3,2,1,7] (by decide)
    (fin9_cases _
      node_1289
      (invalid_excluded a [6,8,3,2,1,7,1] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,2] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,3] (by decide +kernel))
      node_1293
      node_1296
      (invalid_excluded a [6,8,3,2,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,7,8] (by decide +kernel)))

theorem node_1285 : Excluded a [6,8,3,2,1] :=
  branch_excluded a [6,8,3,2,1] (by decide)
    (fin9_cases _
      node_1286
      (invalid_excluded a [6,8,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,3] (by decide +kernel))
      node_1287
      (invalid_excluded a [6,8,3,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,1,6] (by decide +kernel))
      node_1288
      (invalid_excluded a [6,8,3,2,1,8] (by decide +kernel)))

theorem node_1298 : Excluded a [6,8,3,2,7,0] :=
  source_excluded a [6,8,3,2,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1299 : Excluded a [6,8,3,2,7,1] :=
  predecessor_excluded a [6,8,3,2,7,1] 0 2 5 3 (by decide) (by decide +kernel)

theorem node_1300 : Excluded a [6,8,3,2,7,4] :=
  source_excluded a [6,8,3,2,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1297 : Excluded a [6,8,3,2,7] :=
  branch_excluded a [6,8,3,2,7] (by decide)
    (fin9_cases _
      node_1298
      node_1299
      (invalid_excluded a [6,8,3,2,7,2] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,7,3] (by decide +kernel))
      node_1300
      (invalid_excluded a [6,8,3,2,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,7,8] (by decide +kernel)))

theorem node_1283 : Excluded a [6,8,3,2] :=
  branch_excluded a [6,8,3,2] (by decide)
    (fin9_cases _
      node_1284
      node_1285
      (invalid_excluded a [6,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,4] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,3,2,6] (by decide +kernel))
      node_1297
      (invalid_excluded a [6,8,3,2,8] (by decide +kernel)))

theorem node_1301 : Excluded a [6,8,3,5] :=
  source_excluded a [6,8,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1304 : Excluded a [6,8,3,7,0,1] :=
  predecessor_excluded a [6,8,3,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1305 : Excluded a [6,8,3,7,0,2] :=
  source_excluded a [6,8,3,7,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1306 : Excluded a [6,8,3,7,0,4] :=
  source_excluded a [6,8,3,7,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1303 : Excluded a [6,8,3,7,0] :=
  branch_excluded a [6,8,3,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,3,7,0,0] (by decide +kernel))
      node_1304
      node_1305
      (invalid_excluded a [6,8,3,7,0,3] (by decide +kernel))
      node_1306
      (invalid_excluded a [6,8,3,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,0,8] (by decide +kernel)))

theorem node_1308 : Excluded a [6,8,3,7,1,0] :=
  source_excluded a [6,8,3,7,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1309 : Excluded a [6,8,3,7,1,2] :=
  source_excluded a [6,8,3,7,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1310 : Excluded a [6,8,3,7,1,4] :=
  source_excluded a [6,8,3,7,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1307 : Excluded a [6,8,3,7,1] :=
  branch_excluded a [6,8,3,7,1] (by decide)
    (fin9_cases _
      node_1308
      (invalid_excluded a [6,8,3,7,1,1] (by decide +kernel))
      node_1309
      (invalid_excluded a [6,8,3,7,1,3] (by decide +kernel))
      node_1310
      (invalid_excluded a [6,8,3,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,1,8] (by decide +kernel)))

theorem node_1311 : Excluded a [6,8,3,7,2] :=
  predecessor_excluded a [6,8,3,7,2] 0 3 4 2 (by decide) (by decide +kernel)

theorem node_1302 : Excluded a [6,8,3,7] :=
  branch_excluded a [6,8,3,7] (by decide)
    (fin9_cases _
      node_1303
      node_1307
      node_1311
      (invalid_excluded a [6,8,3,7,3] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,3,7,8] (by decide +kernel)))

theorem node_1280 : Excluded a [6,8,3] :=
  branch_excluded a [6,8,3] (by decide)
    (fin9_cases _
      node_1281
      node_1282
      node_1283
      (invalid_excluded a [6,8,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,3,4] (by decide +kernel))
      node_1301
      (invalid_excluded a [6,8,3,6] (by decide +kernel))
      node_1302
      (invalid_excluded a [6,8,3,8] (by decide +kernel)))

theorem node_1313 : Excluded a [6,8,4,0] :=
  source_excluded a [6,8,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1315 : Excluded a [6,8,4,1,0] :=
  source_excluded a [6,8,4,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1316 : Excluded a [6,8,4,1,2] :=
  predecessor_excluded a [6,8,4,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1317 : Excluded a [6,8,4,1,3] :=
  source_excluded a [6,8,4,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1319 : Excluded a [6,8,4,1,7,0] :=
  predecessor_excluded a [6,8,4,1,7,0] 2 1 5 3 (by decide) (by decide +kernel)

theorem node_1320 : Excluded a [6,8,4,1,7,2] :=
  predecessor_excluded a [6,8,4,1,7,2] 0 4 5 2 (by decide) (by decide +kernel)

theorem node_1318 : Excluded a [6,8,4,1,7] :=
  branch_excluded a [6,8,4,1,7] (by decide)
    (fin9_cases _
      node_1319
      (invalid_excluded a [6,8,4,1,7,1] (by decide +kernel))
      node_1320
      (invalid_excluded a [6,8,4,1,7,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,8] (by decide +kernel)))

theorem node_1314 : Excluded a [6,8,4,1] :=
  branch_excluded a [6,8,4,1] (by decide)
    (fin9_cases _
      node_1315
      (invalid_excluded a [6,8,4,1,1] (by decide +kernel))
      node_1316
      node_1317
      (invalid_excluded a [6,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,6] (by decide +kernel))
      node_1318
      (invalid_excluded a [6,8,4,1,8] (by decide +kernel)))

theorem node_1321 : Excluded a [6,8,4,2] :=
  source_excluded a [6,8,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_1322 : Excluded a [6,8,4,5] :=
  source_excluded a [6,8,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1324 : Excluded a [6,8,4,7,0] :=
  source_excluded a [6,8,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1325 : Excluded a [6,8,4,7,1] :=
  predecessor_excluded a [6,8,4,7,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_1327 : Excluded a [6,8,4,7,2,0] :=
  predecessor_excluded a [6,8,4,7,2,0] 1 0 4 5 (by decide) (by decide +kernel)

def b_1331 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 4
  | 3 => 7
  | 4 => 2
  | 5 => 1
  | 6 => 0
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_1331 : LosingRegion (edgeOf a b_1331) 0 :=
  losingMask a b_1331 0 1520077430136090393578496
    (by decide +kernel) (by decide +kernel)

theorem node_1331 : Excluded a [6,8,4,7,2,1,0,3,5] :=
  losing_excluded a [6,8,4,7,2,1,0,3,5] (by decide) b_1331 (by decide +kernel) 1 0 2 cert_1331 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1331 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1520077430136090393578496 1 2; decide +kernel)

theorem node_1330 : Excluded a [6,8,4,7,2,1,0,3] :=
  branch_excluded a [6,8,4,7,2,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,4,7,2,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,3,4] (by decide +kernel))
      node_1331
      (invalid_excluded a [6,8,4,7,2,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,3,8] (by decide +kernel)))

theorem node_1332 : Excluded a [6,8,4,7,2,1,0,5] :=
  predecessor_excluded a [6,8,4,7,2,1,0,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_1329 : Excluded a [6,8,4,7,2,1,0] :=
  branch_excluded a [6,8,4,7,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,4,7,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,2] (by decide +kernel))
      node_1330
      (invalid_excluded a [6,8,4,7,2,1,0,4] (by decide +kernel))
      node_1332
      (invalid_excluded a [6,8,4,7,2,1,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,0,8] (by decide +kernel)))

theorem node_1333 : Excluded a [6,8,4,7,2,1,3] :=
  source_excluded a [6,8,4,7,2,1,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1335 : Excluded a [6,8,4,7,2,1,5,0] :=
  predecessor_excluded a [6,8,4,7,2,1,5,0] 1 6 7 0 (by decide) (by decide +kernel)

theorem node_1336 : Excluded a [6,8,4,7,2,1,5,3] :=
  predecessor_excluded a [6,8,4,7,2,1,5,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_1334 : Excluded a [6,8,4,7,2,1,5] :=
  branch_excluded a [6,8,4,7,2,1,5] (by decide)
    (fin9_cases _
      node_1335
      (invalid_excluded a [6,8,4,7,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,5,2] (by decide +kernel))
      node_1336
      (invalid_excluded a [6,8,4,7,2,1,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,5,8] (by decide +kernel)))

theorem node_1328 : Excluded a [6,8,4,7,2,1] :=
  branch_excluded a [6,8,4,7,2,1] (by decide)
    (fin9_cases _
      node_1329
      (invalid_excluded a [6,8,4,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,2] (by decide +kernel))
      node_1333
      (invalid_excluded a [6,8,4,7,2,1,4] (by decide +kernel))
      node_1334
      (invalid_excluded a [6,8,4,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,1,8] (by decide +kernel)))

theorem node_1326 : Excluded a [6,8,4,7,2] :=
  branch_excluded a [6,8,4,7,2] (by decide)
    (fin9_cases _
      node_1327
      node_1328
      (invalid_excluded a [6,8,4,7,2,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,8] (by decide +kernel)))

theorem node_1337 : Excluded a [6,8,4,7,3] :=
  source_excluded a [6,8,4,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1323 : Excluded a [6,8,4,7] :=
  branch_excluded a [6,8,4,7] (by decide)
    (fin9_cases _
      node_1324
      node_1325
      node_1326
      node_1337
      (invalid_excluded a [6,8,4,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,8] (by decide +kernel)))

theorem node_1312 : Excluded a [6,8,4] :=
  branch_excluded a [6,8,4] (by decide)
    (fin9_cases _
      node_1313
      node_1314
      node_1321
      (invalid_excluded a [6,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,4] (by decide +kernel))
      node_1322
      (invalid_excluded a [6,8,4,6] (by decide +kernel))
      node_1323
      (invalid_excluded a [6,8,4,8] (by decide +kernel)))

theorem node_1340 : Excluded a [6,8,5,0,1] :=
  predecessor_excluded a [6,8,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1341 : Excluded a [6,8,5,0,2] :=
  source_excluded a [6,8,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1342 : Excluded a [6,8,5,0,3] :=
  source_excluded a [6,8,5,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1344 : Excluded a [6,8,5,0,7,1] :=
  predecessor_excluded a [6,8,5,0,7,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_1345 : Excluded a [6,8,5,0,7,2] :=
  predecessor_excluded a [6,8,5,0,7,2] 1 0 5 3 (by decide) (by decide +kernel)

theorem node_1346 : Excluded a [6,8,5,0,7,4] :=
  source_excluded a [6,8,5,0,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1343 : Excluded a [6,8,5,0,7] :=
  branch_excluded a [6,8,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,7,0] (by decide +kernel))
      node_1344
      node_1345
      (invalid_excluded a [6,8,5,0,7,3] (by decide +kernel))
      node_1346
      (invalid_excluded a [6,8,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,8] (by decide +kernel)))

theorem node_1339 : Excluded a [6,8,5,0] :=
  branch_excluded a [6,8,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,0] (by decide +kernel))
      node_1340
      node_1341
      node_1342
      (invalid_excluded a [6,8,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,6] (by decide +kernel))
      node_1343
      (invalid_excluded a [6,8,5,0,8] (by decide +kernel)))

theorem node_1348 : Excluded a [6,8,5,1,0] :=
  source_excluded a [6,8,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1349 : Excluded a [6,8,5,1,2] :=
  source_excluded a [6,8,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1350 : Excluded a [6,8,5,1,3] :=
  source_excluded a [6,8,5,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1352 : Excluded a [6,8,5,1,7,0] :=
  source_excluded a [6,8,5,1,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1355 : Excluded a [6,8,5,1,7,2,0,3] :=
  predecessor_excluded a [6,8,5,1,7,2,0,3] 0 3 4 7 (by decide) (by decide +kernel)

def b_1357 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 5
  | 3 => 1
  | 4 => 7
  | 5 => 2
  | 6 => 0
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_1357 : LosingRegion (edgeOf a b_1357) 0 :=
  losingMask a b_1357 0 1520077429540771419130880
    (by decide +kernel) (by decide +kernel)

theorem node_1357 : Excluded a [6,8,5,1,7,2,0,4,3] :=
  losing_excluded a [6,8,5,1,7,2,0,4,3] (by decide) b_1357 (by decide +kernel) 1 0 2 cert_1357 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1357 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1520077429540771419130880 1 2; decide +kernel)

theorem node_1356 : Excluded a [6,8,5,1,7,2,0,4] :=
  branch_excluded a [6,8,5,1,7,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,1,7,2,0,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,2] (by decide +kernel))
      node_1357
      (invalid_excluded a [6,8,5,1,7,2,0,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,8] (by decide +kernel)))

theorem node_1354 : Excluded a [6,8,5,1,7,2,0] :=
  branch_excluded a [6,8,5,1,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,1,7,2,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,2] (by decide +kernel))
      node_1355
      node_1356
      (invalid_excluded a [6,8,5,1,7,2,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,8] (by decide +kernel)))

theorem node_1359 : Excluded a [6,8,5,1,7,2,3,0] :=
  predecessor_excluded a [6,8,5,1,7,2,3,0] 1 6 7 0 (by decide) (by decide +kernel)

theorem node_1360 : Excluded a [6,8,5,1,7,2,3,4] :=
  predecessor_excluded a [6,8,5,1,7,2,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_1358 : Excluded a [6,8,5,1,7,2,3] :=
  branch_excluded a [6,8,5,1,7,2,3] (by decide)
    (fin9_cases _
      node_1359
      (invalid_excluded a [6,8,5,1,7,2,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,3,3] (by decide +kernel))
      node_1360
      (invalid_excluded a [6,8,5,1,7,2,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,3,8] (by decide +kernel)))

theorem node_1361 : Excluded a [6,8,5,1,7,2,4] :=
  source_excluded a [6,8,5,1,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1353 : Excluded a [6,8,5,1,7,2] :=
  branch_excluded a [6,8,5,1,7,2] (by decide)
    (fin9_cases _
      node_1354
      (invalid_excluded a [6,8,5,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,2] (by decide +kernel))
      node_1358
      node_1361
      (invalid_excluded a [6,8,5,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,8] (by decide +kernel)))

theorem node_1362 : Excluded a [6,8,5,1,7,4] :=
  source_excluded a [6,8,5,1,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1351 : Excluded a [6,8,5,1,7] :=
  branch_excluded a [6,8,5,1,7] (by decide)
    (fin9_cases _
      node_1352
      (invalid_excluded a [6,8,5,1,7,1] (by decide +kernel))
      node_1353
      (invalid_excluded a [6,8,5,1,7,3] (by decide +kernel))
      node_1362
      (invalid_excluded a [6,8,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,8] (by decide +kernel)))

theorem node_1347 : Excluded a [6,8,5,1] :=
  branch_excluded a [6,8,5,1] (by decide)
    (fin9_cases _
      node_1348
      (invalid_excluded a [6,8,5,1,1] (by decide +kernel))
      node_1349
      node_1350
      (invalid_excluded a [6,8,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,6] (by decide +kernel))
      node_1351
      (invalid_excluded a [6,8,5,1,8] (by decide +kernel)))

theorem node_1363 : Excluded a [6,8,5,2] :=
  predecessor_excluded a [6,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_1365 : Excluded a [6,8,5,7,0] :=
  source_excluded a [6,8,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1367 : Excluded a [6,8,5,7,1,0] :=
  source_excluded a [6,8,5,7,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1368 : Excluded a [6,8,5,7,1,2] :=
  predecessor_excluded a [6,8,5,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1369 : Excluded a [6,8,5,7,1,4] :=
  source_excluded a [6,8,5,7,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1366 : Excluded a [6,8,5,7,1] :=
  branch_excluded a [6,8,5,7,1] (by decide)
    (fin9_cases _
      node_1367
      (invalid_excluded a [6,8,5,7,1,1] (by decide +kernel))
      node_1368
      (invalid_excluded a [6,8,5,7,1,3] (by decide +kernel))
      node_1369
      (invalid_excluded a [6,8,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,8] (by decide +kernel)))

theorem node_1370 : Excluded a [6,8,5,7,2] :=
  source_excluded a [6,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1371 : Excluded a [6,8,5,7,3] :=
  source_excluded a [6,8,5,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1364 : Excluded a [6,8,5,7] :=
  branch_excluded a [6,8,5,7] (by decide)
    (fin9_cases _
      node_1365
      node_1366
      node_1370
      node_1371
      (invalid_excluded a [6,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,8] (by decide +kernel)))

theorem node_1338 : Excluded a [6,8,5] :=
  branch_excluded a [6,8,5] (by decide)
    (fin9_cases _
      node_1339
      node_1347
      node_1363
      (invalid_excluded a [6,8,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,6] (by decide +kernel))
      node_1364
      (invalid_excluded a [6,8,5,8] (by decide +kernel)))

theorem node_1374 : Excluded a [6,8,7,0,1] :=
  predecessor_excluded a [6,8,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1378 : Excluded a [6,8,7,0,2,1,3,4] :=
  predecessor_excluded a [6,8,7,0,2,1,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_1380 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 3
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_1380 : LosingRegion (edgeOf a b_1380) 0 :=
  losingMask a b_1380 0 1324551886374561100342272
    (by decide +kernel) (by decide +kernel)

theorem node_1380 : Excluded a [6,8,7,0,2,1,3,5,4] :=
  losing_excluded a [6,8,7,0,2,1,3,5,4] (by decide) b_1380 (by decide +kernel) 1 0 4 cert_1380 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1380 1 0 ∧ 4 ≠ 1 ∧ maskRegion 1324551886374561100342272 1 4; decide +kernel)

theorem node_1379 : Excluded a [6,8,7,0,2,1,3,5] :=
  branch_excluded a [6,8,7,0,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,5,3] (by decide +kernel))
      node_1380
      (invalid_excluded a [6,8,7,0,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,5,8] (by decide +kernel)))

theorem node_1377 : Excluded a [6,8,7,0,2,1,3] :=
  branch_excluded a [6,8,7,0,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,3] (by decide +kernel))
      node_1378
      node_1379
      (invalid_excluded a [6,8,7,0,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,3,8] (by decide +kernel)))

def b_1383 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 4
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_1383 : LosingRegion (edgeOf a b_1383) 0 :=
  losingMask a b_1383 0 2079392365640379800759296
    (by decide +kernel) (by decide +kernel)

theorem node_1383 : Excluded a [6,8,7,0,2,1,4,3,5] :=
  losing_excluded a [6,8,7,0,2,1,4,3,5] (by decide) b_1383 (by decide +kernel) 1 0 2 cert_1383 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1383 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2079392365640379800759296 1 2; decide +kernel)

theorem node_1382 : Excluded a [6,8,7,0,2,1,4,3] :=
  branch_excluded a [6,8,7,0,2,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,3,4] (by decide +kernel))
      node_1383
      (invalid_excluded a [6,8,7,0,2,1,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,3,8] (by decide +kernel)))

theorem node_1384 : Excluded a [6,8,7,0,2,1,4,5] :=
  predecessor_excluded a [6,8,7,0,2,1,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1381 : Excluded a [6,8,7,0,2,1,4] :=
  branch_excluded a [6,8,7,0,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,2] (by decide +kernel))
      node_1382
      (invalid_excluded a [6,8,7,0,2,1,4,4] (by decide +kernel))
      node_1384
      (invalid_excluded a [6,8,7,0,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,4,8] (by decide +kernel)))

theorem node_1386 : Excluded a [6,8,7,0,2,1,5,3] :=
  predecessor_excluded a [6,8,7,0,2,1,5,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_1388 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_1388 : LosingRegion (edgeOf a b_1388) 0 :=
  losingMask a b_1388 0 1399229206301331944383488
    (by decide +kernel) (by decide +kernel)

theorem node_1388 : Excluded a [6,8,7,0,2,1,5,4,3] :=
  losing_excluded a [6,8,7,0,2,1,5,4,3] (by decide) b_1388 (by decide +kernel) 1 0 4 cert_1388 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1388 1 0 ∧ 4 ≠ 1 ∧ maskRegion 1399229206301331944383488 1 4; decide +kernel)

theorem node_1387 : Excluded a [6,8,7,0,2,1,5,4] :=
  branch_excluded a [6,8,7,0,2,1,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,1,5,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,4,2] (by decide +kernel))
      node_1388
      (invalid_excluded a [6,8,7,0,2,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,4,8] (by decide +kernel)))

theorem node_1385 : Excluded a [6,8,7,0,2,1,5] :=
  branch_excluded a [6,8,7,0,2,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,1,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,2] (by decide +kernel))
      node_1386
      node_1387
      (invalid_excluded a [6,8,7,0,2,1,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,5,8] (by decide +kernel)))

theorem node_1376 : Excluded a [6,8,7,0,2,1] :=
  branch_excluded a [6,8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,2] (by decide +kernel))
      node_1377
      node_1381
      node_1385
      (invalid_excluded a [6,8,7,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,1,8] (by decide +kernel)))

theorem node_1389 : Excluded a [6,8,7,0,2,4] :=
  source_excluded a [6,8,7,0,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1375 : Excluded a [6,8,7,0,2] :=
  branch_excluded a [6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,0] (by decide +kernel))
      node_1376
      (invalid_excluded a [6,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3] (by decide +kernel))
      node_1389
      (invalid_excluded a [6,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,8] (by decide +kernel)))

theorem node_1390 : Excluded a [6,8,7,0,3] :=
  source_excluded a [6,8,7,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1373 : Excluded a [6,8,7,0] :=
  branch_excluded a [6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,0] (by decide +kernel))
      node_1374
      node_1375
      node_1390
      (invalid_excluded a [6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,8] (by decide +kernel)))

theorem node_1395 : Excluded a [6,8,7,1,0,2,3,4] :=
  predecessor_excluded a [6,8,7,1,0,2,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_1397 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 3
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_1397 : LosingRegion (edgeOf a b_1397) 0 :=
  losingMask a b_1397 0 1323892703222829306364928
    (by decide +kernel) (by decide +kernel)

theorem node_1397 : Excluded a [6,8,7,1,0,2,3,5,4] :=
  losing_excluded a [6,8,7,1,0,2,3,5,4] (by decide) b_1397 (by decide +kernel) 1 0 5 cert_1397 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1397 1 0 ∧ 5 ≠ 1 ∧ maskRegion 1323892703222829306364928 1 5; decide +kernel)

theorem node_1396 : Excluded a [6,8,7,1,0,2,3,5] :=
  branch_excluded a [6,8,7,1,0,2,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,1,0,2,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,5,3] (by decide +kernel))
      node_1397
      (invalid_excluded a [6,8,7,1,0,2,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,5,8] (by decide +kernel)))

theorem node_1394 : Excluded a [6,8,7,1,0,2,3] :=
  branch_excluded a [6,8,7,1,0,2,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,1,0,2,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,3] (by decide +kernel))
      node_1395
      node_1396
      (invalid_excluded a [6,8,7,1,0,2,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,3,8] (by decide +kernel)))

def b_1400 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 4
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_1400 : LosingRegion (edgeOf a b_1400) 0 :=
  losingMask a b_1400 0 1437888393451583604540416
    (by decide +kernel) (by decide +kernel)

theorem node_1400 : Excluded a [6,8,7,1,0,2,4,3,5] :=
  losing_excluded a [6,8,7,1,0,2,4,3,5] (by decide) b_1400 (by decide +kernel) 1 0 5 cert_1400 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1400 1 0 ∧ 5 ≠ 1 ∧ maskRegion 1437888393451583604540416 1 5; decide +kernel)

theorem node_1399 : Excluded a [6,8,7,1,0,2,4,3] :=
  branch_excluded a [6,8,7,1,0,2,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,1,0,2,4,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,3,4] (by decide +kernel))
      node_1400
      (invalid_excluded a [6,8,7,1,0,2,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,3,8] (by decide +kernel)))

theorem node_1401 : Excluded a [6,8,7,1,0,2,4,5] :=
  predecessor_excluded a [6,8,7,1,0,2,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1398 : Excluded a [6,8,7,1,0,2,4] :=
  branch_excluded a [6,8,7,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,2] (by decide +kernel))
      node_1399
      (invalid_excluded a [6,8,7,1,0,2,4,4] (by decide +kernel))
      node_1401
      (invalid_excluded a [6,8,7,1,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,4,8] (by decide +kernel)))

theorem node_1403 : Excluded a [6,8,7,1,0,2,5,3] :=
  predecessor_excluded a [6,8,7,1,0,2,5,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_1405 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_1405 : LosingRegion (edgeOf a b_1405) 0 :=
  losingMask a b_1405 0 2079245223751881522695168
    (by decide +kernel) (by decide +kernel)

theorem node_1405 : Excluded a [6,8,7,1,0,2,5,4,3] :=
  losing_excluded a [6,8,7,1,0,2,5,4,3] (by decide) b_1405 (by decide +kernel) 1 0 2 cert_1405 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1405 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2079245223751881522695168 1 2; decide +kernel)

theorem node_1404 : Excluded a [6,8,7,1,0,2,5,4] :=
  branch_excluded a [6,8,7,1,0,2,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,1,0,2,5,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,4,2] (by decide +kernel))
      node_1405
      (invalid_excluded a [6,8,7,1,0,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,4,8] (by decide +kernel)))

theorem node_1402 : Excluded a [6,8,7,1,0,2,5] :=
  branch_excluded a [6,8,7,1,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,1,0,2,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,2] (by decide +kernel))
      node_1403
      node_1404
      (invalid_excluded a [6,8,7,1,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,5,8] (by decide +kernel)))

theorem node_1393 : Excluded a [6,8,7,1,0,2] :=
  branch_excluded a [6,8,7,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,2] (by decide +kernel))
      node_1394
      node_1398
      node_1402
      (invalid_excluded a [6,8,7,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,2,8] (by decide +kernel)))

theorem node_1406 : Excluded a [6,8,7,1,0,4] :=
  source_excluded a [6,8,7,1,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1392 : Excluded a [6,8,7,1,0] :=
  branch_excluded a [6,8,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,1] (by decide +kernel))
      node_1393
      (invalid_excluded a [6,8,7,1,0,3] (by decide +kernel))
      node_1406
      (invalid_excluded a [6,8,7,1,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,0,8] (by decide +kernel)))

theorem node_1407 : Excluded a [6,8,7,1,2] :=
  predecessor_excluded a [6,8,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1408 : Excluded a [6,8,7,1,3] :=
  source_excluded a [6,8,7,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1391 : Excluded a [6,8,7,1] :=
  branch_excluded a [6,8,7,1] (by decide)
    (fin9_cases _
      node_1392
      (invalid_excluded a [6,8,7,1,1] (by decide +kernel))
      node_1407
      node_1408
      (invalid_excluded a [6,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,8] (by decide +kernel)))

theorem node_1410 : Excluded a [6,8,7,2,0] :=
  predecessor_excluded a [6,8,7,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1414 : Excluded a [6,8,7,2,1,0,3,4] :=
  predecessor_excluded a [6,8,7,2,1,0,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_1416 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 3
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_1416 : LosingRegion (edgeOf a b_1416) 0 :=
  losingMask a b_1416 0 2079466440567774837218304
    (by decide +kernel) (by decide +kernel)

theorem node_1416 : Excluded a [6,8,7,2,1,0,3,5,4] :=
  losing_excluded a [6,8,7,2,1,0,3,5,4] (by decide) b_1416 (by decide +kernel) 1 0 2 cert_1416 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1416 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2079466440567774837218304 1 2; decide +kernel)

theorem node_1415 : Excluded a [6,8,7,2,1,0,3,5] :=
  branch_excluded a [6,8,7,2,1,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,5,3] (by decide +kernel))
      node_1416
      (invalid_excluded a [6,8,7,2,1,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,5,8] (by decide +kernel)))

theorem node_1413 : Excluded a [6,8,7,2,1,0,3] :=
  branch_excluded a [6,8,7,2,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,3] (by decide +kernel))
      node_1414
      node_1415
      (invalid_excluded a [6,8,7,2,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,3,8] (by decide +kernel)))

def b_1419 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 4
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_1419 : LosingRegion (edgeOf a b_1419) 0 :=
  losingMask a b_1419 0 1437155711837602829046784
    (by decide +kernel) (by decide +kernel)

theorem node_1419 : Excluded a [6,8,7,2,1,0,4,3,5] :=
  losing_excluded a [6,8,7,2,1,0,4,3,5] (by decide) b_1419 (by decide +kernel) 1 0 3 cert_1419 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1419 1 0 ∧ 3 ≠ 1 ∧ maskRegion 1437155711837602829046784 1 3; decide +kernel)

theorem node_1418 : Excluded a [6,8,7,2,1,0,4,3] :=
  branch_excluded a [6,8,7,2,1,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,0,4,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,3,4] (by decide +kernel))
      node_1419
      (invalid_excluded a [6,8,7,2,1,0,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,3,8] (by decide +kernel)))

theorem node_1420 : Excluded a [6,8,7,2,1,0,4,5] :=
  predecessor_excluded a [6,8,7,2,1,0,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1417 : Excluded a [6,8,7,2,1,0,4] :=
  branch_excluded a [6,8,7,2,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,2] (by decide +kernel))
      node_1418
      (invalid_excluded a [6,8,7,2,1,0,4,4] (by decide +kernel))
      node_1420
      (invalid_excluded a [6,8,7,2,1,0,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,4,8] (by decide +kernel)))

theorem node_1422 : Excluded a [6,8,7,2,1,0,5,3] :=
  predecessor_excluded a [6,8,7,2,1,0,5,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_1424 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_1424 : LosingRegion (edgeOf a b_1424) 0 :=
  losingMask a b_1424 0 1400109893936387546158080
    (by decide +kernel) (by decide +kernel)

theorem node_1424 : Excluded a [6,8,7,2,1,0,5,4,3] :=
  losing_excluded a [6,8,7,2,1,0,5,4,3] (by decide) b_1424 (by decide +kernel) 1 0 3 cert_1424 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1424 1 0 ∧ 3 ≠ 1 ∧ maskRegion 1400109893936387546158080 1 3; decide +kernel)

theorem node_1423 : Excluded a [6,8,7,2,1,0,5,4] :=
  branch_excluded a [6,8,7,2,1,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,4,2] (by decide +kernel))
      node_1424
      (invalid_excluded a [6,8,7,2,1,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,4,8] (by decide +kernel)))

theorem node_1421 : Excluded a [6,8,7,2,1,0,5] :=
  branch_excluded a [6,8,7,2,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,2] (by decide +kernel))
      node_1422
      node_1423
      (invalid_excluded a [6,8,7,2,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,5,8] (by decide +kernel)))

theorem node_1412 : Excluded a [6,8,7,2,1,0] :=
  branch_excluded a [6,8,7,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,2] (by decide +kernel))
      node_1413
      node_1417
      node_1421
      (invalid_excluded a [6,8,7,2,1,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,0,8] (by decide +kernel)))

theorem node_1425 : Excluded a [6,8,7,2,1,4] :=
  source_excluded a [6,8,7,2,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1411 : Excluded a [6,8,7,2,1] :=
  branch_excluded a [6,8,7,2,1] (by decide)
    (fin9_cases _
      node_1412
      (invalid_excluded a [6,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3] (by decide +kernel))
      node_1425
      (invalid_excluded a [6,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,8] (by decide +kernel)))

theorem node_1426 : Excluded a [6,8,7,2,3] :=
  source_excluded a [6,8,7,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1409 : Excluded a [6,8,7,2] :=
  branch_excluded a [6,8,7,2] (by decide)
    (fin9_cases _
      node_1410
      node_1411
      (invalid_excluded a [6,8,7,2,2] (by decide +kernel))
      node_1426
      (invalid_excluded a [6,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,8] (by decide +kernel)))

theorem node_1427 : Excluded a [6,8,7,5] :=
  source_excluded a [6,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1372 : Excluded a [6,8,7] :=
  branch_excluded a [6,8,7] (by decide)
    (fin9_cases _
      node_1373
      node_1391
      node_1409
      (invalid_excluded a [6,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,4] (by decide +kernel))
      node_1427
      (invalid_excluded a [6,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,8] (by decide +kernel)))

theorem node_1278 : Excluded a [6,8] :=
  branch_excluded a [6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0] (by decide +kernel))
      node_1279
      (invalid_excluded a [6,8,2] (by decide +kernel))
      node_1280
      node_1312
      node_1338
      (invalid_excluded a [6,8,6] (by decide +kernel))
      node_1372
      (invalid_excluded a [6,8,8] (by decide +kernel)))

theorem node_1086 : Excluded a [6] :=
  branch_excluded a [6] (by decide)
    (fin9_cases _
      node_1087
      (invalid_excluded a [6,1] (by decide +kernel))
      (invalid_excluded a [6,2] (by decide +kernel))
      node_1088
      node_1158
      node_1216
      (invalid_excluded a [6,6] (by decide +kernel))
      node_1277
      node_1278)

theorem node_1429 : Excluded a [7,0] :=
  source_excluded a [7,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_1431 : Excluded a [7,3,1] :=
  source_excluded a [7,3,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1432 : Excluded a [7,3,4] :=
  predecessor_excluded a [7,3,4] 0 4 1 2 (by decide) (by decide +kernel)

theorem node_1434 : Excluded a [7,3,5,0] :=
  predecessor_excluded a [7,3,5,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1436 : Excluded a [7,3,5,1,0] :=
  source_excluded a [7,3,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1437 : Excluded a [7,3,5,1,2] :=
  source_excluded a [7,3,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1439 : Excluded a [7,3,5,1,6,0] :=
  source_excluded a [7,3,5,1,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1440 : Excluded a [7,3,5,1,6,2] :=
  source_excluded a [7,3,5,1,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1441 : Excluded a [7,3,5,1,6,4] :=
  source_excluded a [7,3,5,1,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1443 : Excluded a [7,3,5,1,6,8,0] :=
  source_excluded a [7,3,5,1,6,8,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1445 : Excluded a [7,3,5,1,6,8,2,0] :=
  predecessor_excluded a [7,3,5,1,6,8,2,0] 1 0 6 7 (by decide) (by decide +kernel)

theorem node_1446 : Excluded a [7,3,5,1,6,8,2,4] :=
  predecessor_excluded a [7,3,5,1,6,8,2,4] 0 6 7 4 (by decide) (by decide +kernel)

theorem node_1444 : Excluded a [7,3,5,1,6,8,2] :=
  branch_excluded a [7,3,5,1,6,8,2] (by decide)
    (fin9_cases _
      node_1445
      (invalid_excluded a [7,3,5,1,6,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,2,3] (by decide +kernel))
      node_1446
      (invalid_excluded a [7,3,5,1,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,2,8] (by decide +kernel)))

def b_1449 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 5
  | 3 => 1
  | 4 => 6
  | 5 => 8
  | 6 => 4
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_1449 : LosingRegion (edgeOf a b_1449) 0 :=
  losingMask a b_1449 0 1228999368825829801987072
    (by decide +kernel) (by decide +kernel)

theorem node_1449 : Excluded a [7,3,5,1,6,8,4,0,2] :=
  losing_excluded a [7,3,5,1,6,8,4,0,2] (by decide) b_1449 (by decide +kernel) 1 0 2 cert_1449 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1449 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1228999368825829801987072 1 2; decide +kernel)

theorem node_1448 : Excluded a [7,3,5,1,6,8,4,0] :=
  branch_excluded a [7,3,5,1,6,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,1,6,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,0,1] (by decide +kernel))
      node_1449
      (invalid_excluded a [7,3,5,1,6,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,0,8] (by decide +kernel)))

theorem node_1450 : Excluded a [7,3,5,1,6,8,4,2] :=
  predecessor_excluded a [7,3,5,1,6,8,4,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_1447 : Excluded a [7,3,5,1,6,8,4] :=
  branch_excluded a [7,3,5,1,6,8,4] (by decide)
    (fin9_cases _
      node_1448
      (invalid_excluded a [7,3,5,1,6,8,4,1] (by decide +kernel))
      node_1450
      (invalid_excluded a [7,3,5,1,6,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,4,8] (by decide +kernel)))

theorem node_1442 : Excluded a [7,3,5,1,6,8] :=
  branch_excluded a [7,3,5,1,6,8] (by decide)
    (fin9_cases _
      node_1443
      (invalid_excluded a [7,3,5,1,6,8,1] (by decide +kernel))
      node_1444
      (invalid_excluded a [7,3,5,1,6,8,3] (by decide +kernel))
      node_1447
      (invalid_excluded a [7,3,5,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,8,8] (by decide +kernel)))

theorem node_1438 : Excluded a [7,3,5,1,6] :=
  branch_excluded a [7,3,5,1,6] (by decide)
    (fin9_cases _
      node_1439
      (invalid_excluded a [7,3,5,1,6,1] (by decide +kernel))
      node_1440
      (invalid_excluded a [7,3,5,1,6,3] (by decide +kernel))
      node_1441
      (invalid_excluded a [7,3,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,6,7] (by decide +kernel))
      node_1442)

theorem node_1452 : Excluded a [7,3,5,1,8,0] :=
  source_excluded a [7,3,5,1,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1453 : Excluded a [7,3,5,1,8,2] :=
  source_excluded a [7,3,5,1,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1454 : Excluded a [7,3,5,1,8,4] :=
  source_excluded a [7,3,5,1,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1455 : Excluded a [7,3,5,1,8,6] :=
  predecessor_excluded a [7,3,5,1,8,6] 0 6 4 5 (by decide) (by decide +kernel)

theorem node_1451 : Excluded a [7,3,5,1,8] :=
  branch_excluded a [7,3,5,1,8] (by decide)
    (fin9_cases _
      node_1452
      (invalid_excluded a [7,3,5,1,8,1] (by decide +kernel))
      node_1453
      (invalid_excluded a [7,3,5,1,8,3] (by decide +kernel))
      node_1454
      (invalid_excluded a [7,3,5,1,8,5] (by decide +kernel))
      node_1455
      (invalid_excluded a [7,3,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,8] (by decide +kernel)))

theorem node_1435 : Excluded a [7,3,5,1] :=
  branch_excluded a [7,3,5,1] (by decide)
    (fin9_cases _
      node_1436
      (invalid_excluded a [7,3,5,1,1] (by decide +kernel))
      node_1437
      (invalid_excluded a [7,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,5] (by decide +kernel))
      node_1438
      (invalid_excluded a [7,3,5,1,7] (by decide +kernel))
      node_1451)

theorem node_1456 : Excluded a [7,3,5,2] :=
  source_excluded a [7,3,5,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1458 : Excluded a [7,3,5,6,0] :=
  source_excluded a [7,3,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1459 : Excluded a [7,3,5,6,1] :=
  predecessor_excluded a [7,3,5,6,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1460 : Excluded a [7,3,5,6,2] :=
  source_excluded a [7,3,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1462 : Excluded a [7,3,5,6,8,0] :=
  source_excluded a [7,3,5,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1463 : Excluded a [7,3,5,6,8,1] :=
  source_excluded a [7,3,5,6,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1464 : Excluded a [7,3,5,6,8,2] :=
  source_excluded a [7,3,5,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1465 : Excluded a [7,3,5,6,8,4] :=
  source_excluded a [7,3,5,6,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1461 : Excluded a [7,3,5,6,8] :=
  branch_excluded a [7,3,5,6,8] (by decide)
    (fin9_cases _
      node_1462
      node_1463
      node_1464
      (invalid_excluded a [7,3,5,6,8,3] (by decide +kernel))
      node_1465
      (invalid_excluded a [7,3,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,8] (by decide +kernel)))

theorem node_1457 : Excluded a [7,3,5,6] :=
  branch_excluded a [7,3,5,6] (by decide)
    (fin9_cases _
      node_1458
      node_1459
      node_1460
      (invalid_excluded a [7,3,5,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,7] (by decide +kernel))
      node_1461)

theorem node_1467 : Excluded a [7,3,5,8,0] :=
  source_excluded a [7,3,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1468 : Excluded a [7,3,5,8,1] :=
  predecessor_excluded a [7,3,5,8,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1469 : Excluded a [7,3,5,8,2] :=
  source_excluded a [7,3,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1470 : Excluded a [7,3,5,8,6] :=
  predecessor_excluded a [7,3,5,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_1466 : Excluded a [7,3,5,8] :=
  branch_excluded a [7,3,5,8] (by decide)
    (fin9_cases _
      node_1467
      node_1468
      node_1469
      (invalid_excluded a [7,3,5,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,5] (by decide +kernel))
      node_1470
      (invalid_excluded a [7,3,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,8] (by decide +kernel)))

theorem node_1433 : Excluded a [7,3,5] :=
  branch_excluded a [7,3,5] (by decide)
    (fin9_cases _
      node_1434
      node_1435
      node_1456
      (invalid_excluded a [7,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,5] (by decide +kernel))
      node_1457
      (invalid_excluded a [7,3,5,7] (by decide +kernel))
      node_1466)

theorem node_1471 : Excluded a [7,3,6] :=
  predecessor_excluded a [7,3,6] 1 7 2 0 (by decide) (by decide +kernel)

theorem node_1473 : Excluded a [7,3,8,0] :=
  predecessor_excluded a [7,3,8,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1476 : Excluded a [7,3,8,1,0,2] :=
  source_excluded a [7,3,8,1,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1477 : Excluded a [7,3,8,1,0,4] :=
  source_excluded a [7,3,8,1,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1479 : Excluded a [7,3,8,1,0,6,2] :=
  predecessor_excluded a [7,3,8,1,0,6,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1480 : Excluded a [7,3,8,1,0,6,4] :=
  predecessor_excluded a [7,3,8,1,0,6,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1482 : Excluded a [7,3,8,1,0,6,5,2] :=
  source_excluded a [7,3,8,1,0,6,5,2] 7 0 2 (by decide) (by decide +kernel)

def b_1484 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 8
  | 3 => 1
  | 4 => 0
  | 5 => 6
  | 6 => 5
  | 7 => 4
  | 8 => 2
  | _ => 0

def cert_1484 : LosingRegion (edgeOf a b_1484) 0 :=
  losingMask a b_1484 0 1238516326128344024220672
    (by decide +kernel) (by decide +kernel)

theorem node_1484 : Excluded a [7,3,8,1,0,6,5,4,2] :=
  losing_excluded a [7,3,8,1,0,6,5,4,2] (by decide) b_1484 (by decide +kernel) 5 0 1 cert_1484 (by change 5 ≠ 0 ∧ ¬ edgeOf a b_1484 5 0 ∧ 1 ≠ 5 ∧ maskRegion 1238516326128344024220672 5 1; decide +kernel)

theorem node_1483 : Excluded a [7,3,8,1,0,6,5,4] :=
  branch_excluded a [7,3,8,1,0,6,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,6,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,4,1] (by decide +kernel))
      node_1484
      (invalid_excluded a [7,3,8,1,0,6,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,4,8] (by decide +kernel)))

theorem node_1481 : Excluded a [7,3,8,1,0,6,5] :=
  branch_excluded a [7,3,8,1,0,6,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,6,5,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,1] (by decide +kernel))
      node_1482
      (invalid_excluded a [7,3,8,1,0,6,5,3] (by decide +kernel))
      node_1483
      (invalid_excluded a [7,3,8,1,0,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,5,8] (by decide +kernel)))

theorem node_1478 : Excluded a [7,3,8,1,0,6] :=
  branch_excluded a [7,3,8,1,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,6,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,1] (by decide +kernel))
      node_1479
      (invalid_excluded a [7,3,8,1,0,6,3] (by decide +kernel))
      node_1480
      node_1481
      (invalid_excluded a [7,3,8,1,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6,8] (by decide +kernel)))

theorem node_1475 : Excluded a [7,3,8,1,0] :=
  branch_excluded a [7,3,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,1] (by decide +kernel))
      node_1476
      (invalid_excluded a [7,3,8,1,0,3] (by decide +kernel))
      node_1477
      (invalid_excluded a [7,3,8,1,0,5] (by decide +kernel))
      node_1478
      (invalid_excluded a [7,3,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,8] (by decide +kernel)))

theorem node_1485 : Excluded a [7,3,8,1,2] :=
  predecessor_excluded a [7,3,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1487 : Excluded a [7,3,8,1,6,0] :=
  predecessor_excluded a [7,3,8,1,6,0] 2 1 5 3 (by decide) (by decide +kernel)

theorem node_1488 : Excluded a [7,3,8,1,6,2] :=
  source_excluded a [7,3,8,1,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1489 : Excluded a [7,3,8,1,6,4] :=
  source_excluded a [7,3,8,1,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1486 : Excluded a [7,3,8,1,6] :=
  branch_excluded a [7,3,8,1,6] (by decide)
    (fin9_cases _
      node_1487
      (invalid_excluded a [7,3,8,1,6,1] (by decide +kernel))
      node_1488
      (invalid_excluded a [7,3,8,1,6,3] (by decide +kernel))
      node_1489
      (invalid_excluded a [7,3,8,1,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,6,8] (by decide +kernel)))

theorem node_1474 : Excluded a [7,3,8,1] :=
  branch_excluded a [7,3,8,1] (by decide)
    (fin9_cases _
      node_1475
      (invalid_excluded a [7,3,8,1,1] (by decide +kernel))
      node_1485
      (invalid_excluded a [7,3,8,1,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,5] (by decide +kernel))
      node_1486
      (invalid_excluded a [7,3,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,8] (by decide +kernel)))

theorem node_1490 : Excluded a [7,3,8,2] :=
  source_excluded a [7,3,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1491 : Excluded a [7,3,8,5] :=
  source_excluded a [7,3,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1494 : Excluded a [7,3,8,6,0,1] :=
  source_excluded a [7,3,8,6,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1495 : Excluded a [7,3,8,6,0,2] :=
  source_excluded a [7,3,8,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1496 : Excluded a [7,3,8,6,0,4] :=
  source_excluded a [7,3,8,6,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1493 : Excluded a [7,3,8,6,0] :=
  branch_excluded a [7,3,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,0] (by decide +kernel))
      node_1494
      node_1495
      (invalid_excluded a [7,3,8,6,0,3] (by decide +kernel))
      node_1496
      (invalid_excluded a [7,3,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,8] (by decide +kernel)))

theorem node_1497 : Excluded a [7,3,8,6,1] :=
  predecessor_excluded a [7,3,8,6,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1499 : Excluded a [7,3,8,6,2,0] :=
  predecessor_excluded a [7,3,8,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1500 : Excluded a [7,3,8,6,2,1] :=
  source_excluded a [7,3,8,6,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1501 : Excluded a [7,3,8,6,2,4] :=
  source_excluded a [7,3,8,6,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1498 : Excluded a [7,3,8,6,2] :=
  branch_excluded a [7,3,8,6,2] (by decide)
    (fin9_cases _
      node_1499
      node_1500
      (invalid_excluded a [7,3,8,6,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,3] (by decide +kernel))
      node_1501
      (invalid_excluded a [7,3,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,8] (by decide +kernel)))

theorem node_1492 : Excluded a [7,3,8,6] :=
  branch_excluded a [7,3,8,6] (by decide)
    (fin9_cases _
      node_1493
      node_1497
      node_1498
      (invalid_excluded a [7,3,8,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,8] (by decide +kernel)))

theorem node_1472 : Excluded a [7,3,8] :=
  branch_excluded a [7,3,8] (by decide)
    (fin9_cases _
      node_1473
      node_1474
      node_1490
      (invalid_excluded a [7,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,4] (by decide +kernel))
      node_1491
      node_1492
      (invalid_excluded a [7,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,8] (by decide +kernel)))

theorem node_1430 : Excluded a [7,3] :=
  branch_excluded a [7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,0] (by decide +kernel))
      node_1431
      (invalid_excluded a [7,3,2] (by decide +kernel))
      (invalid_excluded a [7,3,3] (by decide +kernel))
      node_1432
      node_1433
      node_1471
      (invalid_excluded a [7,3,7] (by decide +kernel))
      node_1472)

theorem node_1503 : Excluded a [7,4,1] :=
  source_excluded a [7,4,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1505 : Excluded a [7,4,3,0] :=
  source_excluded a [7,4,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1506 : Excluded a [7,4,3,1] :=
  source_excluded a [7,4,3,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1507 : Excluded a [7,4,3,2] :=
  source_excluded a [7,4,3,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1508 : Excluded a [7,4,3,5] :=
  source_excluded a [7,4,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1510 : Excluded a [7,4,3,6,0] :=
  predecessor_excluded a [7,4,3,6,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1512 : Excluded a [7,4,3,6,1,0] :=
  source_excluded a [7,4,3,6,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1513 : Excluded a [7,4,3,6,1,2] :=
  source_excluded a [7,4,3,6,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1514 : Excluded a [7,4,3,6,1,8] :=
  predecessor_excluded a [7,4,3,6,1,8] 0 6 5 3 (by decide) (by decide +kernel)

theorem node_1511 : Excluded a [7,4,3,6,1] :=
  branch_excluded a [7,4,3,6,1] (by decide)
    (fin9_cases _
      node_1512
      (invalid_excluded a [7,4,3,6,1,1] (by decide +kernel))
      node_1513
      (invalid_excluded a [7,4,3,6,1,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,7] (by decide +kernel))
      node_1514)

theorem node_1515 : Excluded a [7,4,3,6,2] :=
  source_excluded a [7,4,3,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1517 : Excluded a [7,4,3,6,8,0] :=
  source_excluded a [7,4,3,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1518 : Excluded a [7,4,3,6,8,1] :=
  predecessor_excluded a [7,4,3,6,8,1] 0 4 5 1 (by decide) (by decide +kernel)

theorem node_1519 : Excluded a [7,4,3,6,8,2] :=
  source_excluded a [7,4,3,6,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1516 : Excluded a [7,4,3,6,8] :=
  branch_excluded a [7,4,3,6,8] (by decide)
    (fin9_cases _
      node_1517
      node_1518
      node_1519
      (invalid_excluded a [7,4,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,8] (by decide +kernel)))

theorem node_1509 : Excluded a [7,4,3,6] :=
  branch_excluded a [7,4,3,6] (by decide)
    (fin9_cases _
      node_1510
      node_1511
      node_1515
      (invalid_excluded a [7,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,7] (by decide +kernel))
      node_1516)

theorem node_1521 : Excluded a [7,4,3,8,0] :=
  predecessor_excluded a [7,4,3,8,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1523 : Excluded a [7,4,3,8,1,0] :=
  source_excluded a [7,4,3,8,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1524 : Excluded a [7,4,3,8,1,2] :=
  source_excluded a [7,4,3,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1526 : Excluded a [7,4,3,8,1,6,0] :=
  source_excluded a [7,4,3,8,1,6,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1528 : Excluded a [7,4,3,8,1,6,2,0] :=
  predecessor_excluded a [7,4,3,8,1,6,2,0] 1 0 6 7 (by decide) (by decide +kernel)

theorem node_1529 : Excluded a [7,4,3,8,1,6,2,5] :=
  predecessor_excluded a [7,4,3,8,1,6,2,5] 0 6 7 5 (by decide) (by decide +kernel)

theorem node_1527 : Excluded a [7,4,3,8,1,6,2] :=
  branch_excluded a [7,4,3,8,1,6,2] (by decide)
    (fin9_cases _
      node_1528
      (invalid_excluded a [7,4,3,8,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,2,4] (by decide +kernel))
      node_1529
      (invalid_excluded a [7,4,3,8,1,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,2,8] (by decide +kernel)))

def b_1532 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 4
  | 2 => 3
  | 3 => 8
  | 4 => 1
  | 5 => 6
  | 6 => 5
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_1532 : LosingRegion (edgeOf a b_1532) 0 :=
  losingMask a b_1532 0 1228999371038729962654720
    (by decide +kernel) (by decide +kernel)

theorem node_1532 : Excluded a [7,4,3,8,1,6,5,0,2] :=
  losing_excluded a [7,4,3,8,1,6,5,0,2] (by decide) b_1532 (by decide +kernel) 1 0 2 cert_1532 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1532 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1228999371038729962654720 1 2; decide +kernel)

theorem node_1531 : Excluded a [7,4,3,8,1,6,5,0] :=
  branch_excluded a [7,4,3,8,1,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,3,8,1,6,5,0,0] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,0,1] (by decide +kernel))
      node_1532
      (invalid_excluded a [7,4,3,8,1,6,5,0,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,0,8] (by decide +kernel)))

theorem node_1533 : Excluded a [7,4,3,8,1,6,5,2] :=
  predecessor_excluded a [7,4,3,8,1,6,5,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_1530 : Excluded a [7,4,3,8,1,6,5] :=
  branch_excluded a [7,4,3,8,1,6,5] (by decide)
    (fin9_cases _
      node_1531
      (invalid_excluded a [7,4,3,8,1,6,5,1] (by decide +kernel))
      node_1533
      (invalid_excluded a [7,4,3,8,1,6,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,5,8] (by decide +kernel)))

theorem node_1525 : Excluded a [7,4,3,8,1,6] :=
  branch_excluded a [7,4,3,8,1,6] (by decide)
    (fin9_cases _
      node_1526
      (invalid_excluded a [7,4,3,8,1,6,1] (by decide +kernel))
      node_1527
      (invalid_excluded a [7,4,3,8,1,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,4] (by decide +kernel))
      node_1530
      (invalid_excluded a [7,4,3,8,1,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6,8] (by decide +kernel)))

theorem node_1522 : Excluded a [7,4,3,8,1] :=
  branch_excluded a [7,4,3,8,1] (by decide)
    (fin9_cases _
      node_1523
      (invalid_excluded a [7,4,3,8,1,1] (by decide +kernel))
      node_1524
      (invalid_excluded a [7,4,3,8,1,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,5] (by decide +kernel))
      node_1525
      (invalid_excluded a [7,4,3,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,8] (by decide +kernel)))

theorem node_1534 : Excluded a [7,4,3,8,2] :=
  source_excluded a [7,4,3,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1535 : Excluded a [7,4,3,8,6] :=
  predecessor_excluded a [7,4,3,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_1520 : Excluded a [7,4,3,8] :=
  branch_excluded a [7,4,3,8] (by decide)
    (fin9_cases _
      node_1521
      node_1522
      node_1534
      (invalid_excluded a [7,4,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,5] (by decide +kernel))
      node_1535
      (invalid_excluded a [7,4,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,8] (by decide +kernel)))

theorem node_1504 : Excluded a [7,4,3] :=
  branch_excluded a [7,4,3] (by decide)
    (fin9_cases _
      node_1505
      node_1506
      node_1507
      (invalid_excluded a [7,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,4] (by decide +kernel))
      node_1508
      node_1509
      (invalid_excluded a [7,4,3,7] (by decide +kernel))
      node_1520)

theorem node_1536 : Excluded a [7,4,5] :=
  predecessor_excluded a [7,4,5] 0 5 1 2 (by decide) (by decide +kernel)

theorem node_1537 : Excluded a [7,4,6] :=
  predecessor_excluded a [7,4,6] 1 7 2 0 (by decide) (by decide +kernel)

theorem node_1540 : Excluded a [7,4,8,0,1] :=
  predecessor_excluded a [7,4,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1541 : Excluded a [7,4,8,0,2] :=
  source_excluded a [7,4,8,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1542 : Excluded a [7,4,8,0,3] :=
  source_excluded a [7,4,8,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1544 : Excluded a [7,4,8,0,6,1] :=
  predecessor_excluded a [7,4,8,0,6,1] 0 4 5 1 (by decide) (by decide +kernel)

theorem node_1545 : Excluded a [7,4,8,0,6,2] :=
  predecessor_excluded a [7,4,8,0,6,2] 1 0 5 3 (by decide) (by decide +kernel)

theorem node_1543 : Excluded a [7,4,8,0,6] :=
  branch_excluded a [7,4,8,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,0,6,0] (by decide +kernel))
      node_1544
      node_1545
      (invalid_excluded a [7,4,8,0,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,6,8] (by decide +kernel)))

theorem node_1539 : Excluded a [7,4,8,0] :=
  branch_excluded a [7,4,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,0,0] (by decide +kernel))
      node_1540
      node_1541
      node_1542
      (invalid_excluded a [7,4,8,0,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,5] (by decide +kernel))
      node_1543
      (invalid_excluded a [7,4,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,8] (by decide +kernel)))

theorem node_1546 : Excluded a [7,4,8,1] :=
  source_excluded a [7,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1547 : Excluded a [7,4,8,2] :=
  source_excluded a [7,4,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1548 : Excluded a [7,4,8,5] :=
  source_excluded a [7,4,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1550 : Excluded a [7,4,8,6,0] :=
  predecessor_excluded a [7,4,8,6,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1553 : Excluded a [7,4,8,6,1,0,2] :=
  predecessor_excluded a [7,4,8,6,1,0,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1555 : Excluded a [7,4,8,6,1,0,3,2] :=
  source_excluded a [7,4,8,6,1,0,3,2] 7 0 2 (by decide) (by decide +kernel)

def b_1557 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 4
  | 2 => 8
  | 3 => 6
  | 4 => 1
  | 5 => 0
  | 6 => 3
  | 7 => 5
  | 8 => 2
  | _ => 0

def cert_1557 : LosingRegion (edgeOf a b_1557) 0 :=
  losingMask a b_1557 0 1238589824522421405746176
    (by decide +kernel) (by decide +kernel)

theorem node_1557 : Excluded a [7,4,8,6,1,0,3,5,2] :=
  losing_excluded a [7,4,8,6,1,0,3,5,2] (by decide) b_1557 (by decide +kernel) 3 0 1 cert_1557 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1557 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1238589824522421405746176 3 1; decide +kernel)

theorem node_1556 : Excluded a [7,4,8,6,1,0,3,5] :=
  branch_excluded a [7,4,8,6,1,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,6,1,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,5,1] (by decide +kernel))
      node_1557
      (invalid_excluded a [7,4,8,6,1,0,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,5,8] (by decide +kernel)))

theorem node_1554 : Excluded a [7,4,8,6,1,0,3] :=
  branch_excluded a [7,4,8,6,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,6,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,1] (by decide +kernel))
      node_1555
      (invalid_excluded a [7,4,8,6,1,0,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,4] (by decide +kernel))
      node_1556
      (invalid_excluded a [7,4,8,6,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,3,8] (by decide +kernel)))

theorem node_1558 : Excluded a [7,4,8,6,1,0,5] :=
  predecessor_excluded a [7,4,8,6,1,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1552 : Excluded a [7,4,8,6,1,0] :=
  branch_excluded a [7,4,8,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,1] (by decide +kernel))
      node_1553
      node_1554
      (invalid_excluded a [7,4,8,6,1,0,4] (by decide +kernel))
      node_1558
      (invalid_excluded a [7,4,8,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,0,8] (by decide +kernel)))

theorem node_1559 : Excluded a [7,4,8,6,1,2] :=
  predecessor_excluded a [7,4,8,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1551 : Excluded a [7,4,8,6,1] :=
  branch_excluded a [7,4,8,6,1] (by decide)
    (fin9_cases _
      node_1552
      (invalid_excluded a [7,4,8,6,1,1] (by decide +kernel))
      node_1559
      (invalid_excluded a [7,4,8,6,1,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,8] (by decide +kernel)))

theorem node_1560 : Excluded a [7,4,8,6,2] :=
  source_excluded a [7,4,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1561 : Excluded a [7,4,8,6,3] :=
  source_excluded a [7,4,8,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1549 : Excluded a [7,4,8,6] :=
  branch_excluded a [7,4,8,6] (by decide)
    (fin9_cases _
      node_1550
      node_1551
      node_1560
      node_1561
      (invalid_excluded a [7,4,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,8] (by decide +kernel)))

theorem node_1538 : Excluded a [7,4,8] :=
  branch_excluded a [7,4,8] (by decide)
    (fin9_cases _
      node_1539
      node_1546
      node_1547
      (invalid_excluded a [7,4,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,4] (by decide +kernel))
      node_1548
      node_1549
      (invalid_excluded a [7,4,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,8] (by decide +kernel)))

theorem node_1502 : Excluded a [7,4] :=
  branch_excluded a [7,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0] (by decide +kernel))
      node_1503
      (invalid_excluded a [7,4,2] (by decide +kernel))
      node_1504
      (invalid_excluded a [7,4,4] (by decide +kernel))
      node_1536
      node_1537
      (invalid_excluded a [7,4,7] (by decide +kernel))
      node_1538)

theorem node_1563 : Excluded a [7,5,1] :=
  source_excluded a [7,5,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1564 : Excluded a [7,5,3] :=
  predecessor_excluded a [7,5,3] 0 3 1 2 (by decide) (by decide +kernel)

theorem node_1566 : Excluded a [7,5,4,0] :=
  source_excluded a [7,5,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1567 : Excluded a [7,5,4,1] :=
  predecessor_excluded a [7,5,4,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1568 : Excluded a [7,5,4,2] :=
  source_excluded a [7,5,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_1570 : Excluded a [7,5,4,6,0] :=
  source_excluded a [7,5,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1571 : Excluded a [7,5,4,6,1] :=
  source_excluded a [7,5,4,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1572 : Excluded a [7,5,4,6,2] :=
  source_excluded a [7,5,4,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1573 : Excluded a [7,5,4,6,3] :=
  source_excluded a [7,5,4,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1575 : Excluded a [7,5,4,6,8,0] :=
  predecessor_excluded a [7,5,4,6,8,0] 3 0 1 5 (by decide) (by decide +kernel)

theorem node_1577 : Excluded a [7,5,4,6,8,1,0] :=
  source_excluded a [7,5,4,6,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1579 : Excluded a [7,5,4,6,8,1,2,0] :=
  predecessor_excluded a [7,5,4,6,8,1,2,0] 1 0 6 7 (by decide) (by decide +kernel)

theorem node_1580 : Excluded a [7,5,4,6,8,1,2,3] :=
  predecessor_excluded a [7,5,4,6,8,1,2,3] 0 6 7 3 (by decide) (by decide +kernel)

theorem node_1578 : Excluded a [7,5,4,6,8,1,2] :=
  branch_excluded a [7,5,4,6,8,1,2] (by decide)
    (fin9_cases _
      node_1579
      (invalid_excluded a [7,5,4,6,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,2,2] (by decide +kernel))
      node_1580
      (invalid_excluded a [7,5,4,6,8,1,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,2,8] (by decide +kernel)))

def b_1583 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 5
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 1
  | 6 => 3
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_1583 : LosingRegion (edgeOf a b_1583) 0 :=
  losingMask a b_1583 0 1228999369419638826994688
    (by decide +kernel) (by decide +kernel)

theorem node_1583 : Excluded a [7,5,4,6,8,1,3,0,2] :=
  losing_excluded a [7,5,4,6,8,1,3,0,2] (by decide) b_1583 (by decide +kernel) 1 0 2 cert_1583 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1583 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1228999369419638826994688 1 2; decide +kernel)

theorem node_1582 : Excluded a [7,5,4,6,8,1,3,0] :=
  branch_excluded a [7,5,4,6,8,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,4,6,8,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,1] (by decide +kernel))
      node_1583
      (invalid_excluded a [7,5,4,6,8,1,3,0,3] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,8] (by decide +kernel)))

theorem node_1584 : Excluded a [7,5,4,6,8,1,3,2] :=
  predecessor_excluded a [7,5,4,6,8,1,3,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_1581 : Excluded a [7,5,4,6,8,1,3] :=
  branch_excluded a [7,5,4,6,8,1,3] (by decide)
    (fin9_cases _
      node_1582
      (invalid_excluded a [7,5,4,6,8,1,3,1] (by decide +kernel))
      node_1584
      (invalid_excluded a [7,5,4,6,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,8] (by decide +kernel)))

theorem node_1576 : Excluded a [7,5,4,6,8,1] :=
  branch_excluded a [7,5,4,6,8,1] (by decide)
    (fin9_cases _
      node_1577
      (invalid_excluded a [7,5,4,6,8,1,1] (by decide +kernel))
      node_1578
      node_1581
      (invalid_excluded a [7,5,4,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,8] (by decide +kernel)))

theorem node_1585 : Excluded a [7,5,4,6,8,2] :=
  source_excluded a [7,5,4,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1574 : Excluded a [7,5,4,6,8] :=
  branch_excluded a [7,5,4,6,8] (by decide)
    (fin9_cases _
      node_1575
      node_1576
      node_1585
      (invalid_excluded a [7,5,4,6,8,3] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,8] (by decide +kernel)))

theorem node_1569 : Excluded a [7,5,4,6] :=
  branch_excluded a [7,5,4,6] (by decide)
    (fin9_cases _
      node_1570
      node_1571
      node_1572
      node_1573
      (invalid_excluded a [7,5,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,7] (by decide +kernel))
      node_1574)

theorem node_1587 : Excluded a [7,5,4,8,0] :=
  source_excluded a [7,5,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1588 : Excluded a [7,5,4,8,1] :=
  source_excluded a [7,5,4,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1589 : Excluded a [7,5,4,8,2] :=
  source_excluded a [7,5,4,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1590 : Excluded a [7,5,4,8,3] :=
  source_excluded a [7,5,4,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1591 : Excluded a [7,5,4,8,6] :=
  predecessor_excluded a [7,5,4,8,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_1586 : Excluded a [7,5,4,8] :=
  branch_excluded a [7,5,4,8] (by decide)
    (fin9_cases _
      node_1587
      node_1588
      node_1589
      node_1590
      (invalid_excluded a [7,5,4,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,8,5] (by decide +kernel))
      node_1591
      (invalid_excluded a [7,5,4,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,8,8] (by decide +kernel)))

theorem node_1565 : Excluded a [7,5,4] :=
  branch_excluded a [7,5,4] (by decide)
    (fin9_cases _
      node_1566
      node_1567
      node_1568
      (invalid_excluded a [7,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,5] (by decide +kernel))
      node_1569
      (invalid_excluded a [7,5,4,7] (by decide +kernel))
      node_1586)

theorem node_1592 : Excluded a [7,5,6] :=
  predecessor_excluded a [7,5,6] 1 7 2 0 (by decide) (by decide +kernel)

theorem node_1595 : Excluded a [7,5,8,0,1] :=
  source_excluded a [7,5,8,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1596 : Excluded a [7,5,8,0,2] :=
  source_excluded a [7,5,8,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1597 : Excluded a [7,5,8,0,3] :=
  source_excluded a [7,5,8,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1600 : Excluded a [7,5,8,0,6,1,2] :=
  predecessor_excluded a [7,5,8,0,6,1,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1601 : Excluded a [7,5,8,0,6,1,3] :=
  predecessor_excluded a [7,5,8,0,6,1,3] 0 3 4 6 (by decide) (by decide +kernel)

theorem node_1603 : Excluded a [7,5,8,0,6,1,4,2] :=
  source_excluded a [7,5,8,0,6,1,4,2] 7 0 2 (by decide) (by decide +kernel)

def b_1605 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 5
  | 2 => 8
  | 3 => 0
  | 4 => 6
  | 5 => 1
  | 6 => 4
  | 7 => 3
  | 8 => 2
  | _ => 0

def cert_1605 : LosingRegion (edgeOf a b_1605) 0 :=
  losingMask a b_1605 0 1238737830822909356016640
    (by decide +kernel) (by decide +kernel)

theorem node_1605 : Excluded a [7,5,8,0,6,1,4,3,2] :=
  losing_excluded a [7,5,8,0,6,1,4,3,2] (by decide) b_1605 (by decide +kernel) 4 0 1 cert_1605 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1605 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1238737830822909356016640 4 1; decide +kernel)

theorem node_1604 : Excluded a [7,5,8,0,6,1,4,3] :=
  branch_excluded a [7,5,8,0,6,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,6,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,3,1] (by decide +kernel))
      node_1605
      (invalid_excluded a [7,5,8,0,6,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,3,8] (by decide +kernel)))

theorem node_1602 : Excluded a [7,5,8,0,6,1,4] :=
  branch_excluded a [7,5,8,0,6,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,6,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,1] (by decide +kernel))
      node_1603
      node_1604
      (invalid_excluded a [7,5,8,0,6,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,4,8] (by decide +kernel)))

theorem node_1599 : Excluded a [7,5,8,0,6,1] :=
  branch_excluded a [7,5,8,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,1] (by decide +kernel))
      node_1600
      node_1601
      node_1602
      (invalid_excluded a [7,5,8,0,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,1,8] (by decide +kernel)))

theorem node_1606 : Excluded a [7,5,8,0,6,2] :=
  source_excluded a [7,5,8,0,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1607 : Excluded a [7,5,8,0,6,4] :=
  source_excluded a [7,5,8,0,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1598 : Excluded a [7,5,8,0,6] :=
  branch_excluded a [7,5,8,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,6,0] (by decide +kernel))
      node_1599
      node_1606
      (invalid_excluded a [7,5,8,0,6,3] (by decide +kernel))
      node_1607
      (invalid_excluded a [7,5,8,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,8] (by decide +kernel)))

theorem node_1594 : Excluded a [7,5,8,0] :=
  branch_excluded a [7,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,0] (by decide +kernel))
      node_1595
      node_1596
      node_1597
      (invalid_excluded a [7,5,8,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,5] (by decide +kernel))
      node_1598
      (invalid_excluded a [7,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,8] (by decide +kernel)))

theorem node_1608 : Excluded a [7,5,8,1] :=
  predecessor_excluded a [7,5,8,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1610 : Excluded a [7,5,8,2,0] :=
  predecessor_excluded a [7,5,8,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1611 : Excluded a [7,5,8,2,1] :=
  source_excluded a [7,5,8,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1612 : Excluded a [7,5,8,2,3] :=
  source_excluded a [7,5,8,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1614 : Excluded a [7,5,8,2,6,0] :=
  predecessor_excluded a [7,5,8,2,6,0] 3 0 1 5 (by decide) (by decide +kernel)

theorem node_1615 : Excluded a [7,5,8,2,6,1] :=
  predecessor_excluded a [7,5,8,2,6,1] 0 2 5 3 (by decide) (by decide +kernel)

theorem node_1616 : Excluded a [7,5,8,2,6,4] :=
  source_excluded a [7,5,8,2,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1613 : Excluded a [7,5,8,2,6] :=
  branch_excluded a [7,5,8,2,6] (by decide)
    (fin9_cases _
      node_1614
      node_1615
      (invalid_excluded a [7,5,8,2,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,6,3] (by decide +kernel))
      node_1616
      (invalid_excluded a [7,5,8,2,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,6,8] (by decide +kernel)))

theorem node_1609 : Excluded a [7,5,8,2] :=
  branch_excluded a [7,5,8,2] (by decide)
    (fin9_cases _
      node_1610
      node_1611
      (invalid_excluded a [7,5,8,2,2] (by decide +kernel))
      node_1612
      (invalid_excluded a [7,5,8,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,5] (by decide +kernel))
      node_1613
      (invalid_excluded a [7,5,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,8] (by decide +kernel)))

theorem node_1619 : Excluded a [7,5,8,6,0,1] :=
  predecessor_excluded a [7,5,8,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1620 : Excluded a [7,5,8,6,0,2] :=
  source_excluded a [7,5,8,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1621 : Excluded a [7,5,8,6,0,4] :=
  source_excluded a [7,5,8,6,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1618 : Excluded a [7,5,8,6,0] :=
  branch_excluded a [7,5,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,6,0,0] (by decide +kernel))
      node_1619
      node_1620
      (invalid_excluded a [7,5,8,6,0,3] (by decide +kernel))
      node_1621
      (invalid_excluded a [7,5,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,8] (by decide +kernel)))

theorem node_1622 : Excluded a [7,5,8,6,1] :=
  source_excluded a [7,5,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1623 : Excluded a [7,5,8,6,2] :=
  source_excluded a [7,5,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1624 : Excluded a [7,5,8,6,3] :=
  source_excluded a [7,5,8,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1617 : Excluded a [7,5,8,6] :=
  branch_excluded a [7,5,8,6] (by decide)
    (fin9_cases _
      node_1618
      node_1622
      node_1623
      node_1624
      (invalid_excluded a [7,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,8] (by decide +kernel)))

theorem node_1593 : Excluded a [7,5,8] :=
  branch_excluded a [7,5,8] (by decide)
    (fin9_cases _
      node_1594
      node_1608
      node_1609
      (invalid_excluded a [7,5,8,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,5] (by decide +kernel))
      node_1617
      (invalid_excluded a [7,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,8] (by decide +kernel)))

theorem node_1562 : Excluded a [7,5] :=
  branch_excluded a [7,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0] (by decide +kernel))
      node_1563
      (invalid_excluded a [7,5,2] (by decide +kernel))
      node_1564
      node_1565
      (invalid_excluded a [7,5,5] (by decide +kernel))
      node_1592
      (invalid_excluded a [7,5,7] (by decide +kernel))
      node_1593)

theorem node_1626 : Excluded a [7,6,1] :=
  source_excluded a [7,6,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1628 : Excluded a [7,6,3,0] :=
  source_excluded a [7,6,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1629 : Excluded a [7,6,3,1] :=
  predecessor_excluded a [7,6,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_1631 : Excluded a [7,6,3,2,0] :=
  predecessor_excluded a [7,6,3,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1633 : Excluded a [7,6,3,2,1,0] :=
  source_excluded a [7,6,3,2,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1634 : Excluded a [7,6,3,2,1,4] :=
  source_excluded a [7,6,3,2,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1636 : Excluded a [7,6,3,2,1,8,0] :=
  source_excluded a [7,6,3,2,1,8,0] 6 1 0 (by decide) (by decide +kernel)

def b_1639 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 8
  | 6 => 4
  | 7 => 0
  | 8 => 5
  | _ => 0

def cert_1639 : LosingRegion (edgeOf a b_1639) 0 :=
  losingMask a b_1639 0 2149860820324065939033088
    (by decide +kernel) (by decide +kernel)

theorem node_1639 : Excluded a [7,6,3,2,1,8,4,0,5] :=
  losing_excluded a [7,6,3,2,1,8,4,0,5] (by decide) b_1639 (by decide +kernel) 1 0 2 cert_1639 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1639 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2149860820324065939033088 1 2; decide +kernel)

theorem node_1638 : Excluded a [7,6,3,2,1,8,4,0] :=
  branch_excluded a [7,6,3,2,1,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,3,2,1,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,0,1] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,0,4] (by decide +kernel))
      node_1639
      (invalid_excluded a [7,6,3,2,1,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,0,8] (by decide +kernel)))

theorem node_1640 : Excluded a [7,6,3,2,1,8,4,5] :=
  source_excluded a [7,6,3,2,1,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_1637 : Excluded a [7,6,3,2,1,8,4] :=
  branch_excluded a [7,6,3,2,1,8,4] (by decide)
    (fin9_cases _
      node_1638
      (invalid_excluded a [7,6,3,2,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,4] (by decide +kernel))
      node_1640
      (invalid_excluded a [7,6,3,2,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,4,8] (by decide +kernel)))

theorem node_1641 : Excluded a [7,6,3,2,1,8,5] :=
  predecessor_excluded a [7,6,3,2,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1635 : Excluded a [7,6,3,2,1,8] :=
  branch_excluded a [7,6,3,2,1,8] (by decide)
    (fin9_cases _
      node_1636
      (invalid_excluded a [7,6,3,2,1,8,1] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,3] (by decide +kernel))
      node_1637
      node_1641
      (invalid_excluded a [7,6,3,2,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,8,8] (by decide +kernel)))

theorem node_1632 : Excluded a [7,6,3,2,1] :=
  branch_excluded a [7,6,3,2,1] (by decide)
    (fin9_cases _
      node_1633
      (invalid_excluded a [7,6,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,3] (by decide +kernel))
      node_1634
      (invalid_excluded a [7,6,3,2,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,1,7] (by decide +kernel))
      node_1635)

theorem node_1643 : Excluded a [7,6,3,2,8,0] :=
  source_excluded a [7,6,3,2,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1644 : Excluded a [7,6,3,2,8,1] :=
  predecessor_excluded a [7,6,3,2,8,1] 0 2 5 3 (by decide) (by decide +kernel)

theorem node_1645 : Excluded a [7,6,3,2,8,4] :=
  source_excluded a [7,6,3,2,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1642 : Excluded a [7,6,3,2,8] :=
  branch_excluded a [7,6,3,2,8] (by decide)
    (fin9_cases _
      node_1643
      node_1644
      (invalid_excluded a [7,6,3,2,8,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,3] (by decide +kernel))
      node_1645
      (invalid_excluded a [7,6,3,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,8] (by decide +kernel)))

theorem node_1630 : Excluded a [7,6,3,2] :=
  branch_excluded a [7,6,3,2] (by decide)
    (fin9_cases _
      node_1631
      node_1632
      (invalid_excluded a [7,6,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,4] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,7] (by decide +kernel))
      node_1642)

theorem node_1646 : Excluded a [7,6,3,5] :=
  source_excluded a [7,6,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1649 : Excluded a [7,6,3,8,0,1] :=
  predecessor_excluded a [7,6,3,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1650 : Excluded a [7,6,3,8,0,2] :=
  source_excluded a [7,6,3,8,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1651 : Excluded a [7,6,3,8,0,4] :=
  source_excluded a [7,6,3,8,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1648 : Excluded a [7,6,3,8,0] :=
  branch_excluded a [7,6,3,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,3,8,0,0] (by decide +kernel))
      node_1649
      node_1650
      (invalid_excluded a [7,6,3,8,0,3] (by decide +kernel))
      node_1651
      (invalid_excluded a [7,6,3,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,0,8] (by decide +kernel)))

theorem node_1653 : Excluded a [7,6,3,8,1,0] :=
  source_excluded a [7,6,3,8,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1654 : Excluded a [7,6,3,8,1,2] :=
  source_excluded a [7,6,3,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1655 : Excluded a [7,6,3,8,1,4] :=
  source_excluded a [7,6,3,8,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1652 : Excluded a [7,6,3,8,1] :=
  branch_excluded a [7,6,3,8,1] (by decide)
    (fin9_cases _
      node_1653
      (invalid_excluded a [7,6,3,8,1,1] (by decide +kernel))
      node_1654
      (invalid_excluded a [7,6,3,8,1,3] (by decide +kernel))
      node_1655
      (invalid_excluded a [7,6,3,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,1,8] (by decide +kernel)))

theorem node_1656 : Excluded a [7,6,3,8,2] :=
  predecessor_excluded a [7,6,3,8,2] 0 3 4 2 (by decide) (by decide +kernel)

theorem node_1647 : Excluded a [7,6,3,8] :=
  branch_excluded a [7,6,3,8] (by decide)
    (fin9_cases _
      node_1648
      node_1652
      node_1656
      (invalid_excluded a [7,6,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,8] (by decide +kernel)))

theorem node_1627 : Excluded a [7,6,3] :=
  branch_excluded a [7,6,3] (by decide)
    (fin9_cases _
      node_1628
      node_1629
      node_1630
      (invalid_excluded a [7,6,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,4] (by decide +kernel))
      node_1646
      (invalid_excluded a [7,6,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,7] (by decide +kernel))
      node_1647)

theorem node_1658 : Excluded a [7,6,4,0] :=
  source_excluded a [7,6,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1660 : Excluded a [7,6,4,1,0] :=
  source_excluded a [7,6,4,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1661 : Excluded a [7,6,4,1,2] :=
  predecessor_excluded a [7,6,4,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1662 : Excluded a [7,6,4,1,3] :=
  source_excluded a [7,6,4,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1664 : Excluded a [7,6,4,1,8,0] :=
  predecessor_excluded a [7,6,4,1,8,0] 2 1 5 3 (by decide) (by decide +kernel)

theorem node_1665 : Excluded a [7,6,4,1,8,2] :=
  predecessor_excluded a [7,6,4,1,8,2] 0 4 5 2 (by decide) (by decide +kernel)

theorem node_1663 : Excluded a [7,6,4,1,8] :=
  branch_excluded a [7,6,4,1,8] (by decide)
    (fin9_cases _
      node_1664
      (invalid_excluded a [7,6,4,1,8,1] (by decide +kernel))
      node_1665
      (invalid_excluded a [7,6,4,1,8,3] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,8,8] (by decide +kernel)))

theorem node_1659 : Excluded a [7,6,4,1] :=
  branch_excluded a [7,6,4,1] (by decide)
    (fin9_cases _
      node_1660
      (invalid_excluded a [7,6,4,1,1] (by decide +kernel))
      node_1661
      node_1662
      (invalid_excluded a [7,6,4,1,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,7] (by decide +kernel))
      node_1663)

theorem node_1666 : Excluded a [7,6,4,2] :=
  source_excluded a [7,6,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_1667 : Excluded a [7,6,4,5] :=
  source_excluded a [7,6,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1669 : Excluded a [7,6,4,8,0] :=
  source_excluded a [7,6,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1670 : Excluded a [7,6,4,8,1] :=
  predecessor_excluded a [7,6,4,8,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_1672 : Excluded a [7,6,4,8,2,0] :=
  predecessor_excluded a [7,6,4,8,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1674 : Excluded a [7,6,4,8,2,1,0] :=
  source_excluded a [7,6,4,8,2,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1675 : Excluded a [7,6,4,8,2,1,3] :=
  predecessor_excluded a [7,6,4,8,2,1,3] 0 8 6 3 (by decide) (by decide +kernel)

def b_1678 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 4
  | 3 => 8
  | 4 => 2
  | 5 => 1
  | 6 => 5
  | 7 => 0
  | 8 => 3
  | _ => 0

def cert_1678 : LosingRegion (edgeOf a b_1678) 0 :=
  losingMask a b_1678 0 2149860820041979063700480
    (by decide +kernel) (by decide +kernel)

theorem node_1678 : Excluded a [7,6,4,8,2,1,5,0,3] :=
  losing_excluded a [7,6,4,8,2,1,5,0,3] (by decide) b_1678 (by decide +kernel) 1 0 2 cert_1678 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1678 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2149860820041979063700480 1 2; decide +kernel)

theorem node_1677 : Excluded a [7,6,4,8,2,1,5,0] :=
  branch_excluded a [7,6,4,8,2,1,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,4,8,2,1,5,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,0,1] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,0,2] (by decide +kernel))
      node_1678
      (invalid_excluded a [7,6,4,8,2,1,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,0,8] (by decide +kernel)))

theorem node_1679 : Excluded a [7,6,4,8,2,1,5,3] :=
  source_excluded a [7,6,4,8,2,1,5,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_1676 : Excluded a [7,6,4,8,2,1,5] :=
  branch_excluded a [7,6,4,8,2,1,5] (by decide)
    (fin9_cases _
      node_1677
      (invalid_excluded a [7,6,4,8,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,2] (by decide +kernel))
      node_1679
      (invalid_excluded a [7,6,4,8,2,1,5,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,5,8] (by decide +kernel)))

theorem node_1673 : Excluded a [7,6,4,8,2,1] :=
  branch_excluded a [7,6,4,8,2,1] (by decide)
    (fin9_cases _
      node_1674
      (invalid_excluded a [7,6,4,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,2] (by decide +kernel))
      node_1675
      (invalid_excluded a [7,6,4,8,2,1,4] (by decide +kernel))
      node_1676
      (invalid_excluded a [7,6,4,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,1,8] (by decide +kernel)))

theorem node_1671 : Excluded a [7,6,4,8,2] :=
  branch_excluded a [7,6,4,8,2] (by decide)
    (fin9_cases _
      node_1672
      node_1673
      (invalid_excluded a [7,6,4,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,8] (by decide +kernel)))

theorem node_1680 : Excluded a [7,6,4,8,3] :=
  source_excluded a [7,6,4,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1668 : Excluded a [7,6,4,8] :=
  branch_excluded a [7,6,4,8] (by decide)
    (fin9_cases _
      node_1669
      node_1670
      node_1671
      node_1680
      (invalid_excluded a [7,6,4,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,8] (by decide +kernel)))

theorem node_1657 : Excluded a [7,6,4] :=
  branch_excluded a [7,6,4] (by decide)
    (fin9_cases _
      node_1658
      node_1659
      node_1666
      (invalid_excluded a [7,6,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,4,4] (by decide +kernel))
      node_1667
      (invalid_excluded a [7,6,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,7] (by decide +kernel))
      node_1668)

theorem node_1683 : Excluded a [7,6,5,0,1] :=
  predecessor_excluded a [7,6,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1684 : Excluded a [7,6,5,0,2] :=
  source_excluded a [7,6,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1685 : Excluded a [7,6,5,0,3] :=
  source_excluded a [7,6,5,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1687 : Excluded a [7,6,5,0,8,1] :=
  predecessor_excluded a [7,6,5,0,8,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_1688 : Excluded a [7,6,5,0,8,2] :=
  predecessor_excluded a [7,6,5,0,8,2] 1 0 5 3 (by decide) (by decide +kernel)

theorem node_1689 : Excluded a [7,6,5,0,8,4] :=
  source_excluded a [7,6,5,0,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1686 : Excluded a [7,6,5,0,8] :=
  branch_excluded a [7,6,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,8,0] (by decide +kernel))
      node_1687
      node_1688
      (invalid_excluded a [7,6,5,0,8,3] (by decide +kernel))
      node_1689
      (invalid_excluded a [7,6,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,8] (by decide +kernel)))

theorem node_1682 : Excluded a [7,6,5,0] :=
  branch_excluded a [7,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,0] (by decide +kernel))
      node_1683
      node_1684
      node_1685
      (invalid_excluded a [7,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,7] (by decide +kernel))
      node_1686)

theorem node_1691 : Excluded a [7,6,5,1,0] :=
  source_excluded a [7,6,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1692 : Excluded a [7,6,5,1,2] :=
  source_excluded a [7,6,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1693 : Excluded a [7,6,5,1,3] :=
  source_excluded a [7,6,5,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1695 : Excluded a [7,6,5,1,8,0] :=
  source_excluded a [7,6,5,1,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1697 : Excluded a [7,6,5,1,8,2,0] :=
  source_excluded a [7,6,5,1,8,2,0] 6 1 0 (by decide) (by decide +kernel)

def b_1700 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 5
  | 3 => 1
  | 4 => 8
  | 5 => 2
  | 6 => 3
  | 7 => 0
  | 8 => 4
  | _ => 0

def cert_1700 : LosingRegion (edgeOf a b_1700) 0 :=
  losingMask a b_1700 0 2149860819446660089252864
    (by decide +kernel) (by decide +kernel)

theorem node_1700 : Excluded a [7,6,5,1,8,2,3,0,4] :=
  losing_excluded a [7,6,5,1,8,2,3,0,4] (by decide) b_1700 (by decide +kernel) 1 0 2 cert_1700 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1700 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2149860819446660089252864 1 2; decide +kernel)

theorem node_1699 : Excluded a [7,6,5,1,8,2,3,0] :=
  branch_excluded a [7,6,5,1,8,2,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,1,8,2,3,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,0,1] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,0,2] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,0,3] (by decide +kernel))
      node_1700
      (invalid_excluded a [7,6,5,1,8,2,3,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,0,8] (by decide +kernel)))

theorem node_1701 : Excluded a [7,6,5,1,8,2,3,4] :=
  source_excluded a [7,6,5,1,8,2,3,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_1698 : Excluded a [7,6,5,1,8,2,3] :=
  branch_excluded a [7,6,5,1,8,2,3] (by decide)
    (fin9_cases _
      node_1699
      (invalid_excluded a [7,6,5,1,8,2,3,1] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,3] (by decide +kernel))
      node_1701
      (invalid_excluded a [7,6,5,1,8,2,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,3,8] (by decide +kernel)))

theorem node_1702 : Excluded a [7,6,5,1,8,2,4] :=
  predecessor_excluded a [7,6,5,1,8,2,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1696 : Excluded a [7,6,5,1,8,2] :=
  branch_excluded a [7,6,5,1,8,2] (by decide)
    (fin9_cases _
      node_1697
      (invalid_excluded a [7,6,5,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,2] (by decide +kernel))
      node_1698
      node_1702
      (invalid_excluded a [7,6,5,1,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,2,8] (by decide +kernel)))

theorem node_1703 : Excluded a [7,6,5,1,8,4] :=
  source_excluded a [7,6,5,1,8,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1694 : Excluded a [7,6,5,1,8] :=
  branch_excluded a [7,6,5,1,8] (by decide)
    (fin9_cases _
      node_1695
      (invalid_excluded a [7,6,5,1,8,1] (by decide +kernel))
      node_1696
      (invalid_excluded a [7,6,5,1,8,3] (by decide +kernel))
      node_1703
      (invalid_excluded a [7,6,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,8] (by decide +kernel)))

theorem node_1690 : Excluded a [7,6,5,1] :=
  branch_excluded a [7,6,5,1] (by decide)
    (fin9_cases _
      node_1691
      (invalid_excluded a [7,6,5,1,1] (by decide +kernel))
      node_1692
      node_1693
      (invalid_excluded a [7,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,7] (by decide +kernel))
      node_1694)

theorem node_1704 : Excluded a [7,6,5,2] :=
  predecessor_excluded a [7,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_1706 : Excluded a [7,6,5,8,0] :=
  source_excluded a [7,6,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1708 : Excluded a [7,6,5,8,1,0] :=
  source_excluded a [7,6,5,8,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1709 : Excluded a [7,6,5,8,1,2] :=
  predecessor_excluded a [7,6,5,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1710 : Excluded a [7,6,5,8,1,4] :=
  source_excluded a [7,6,5,8,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1707 : Excluded a [7,6,5,8,1] :=
  branch_excluded a [7,6,5,8,1] (by decide)
    (fin9_cases _
      node_1708
      (invalid_excluded a [7,6,5,8,1,1] (by decide +kernel))
      node_1709
      (invalid_excluded a [7,6,5,8,1,3] (by decide +kernel))
      node_1710
      (invalid_excluded a [7,6,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,1,8] (by decide +kernel)))

theorem node_1711 : Excluded a [7,6,5,8,2] :=
  source_excluded a [7,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1712 : Excluded a [7,6,5,8,3] :=
  source_excluded a [7,6,5,8,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1705 : Excluded a [7,6,5,8] :=
  branch_excluded a [7,6,5,8] (by decide)
    (fin9_cases _
      node_1706
      node_1707
      node_1711
      node_1712
      (invalid_excluded a [7,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,8] (by decide +kernel)))

theorem node_1681 : Excluded a [7,6,5] :=
  branch_excluded a [7,6,5] (by decide)
    (fin9_cases _
      node_1682
      node_1690
      node_1704
      (invalid_excluded a [7,6,5,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,7] (by decide +kernel))
      node_1705)

theorem node_1715 : Excluded a [7,6,8,0,1] :=
  predecessor_excluded a [7,6,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1719 : Excluded a [7,6,8,0,2,1,3,4] :=
  predecessor_excluded a [7,6,8,0,2,1,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_1721 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 3
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_1721 : LosingRegion (edgeOf a b_1721) 0 :=
  losingMask a b_1721 0 1324551886374561100342272
    (by decide +kernel) (by decide +kernel)

theorem node_1721 : Excluded a [7,6,8,0,2,1,3,5,4] :=
  losing_excluded a [7,6,8,0,2,1,3,5,4] (by decide) b_1721 (by decide +kernel) 1 0 4 cert_1721 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1721 1 0 ∧ 4 ≠ 1 ∧ maskRegion 1324551886374561100342272 1 4; decide +kernel)

theorem node_1720 : Excluded a [7,6,8,0,2,1,3,5] :=
  branch_excluded a [7,6,8,0,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,5,3] (by decide +kernel))
      node_1721
      (invalid_excluded a [7,6,8,0,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,5,8] (by decide +kernel)))

theorem node_1718 : Excluded a [7,6,8,0,2,1,3] :=
  branch_excluded a [7,6,8,0,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,3] (by decide +kernel))
      node_1719
      node_1720
      (invalid_excluded a [7,6,8,0,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,3,8] (by decide +kernel)))

def b_1724 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 4
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_1724 : LosingRegion (edgeOf a b_1724) 0 :=
  losingMask a b_1724 0 2079392365640379800757248
    (by decide +kernel) (by decide +kernel)

theorem node_1724 : Excluded a [7,6,8,0,2,1,4,3,5] :=
  losing_excluded a [7,6,8,0,2,1,4,3,5] (by decide) b_1724 (by decide +kernel) 1 0 4 cert_1724 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1724 1 0 ∧ 4 ≠ 1 ∧ maskRegion 2079392365640379800757248 1 4; decide +kernel)

theorem node_1723 : Excluded a [7,6,8,0,2,1,4,3] :=
  branch_excluded a [7,6,8,0,2,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,3,4] (by decide +kernel))
      node_1724
      (invalid_excluded a [7,6,8,0,2,1,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,3,8] (by decide +kernel)))

theorem node_1725 : Excluded a [7,6,8,0,2,1,4,5] :=
  predecessor_excluded a [7,6,8,0,2,1,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1722 : Excluded a [7,6,8,0,2,1,4] :=
  branch_excluded a [7,6,8,0,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,2] (by decide +kernel))
      node_1723
      (invalid_excluded a [7,6,8,0,2,1,4,4] (by decide +kernel))
      node_1725
      (invalid_excluded a [7,6,8,0,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,4,8] (by decide +kernel)))

theorem node_1727 : Excluded a [7,6,8,0,2,1,5,3] :=
  predecessor_excluded a [7,6,8,0,2,1,5,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_1729 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_1729 : LosingRegion (edgeOf a b_1729) 0 :=
  losingMask a b_1729 0 1399229206301331944385536
    (by decide +kernel) (by decide +kernel)

theorem node_1729 : Excluded a [7,6,8,0,2,1,5,4,3] :=
  losing_excluded a [7,6,8,0,2,1,5,4,3] (by decide) b_1729 (by decide +kernel) 1 0 2 cert_1729 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1729 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1399229206301331944385536 1 2; decide +kernel)

theorem node_1728 : Excluded a [7,6,8,0,2,1,5,4] :=
  branch_excluded a [7,6,8,0,2,1,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,1,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,4,2] (by decide +kernel))
      node_1729
      (invalid_excluded a [7,6,8,0,2,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,4,8] (by decide +kernel)))

theorem node_1726 : Excluded a [7,6,8,0,2,1,5] :=
  branch_excluded a [7,6,8,0,2,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,2] (by decide +kernel))
      node_1727
      node_1728
      (invalid_excluded a [7,6,8,0,2,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,5,8] (by decide +kernel)))

theorem node_1717 : Excluded a [7,6,8,0,2,1] :=
  branch_excluded a [7,6,8,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,2] (by decide +kernel))
      node_1718
      node_1722
      node_1726
      (invalid_excluded a [7,6,8,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,1,8] (by decide +kernel)))

theorem node_1730 : Excluded a [7,6,8,0,2,4] :=
  source_excluded a [7,6,8,0,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1716 : Excluded a [7,6,8,0,2] :=
  branch_excluded a [7,6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,0] (by decide +kernel))
      node_1717
      (invalid_excluded a [7,6,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3] (by decide +kernel))
      node_1730
      (invalid_excluded a [7,6,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,8] (by decide +kernel)))

theorem node_1731 : Excluded a [7,6,8,0,3] :=
  source_excluded a [7,6,8,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1714 : Excluded a [7,6,8,0] :=
  branch_excluded a [7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,0] (by decide +kernel))
      node_1715
      node_1716
      node_1731
      (invalid_excluded a [7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,8] (by decide +kernel)))

theorem node_1736 : Excluded a [7,6,8,1,0,2,3,4] :=
  predecessor_excluded a [7,6,8,1,0,2,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_1738 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 3
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_1738 : LosingRegion (edgeOf a b_1738) 0 :=
  losingMask a b_1738 0 1323892703222829306366976
    (by decide +kernel) (by decide +kernel)

theorem node_1738 : Excluded a [7,6,8,1,0,2,3,5,4] :=
  losing_excluded a [7,6,8,1,0,2,3,5,4] (by decide) b_1738 (by decide +kernel) 1 0 2 cert_1738 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1738 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1323892703222829306366976 1 2; decide +kernel)

theorem node_1737 : Excluded a [7,6,8,1,0,2,3,5] :=
  branch_excluded a [7,6,8,1,0,2,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,2,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,5,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,5,3] (by decide +kernel))
      node_1738
      (invalid_excluded a [7,6,8,1,0,2,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,5,8] (by decide +kernel)))

theorem node_1735 : Excluded a [7,6,8,1,0,2,3] :=
  branch_excluded a [7,6,8,1,0,2,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,2,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,3] (by decide +kernel))
      node_1736
      node_1737
      (invalid_excluded a [7,6,8,1,0,2,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,3,8] (by decide +kernel)))

def b_1741 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 4
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_1741 : LosingRegion (edgeOf a b_1741) 0 :=
  losingMask a b_1741 0 1437888393451583604540416
    (by decide +kernel) (by decide +kernel)

theorem node_1741 : Excluded a [7,6,8,1,0,2,4,3,5] :=
  losing_excluded a [7,6,8,1,0,2,4,3,5] (by decide) b_1741 (by decide +kernel) 1 0 5 cert_1741 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1741 1 0 ∧ 5 ≠ 1 ∧ maskRegion 1437888393451583604540416 1 5; decide +kernel)

theorem node_1740 : Excluded a [7,6,8,1,0,2,4,3] :=
  branch_excluded a [7,6,8,1,0,2,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,2,4,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,3,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,3,4] (by decide +kernel))
      node_1741
      (invalid_excluded a [7,6,8,1,0,2,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,3,8] (by decide +kernel)))

theorem node_1742 : Excluded a [7,6,8,1,0,2,4,5] :=
  predecessor_excluded a [7,6,8,1,0,2,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1739 : Excluded a [7,6,8,1,0,2,4] :=
  branch_excluded a [7,6,8,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,2] (by decide +kernel))
      node_1740
      (invalid_excluded a [7,6,8,1,0,2,4,4] (by decide +kernel))
      node_1742
      (invalid_excluded a [7,6,8,1,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,4,8] (by decide +kernel)))

theorem node_1744 : Excluded a [7,6,8,1,0,2,5,3] :=
  predecessor_excluded a [7,6,8,1,0,2,5,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_1746 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_1746 : LosingRegion (edgeOf a b_1746) 0 :=
  losingMask a b_1746 0 2079245223751881522693120
    (by decide +kernel) (by decide +kernel)

theorem node_1746 : Excluded a [7,6,8,1,0,2,5,4,3] :=
  losing_excluded a [7,6,8,1,0,2,5,4,3] (by decide) b_1746 (by decide +kernel) 1 0 5 cert_1746 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1746 1 0 ∧ 5 ≠ 1 ∧ maskRegion 2079245223751881522693120 1 5; decide +kernel)

theorem node_1745 : Excluded a [7,6,8,1,0,2,5,4] :=
  branch_excluded a [7,6,8,1,0,2,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,2,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,4,2] (by decide +kernel))
      node_1746
      (invalid_excluded a [7,6,8,1,0,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,4,8] (by decide +kernel)))

theorem node_1743 : Excluded a [7,6,8,1,0,2,5] :=
  branch_excluded a [7,6,8,1,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,2,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,2] (by decide +kernel))
      node_1744
      node_1745
      (invalid_excluded a [7,6,8,1,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,5,8] (by decide +kernel)))

theorem node_1734 : Excluded a [7,6,8,1,0,2] :=
  branch_excluded a [7,6,8,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,2] (by decide +kernel))
      node_1735
      node_1739
      node_1743
      (invalid_excluded a [7,6,8,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,2,8] (by decide +kernel)))

theorem node_1747 : Excluded a [7,6,8,1,0,4] :=
  source_excluded a [7,6,8,1,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1733 : Excluded a [7,6,8,1,0] :=
  branch_excluded a [7,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,1] (by decide +kernel))
      node_1734
      (invalid_excluded a [7,6,8,1,0,3] (by decide +kernel))
      node_1747
      (invalid_excluded a [7,6,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,8] (by decide +kernel)))

theorem node_1748 : Excluded a [7,6,8,1,2] :=
  predecessor_excluded a [7,6,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1749 : Excluded a [7,6,8,1,3] :=
  source_excluded a [7,6,8,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1732 : Excluded a [7,6,8,1] :=
  branch_excluded a [7,6,8,1] (by decide)
    (fin9_cases _
      node_1733
      (invalid_excluded a [7,6,8,1,1] (by decide +kernel))
      node_1748
      node_1749
      (invalid_excluded a [7,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,8] (by decide +kernel)))

theorem node_1751 : Excluded a [7,6,8,2,0] :=
  predecessor_excluded a [7,6,8,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1755 : Excluded a [7,6,8,2,1,0,3,4] :=
  predecessor_excluded a [7,6,8,2,1,0,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_1757 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 3
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_1757 : LosingRegion (edgeOf a b_1757) 0 :=
  losingMask a b_1757 0 2079466440567774837216256
    (by decide +kernel) (by decide +kernel)

theorem node_1757 : Excluded a [7,6,8,2,1,0,3,5,4] :=
  losing_excluded a [7,6,8,2,1,0,3,5,4] (by decide) b_1757 (by decide +kernel) 1 0 3 cert_1757 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1757 1 0 ∧ 3 ≠ 1 ∧ maskRegion 2079466440567774837216256 1 3; decide +kernel)

theorem node_1756 : Excluded a [7,6,8,2,1,0,3,5] :=
  branch_excluded a [7,6,8,2,1,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,1,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,5,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,5,3] (by decide +kernel))
      node_1757
      (invalid_excluded a [7,6,8,2,1,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,5,8] (by decide +kernel)))

theorem node_1754 : Excluded a [7,6,8,2,1,0,3] :=
  branch_excluded a [7,6,8,2,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,3] (by decide +kernel))
      node_1755
      node_1756
      (invalid_excluded a [7,6,8,2,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,3,8] (by decide +kernel)))

def b_1760 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 4
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_1760 : LosingRegion (edgeOf a b_1760) 0 :=
  losingMask a b_1760 0 1437155711837602829048832
    (by decide +kernel) (by decide +kernel)

theorem node_1760 : Excluded a [7,6,8,2,1,0,4,3,5] :=
  losing_excluded a [7,6,8,2,1,0,4,3,5] (by decide) b_1760 (by decide +kernel) 1 0 2 cert_1760 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1760 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1437155711837602829048832 1 2; decide +kernel)

theorem node_1759 : Excluded a [7,6,8,2,1,0,4,3] :=
  branch_excluded a [7,6,8,2,1,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,1,0,4,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,3,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,3,4] (by decide +kernel))
      node_1760
      (invalid_excluded a [7,6,8,2,1,0,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,3,8] (by decide +kernel)))

theorem node_1761 : Excluded a [7,6,8,2,1,0,4,5] :=
  predecessor_excluded a [7,6,8,2,1,0,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1758 : Excluded a [7,6,8,2,1,0,4] :=
  branch_excluded a [7,6,8,2,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,2] (by decide +kernel))
      node_1759
      (invalid_excluded a [7,6,8,2,1,0,4,4] (by decide +kernel))
      node_1761
      (invalid_excluded a [7,6,8,2,1,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,4,8] (by decide +kernel)))

theorem node_1763 : Excluded a [7,6,8,2,1,0,5,3] :=
  predecessor_excluded a [7,6,8,2,1,0,5,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_1765 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_1765 : LosingRegion (edgeOf a b_1765) 0 :=
  losingMask a b_1765 0 1400109893936387546158080
    (by decide +kernel) (by decide +kernel)

theorem node_1765 : Excluded a [7,6,8,2,1,0,5,4,3] :=
  losing_excluded a [7,6,8,2,1,0,5,4,3] (by decide) b_1765 (by decide +kernel) 1 0 3 cert_1765 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1765 1 0 ∧ 3 ≠ 1 ∧ maskRegion 1400109893936387546158080 1 3; decide +kernel)

theorem node_1764 : Excluded a [7,6,8,2,1,0,5,4] :=
  branch_excluded a [7,6,8,2,1,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,1,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,4,2] (by decide +kernel))
      node_1765
      (invalid_excluded a [7,6,8,2,1,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,4,8] (by decide +kernel)))

theorem node_1762 : Excluded a [7,6,8,2,1,0,5] :=
  branch_excluded a [7,6,8,2,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,2] (by decide +kernel))
      node_1763
      node_1764
      (invalid_excluded a [7,6,8,2,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,5,8] (by decide +kernel)))

theorem node_1753 : Excluded a [7,6,8,2,1,0] :=
  branch_excluded a [7,6,8,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,2] (by decide +kernel))
      node_1754
      node_1758
      node_1762
      (invalid_excluded a [7,6,8,2,1,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,0,8] (by decide +kernel)))

theorem node_1766 : Excluded a [7,6,8,2,1,4] :=
  source_excluded a [7,6,8,2,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1752 : Excluded a [7,6,8,2,1] :=
  branch_excluded a [7,6,8,2,1] (by decide)
    (fin9_cases _
      node_1753
      (invalid_excluded a [7,6,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,3] (by decide +kernel))
      node_1766
      (invalid_excluded a [7,6,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,1,8] (by decide +kernel)))

theorem node_1767 : Excluded a [7,6,8,2,3] :=
  source_excluded a [7,6,8,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1750 : Excluded a [7,6,8,2] :=
  branch_excluded a [7,6,8,2] (by decide)
    (fin9_cases _
      node_1751
      node_1752
      (invalid_excluded a [7,6,8,2,2] (by decide +kernel))
      node_1767
      (invalid_excluded a [7,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,8] (by decide +kernel)))

theorem node_1768 : Excluded a [7,6,8,5] :=
  source_excluded a [7,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1713 : Excluded a [7,6,8] :=
  branch_excluded a [7,6,8] (by decide)
    (fin9_cases _
      node_1714
      node_1732
      node_1750
      (invalid_excluded a [7,6,8,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,4] (by decide +kernel))
      node_1768
      (invalid_excluded a [7,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,8] (by decide +kernel)))

theorem node_1625 : Excluded a [7,6] :=
  branch_excluded a [7,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0] (by decide +kernel))
      node_1626
      (invalid_excluded a [7,6,2] (by decide +kernel))
      node_1627
      node_1657
      node_1681
      (invalid_excluded a [7,6,6] (by decide +kernel))
      (invalid_excluded a [7,6,7] (by decide +kernel))
      node_1713)

theorem node_1769 : Excluded a [7,8] :=
  predecessor_excluded a [7,8] 2 8 0 1 (by decide) (by decide +kernel)

theorem node_1428 : Excluded a [7] :=
  branch_excluded a [7] (by decide)
    (fin9_cases _
      node_1429
      (invalid_excluded a [7,1] (by decide +kernel))
      (invalid_excluded a [7,2] (by decide +kernel))
      node_1430
      node_1502
      node_1562
      node_1625
      (invalid_excluded a [7,7] (by decide +kernel))
      node_1769)

theorem node_1771 : Excluded a [8,0] :=
  source_excluded a [8,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_1773 : Excluded a [8,3,1] :=
  source_excluded a [8,3,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1774 : Excluded a [8,3,4] :=
  predecessor_excluded a [8,3,4] 0 4 1 2 (by decide) (by decide +kernel)

theorem node_1776 : Excluded a [8,3,5,0] :=
  predecessor_excluded a [8,3,5,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1778 : Excluded a [8,3,5,1,0] :=
  source_excluded a [8,3,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1779 : Excluded a [8,3,5,1,2] :=
  source_excluded a [8,3,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1781 : Excluded a [8,3,5,1,6,0] :=
  source_excluded a [8,3,5,1,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1782 : Excluded a [8,3,5,1,6,2] :=
  source_excluded a [8,3,5,1,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1783 : Excluded a [8,3,5,1,6,4] :=
  source_excluded a [8,3,5,1,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1784 : Excluded a [8,3,5,1,6,7] :=
  predecessor_excluded a [8,3,5,1,6,7] 0 7 4 5 (by decide) (by decide +kernel)

theorem node_1780 : Excluded a [8,3,5,1,6] :=
  branch_excluded a [8,3,5,1,6] (by decide)
    (fin9_cases _
      node_1781
      (invalid_excluded a [8,3,5,1,6,1] (by decide +kernel))
      node_1782
      (invalid_excluded a [8,3,5,1,6,3] (by decide +kernel))
      node_1783
      (invalid_excluded a [8,3,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,6,6] (by decide +kernel))
      node_1784
      (invalid_excluded a [8,3,5,1,6,8] (by decide +kernel)))

theorem node_1786 : Excluded a [8,3,5,1,7,0] :=
  source_excluded a [8,3,5,1,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1787 : Excluded a [8,3,5,1,7,2] :=
  source_excluded a [8,3,5,1,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1788 : Excluded a [8,3,5,1,7,4] :=
  source_excluded a [8,3,5,1,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1790 : Excluded a [8,3,5,1,7,6,0] :=
  predecessor_excluded a [8,3,5,1,7,6,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_1792 : Excluded a [8,3,5,1,7,6,2,0] :=
  source_excluded a [8,3,5,1,7,6,2,0] 7 1 0 (by decide) (by decide +kernel)

def b_1794 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 3
  | 2 => 5
  | 3 => 1
  | 4 => 7
  | 5 => 6
  | 6 => 2
  | 7 => 4
  | 8 => 0
  | _ => 0

def cert_1794 : LosingRegion (edgeOf a b_1794) 0 :=
  losingMask a b_1794 0 1212478055456200809548800
    (by decide +kernel) (by decide +kernel)

theorem node_1794 : Excluded a [8,3,5,1,7,6,2,4,0] :=
  losing_excluded a [8,3,5,1,7,6,2,4,0] (by decide) b_1794 (by decide +kernel) 1 0 2 cert_1794 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1794 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212478055456200809548800 1 2; decide +kernel)

theorem node_1793 : Excluded a [8,3,5,1,7,6,2,4] :=
  branch_excluded a [8,3,5,1,7,6,2,4] (by decide)
    (fin9_cases _
      node_1794
      (invalid_excluded a [8,3,5,1,7,6,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,4,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,4,3] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,4,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,4,8] (by decide +kernel)))

theorem node_1791 : Excluded a [8,3,5,1,7,6,2] :=
  branch_excluded a [8,3,5,1,7,6,2] (by decide)
    (fin9_cases _
      node_1792
      (invalid_excluded a [8,3,5,1,7,6,2,1] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,3] (by decide +kernel))
      node_1793
      (invalid_excluded a [8,3,5,1,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,2,8] (by decide +kernel)))

theorem node_1795 : Excluded a [8,3,5,1,7,6,4] :=
  source_excluded a [8,3,5,1,7,6,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1789 : Excluded a [8,3,5,1,7,6] :=
  branch_excluded a [8,3,5,1,7,6] (by decide)
    (fin9_cases _
      node_1790
      (invalid_excluded a [8,3,5,1,7,6,1] (by decide +kernel))
      node_1791
      (invalid_excluded a [8,3,5,1,7,6,3] (by decide +kernel))
      node_1795
      (invalid_excluded a [8,3,5,1,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,6,8] (by decide +kernel)))

theorem node_1785 : Excluded a [8,3,5,1,7] :=
  branch_excluded a [8,3,5,1,7] (by decide)
    (fin9_cases _
      node_1786
      (invalid_excluded a [8,3,5,1,7,1] (by decide +kernel))
      node_1787
      (invalid_excluded a [8,3,5,1,7,3] (by decide +kernel))
      node_1788
      (invalid_excluded a [8,3,5,1,7,5] (by decide +kernel))
      node_1789
      (invalid_excluded a [8,3,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,7,8] (by decide +kernel)))

theorem node_1777 : Excluded a [8,3,5,1] :=
  branch_excluded a [8,3,5,1] (by decide)
    (fin9_cases _
      node_1778
      (invalid_excluded a [8,3,5,1,1] (by decide +kernel))
      node_1779
      (invalid_excluded a [8,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,3,5,1,5] (by decide +kernel))
      node_1780
      node_1785
      (invalid_excluded a [8,3,5,1,8] (by decide +kernel)))

theorem node_1796 : Excluded a [8,3,5,2] :=
  source_excluded a [8,3,5,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1798 : Excluded a [8,3,5,6,0] :=
  source_excluded a [8,3,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1799 : Excluded a [8,3,5,6,1] :=
  predecessor_excluded a [8,3,5,6,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1800 : Excluded a [8,3,5,6,2] :=
  source_excluded a [8,3,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1801 : Excluded a [8,3,5,6,7] :=
  predecessor_excluded a [8,3,5,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1797 : Excluded a [8,3,5,6] :=
  branch_excluded a [8,3,5,6] (by decide)
    (fin9_cases _
      node_1798
      node_1799
      node_1800
      (invalid_excluded a [8,3,5,6,3] (by decide +kernel))
      (invalid_excluded a [8,3,5,6,4] (by decide +kernel))
      (invalid_excluded a [8,3,5,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,6,6] (by decide +kernel))
      node_1801
      (invalid_excluded a [8,3,5,6,8] (by decide +kernel)))

theorem node_1803 : Excluded a [8,3,5,7,0] :=
  source_excluded a [8,3,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1804 : Excluded a [8,3,5,7,1] :=
  predecessor_excluded a [8,3,5,7,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1805 : Excluded a [8,3,5,7,2] :=
  source_excluded a [8,3,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1807 : Excluded a [8,3,5,7,6,0] :=
  source_excluded a [8,3,5,7,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1808 : Excluded a [8,3,5,7,6,1] :=
  source_excluded a [8,3,5,7,6,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1809 : Excluded a [8,3,5,7,6,2] :=
  source_excluded a [8,3,5,7,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1810 : Excluded a [8,3,5,7,6,4] :=
  source_excluded a [8,3,5,7,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1806 : Excluded a [8,3,5,7,6] :=
  branch_excluded a [8,3,5,7,6] (by decide)
    (fin9_cases _
      node_1807
      node_1808
      node_1809
      (invalid_excluded a [8,3,5,7,6,3] (by decide +kernel))
      node_1810
      (invalid_excluded a [8,3,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,8] (by decide +kernel)))

theorem node_1802 : Excluded a [8,3,5,7] :=
  branch_excluded a [8,3,5,7] (by decide)
    (fin9_cases _
      node_1803
      node_1804
      node_1805
      (invalid_excluded a [8,3,5,7,3] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,5] (by decide +kernel))
      node_1806
      (invalid_excluded a [8,3,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,8] (by decide +kernel)))

theorem node_1775 : Excluded a [8,3,5] :=
  branch_excluded a [8,3,5] (by decide)
    (fin9_cases _
      node_1776
      node_1777
      node_1796
      (invalid_excluded a [8,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,3,5,5] (by decide +kernel))
      node_1797
      node_1802
      (invalid_excluded a [8,3,5,8] (by decide +kernel)))

theorem node_1812 : Excluded a [8,3,6,0] :=
  predecessor_excluded a [8,3,6,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1815 : Excluded a [8,3,6,1,0,2] :=
  source_excluded a [8,3,6,1,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1816 : Excluded a [8,3,6,1,0,4] :=
  source_excluded a [8,3,6,1,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1819 : Excluded a [8,3,6,1,0,7,2,4] :=
  predecessor_excluded a [8,3,6,1,0,7,2,4] 0 4 5 7 (by decide) (by decide +kernel)

def b_1821 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 3
  | 2 => 6
  | 3 => 1
  | 4 => 0
  | 5 => 7
  | 6 => 2
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_1821 : LosingRegion (edgeOf a b_1821) 0 :=
  losingMask a b_1821 0 1248283210582628380967936
    (by decide +kernel) (by decide +kernel)

theorem node_1821 : Excluded a [8,3,6,1,0,7,2,5,4] :=
  losing_excluded a [8,3,6,1,0,7,2,5,4] (by decide) b_1821 (by decide +kernel) 5 0 1 cert_1821 (by change 5 ≠ 0 ∧ ¬ edgeOf a b_1821 5 0 ∧ 1 ≠ 5 ∧ maskRegion 1248283210582628380967936 5 1; decide +kernel)

theorem node_1820 : Excluded a [8,3,6,1,0,7,2,5] :=
  branch_excluded a [8,3,6,1,0,7,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,1,0,7,2,5,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,5,1] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,5,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,5,3] (by decide +kernel))
      node_1821
      (invalid_excluded a [8,3,6,1,0,7,2,5,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,5,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,5,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,5,8] (by decide +kernel)))

theorem node_1818 : Excluded a [8,3,6,1,0,7,2] :=
  branch_excluded a [8,3,6,1,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,1,0,7,2,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,1] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,3] (by decide +kernel))
      node_1819
      node_1820
      (invalid_excluded a [8,3,6,1,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,2,8] (by decide +kernel)))

theorem node_1823 : Excluded a [8,3,6,1,0,7,4,2] :=
  predecessor_excluded a [8,3,6,1,0,7,4,2] 0 6 7 2 (by decide) (by decide +kernel)

theorem node_1824 : Excluded a [8,3,6,1,0,7,4,5] :=
  predecessor_excluded a [8,3,6,1,0,7,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1822 : Excluded a [8,3,6,1,0,7,4] :=
  branch_excluded a [8,3,6,1,0,7,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,1,0,7,4,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,4,1] (by decide +kernel))
      node_1823
      (invalid_excluded a [8,3,6,1,0,7,4,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,4,4] (by decide +kernel))
      node_1824
      (invalid_excluded a [8,3,6,1,0,7,4,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,4,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,4,8] (by decide +kernel)))

theorem node_1825 : Excluded a [8,3,6,1,0,7,5] :=
  source_excluded a [8,3,6,1,0,7,5] 6 0 5 (by decide) (by decide +kernel)

theorem node_1817 : Excluded a [8,3,6,1,0,7] :=
  branch_excluded a [8,3,6,1,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,1,0,7,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,1] (by decide +kernel))
      node_1818
      (invalid_excluded a [8,3,6,1,0,7,3] (by decide +kernel))
      node_1822
      node_1825
      (invalid_excluded a [8,3,6,1,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,7,8] (by decide +kernel)))

theorem node_1814 : Excluded a [8,3,6,1,0] :=
  branch_excluded a [8,3,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,1] (by decide +kernel))
      node_1815
      (invalid_excluded a [8,3,6,1,0,3] (by decide +kernel))
      node_1816
      (invalid_excluded a [8,3,6,1,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,0,6] (by decide +kernel))
      node_1817
      (invalid_excluded a [8,3,6,1,0,8] (by decide +kernel)))

theorem node_1826 : Excluded a [8,3,6,1,2] :=
  predecessor_excluded a [8,3,6,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1828 : Excluded a [8,3,6,1,7,0] :=
  predecessor_excluded a [8,3,6,1,7,0] 2 1 5 3 (by decide) (by decide +kernel)

theorem node_1829 : Excluded a [8,3,6,1,7,2] :=
  source_excluded a [8,3,6,1,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1830 : Excluded a [8,3,6,1,7,4] :=
  source_excluded a [8,3,6,1,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1827 : Excluded a [8,3,6,1,7] :=
  branch_excluded a [8,3,6,1,7] (by decide)
    (fin9_cases _
      node_1828
      (invalid_excluded a [8,3,6,1,7,1] (by decide +kernel))
      node_1829
      (invalid_excluded a [8,3,6,1,7,3] (by decide +kernel))
      node_1830
      (invalid_excluded a [8,3,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,7,8] (by decide +kernel)))

theorem node_1813 : Excluded a [8,3,6,1] :=
  branch_excluded a [8,3,6,1] (by decide)
    (fin9_cases _
      node_1814
      (invalid_excluded a [8,3,6,1,1] (by decide +kernel))
      node_1826
      (invalid_excluded a [8,3,6,1,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,1,6] (by decide +kernel))
      node_1827
      (invalid_excluded a [8,3,6,1,8] (by decide +kernel)))

theorem node_1831 : Excluded a [8,3,6,2] :=
  source_excluded a [8,3,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1832 : Excluded a [8,3,6,5] :=
  source_excluded a [8,3,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1835 : Excluded a [8,3,6,7,0,1] :=
  source_excluded a [8,3,6,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1836 : Excluded a [8,3,6,7,0,2] :=
  source_excluded a [8,3,6,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1837 : Excluded a [8,3,6,7,0,4] :=
  source_excluded a [8,3,6,7,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1834 : Excluded a [8,3,6,7,0] :=
  branch_excluded a [8,3,6,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,7,0,0] (by decide +kernel))
      node_1835
      node_1836
      (invalid_excluded a [8,3,6,7,0,3] (by decide +kernel))
      node_1837
      (invalid_excluded a [8,3,6,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,0,8] (by decide +kernel)))

theorem node_1838 : Excluded a [8,3,6,7,1] :=
  predecessor_excluded a [8,3,6,7,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1840 : Excluded a [8,3,6,7,2,0] :=
  predecessor_excluded a [8,3,6,7,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1841 : Excluded a [8,3,6,7,2,1] :=
  source_excluded a [8,3,6,7,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1842 : Excluded a [8,3,6,7,2,4] :=
  source_excluded a [8,3,6,7,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1839 : Excluded a [8,3,6,7,2] :=
  branch_excluded a [8,3,6,7,2] (by decide)
    (fin9_cases _
      node_1840
      node_1841
      (invalid_excluded a [8,3,6,7,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,2,3] (by decide +kernel))
      node_1842
      (invalid_excluded a [8,3,6,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,2,8] (by decide +kernel)))

theorem node_1833 : Excluded a [8,3,6,7] :=
  branch_excluded a [8,3,6,7] (by decide)
    (fin9_cases _
      node_1834
      node_1838
      node_1839
      (invalid_excluded a [8,3,6,7,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,4] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,7,8] (by decide +kernel)))

theorem node_1811 : Excluded a [8,3,6] :=
  branch_excluded a [8,3,6] (by decide)
    (fin9_cases _
      node_1812
      node_1813
      node_1831
      (invalid_excluded a [8,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,4] (by decide +kernel))
      node_1832
      (invalid_excluded a [8,3,6,6] (by decide +kernel))
      node_1833
      (invalid_excluded a [8,3,6,8] (by decide +kernel)))

theorem node_1843 : Excluded a [8,3,7] :=
  predecessor_excluded a [8,3,7] 1 8 2 0 (by decide) (by decide +kernel)

theorem node_1772 : Excluded a [8,3] :=
  branch_excluded a [8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,0] (by decide +kernel))
      node_1773
      (invalid_excluded a [8,3,2] (by decide +kernel))
      (invalid_excluded a [8,3,3] (by decide +kernel))
      node_1774
      node_1775
      node_1811
      node_1843
      (invalid_excluded a [8,3,8] (by decide +kernel)))

theorem node_1845 : Excluded a [8,4,1] :=
  source_excluded a [8,4,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1847 : Excluded a [8,4,3,0] :=
  source_excluded a [8,4,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1848 : Excluded a [8,4,3,1] :=
  source_excluded a [8,4,3,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1849 : Excluded a [8,4,3,2] :=
  source_excluded a [8,4,3,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1850 : Excluded a [8,4,3,5] :=
  source_excluded a [8,4,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1852 : Excluded a [8,4,3,6,0] :=
  predecessor_excluded a [8,4,3,6,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1854 : Excluded a [8,4,3,6,1,0] :=
  source_excluded a [8,4,3,6,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1855 : Excluded a [8,4,3,6,1,2] :=
  source_excluded a [8,4,3,6,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1857 : Excluded a [8,4,3,6,1,7,0] :=
  predecessor_excluded a [8,4,3,6,1,7,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_1859 : Excluded a [8,4,3,6,1,7,2,0] :=
  source_excluded a [8,4,3,6,1,7,2,0] 7 1 0 (by decide) (by decide +kernel)

def b_1861 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 3
  | 3 => 6
  | 4 => 1
  | 5 => 7
  | 6 => 2
  | 7 => 5
  | 8 => 0
  | _ => 0

def cert_1861 : LosingRegion (edgeOf a b_1861) 0 :=
  losingMask a b_1861 0 1212478059916502737390592
    (by decide +kernel) (by decide +kernel)

theorem node_1861 : Excluded a [8,4,3,6,1,7,2,5,0] :=
  losing_excluded a [8,4,3,6,1,7,2,5,0] (by decide) b_1861 (by decide +kernel) 1 0 2 cert_1861 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1861 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212478059916502737390592 1 2; decide +kernel)

theorem node_1860 : Excluded a [8,4,3,6,1,7,2,5] :=
  branch_excluded a [8,4,3,6,1,7,2,5] (by decide)
    (fin9_cases _
      node_1861
      (invalid_excluded a [8,4,3,6,1,7,2,5,1] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,5,2] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,5,6] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,5,8] (by decide +kernel)))

theorem node_1858 : Excluded a [8,4,3,6,1,7,2] :=
  branch_excluded a [8,4,3,6,1,7,2] (by decide)
    (fin9_cases _
      node_1859
      (invalid_excluded a [8,4,3,6,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,4] (by decide +kernel))
      node_1860
      (invalid_excluded a [8,4,3,6,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,2,8] (by decide +kernel)))

theorem node_1862 : Excluded a [8,4,3,6,1,7,5] :=
  source_excluded a [8,4,3,6,1,7,5] 6 0 5 (by decide) (by decide +kernel)

theorem node_1856 : Excluded a [8,4,3,6,1,7] :=
  branch_excluded a [8,4,3,6,1,7] (by decide)
    (fin9_cases _
      node_1857
      (invalid_excluded a [8,4,3,6,1,7,1] (by decide +kernel))
      node_1858
      (invalid_excluded a [8,4,3,6,1,7,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,4] (by decide +kernel))
      node_1862
      (invalid_excluded a [8,4,3,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,7,8] (by decide +kernel)))

theorem node_1853 : Excluded a [8,4,3,6,1] :=
  branch_excluded a [8,4,3,6,1] (by decide)
    (fin9_cases _
      node_1854
      (invalid_excluded a [8,4,3,6,1,1] (by decide +kernel))
      node_1855
      (invalid_excluded a [8,4,3,6,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,6] (by decide +kernel))
      node_1856
      (invalid_excluded a [8,4,3,6,1,8] (by decide +kernel)))

theorem node_1863 : Excluded a [8,4,3,6,2] :=
  source_excluded a [8,4,3,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1864 : Excluded a [8,4,3,6,7] :=
  predecessor_excluded a [8,4,3,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1851 : Excluded a [8,4,3,6] :=
  branch_excluded a [8,4,3,6] (by decide)
    (fin9_cases _
      node_1852
      node_1853
      node_1863
      (invalid_excluded a [8,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,6] (by decide +kernel))
      node_1864
      (invalid_excluded a [8,4,3,6,8] (by decide +kernel)))

theorem node_1866 : Excluded a [8,4,3,7,0] :=
  predecessor_excluded a [8,4,3,7,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1868 : Excluded a [8,4,3,7,1,0] :=
  source_excluded a [8,4,3,7,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1869 : Excluded a [8,4,3,7,1,2] :=
  source_excluded a [8,4,3,7,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1870 : Excluded a [8,4,3,7,1,6] :=
  predecessor_excluded a [8,4,3,7,1,6] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1867 : Excluded a [8,4,3,7,1] :=
  branch_excluded a [8,4,3,7,1] (by decide)
    (fin9_cases _
      node_1868
      (invalid_excluded a [8,4,3,7,1,1] (by decide +kernel))
      node_1869
      (invalid_excluded a [8,4,3,7,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,5] (by decide +kernel))
      node_1870
      (invalid_excluded a [8,4,3,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,8] (by decide +kernel)))

theorem node_1871 : Excluded a [8,4,3,7,2] :=
  source_excluded a [8,4,3,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1873 : Excluded a [8,4,3,7,6,0] :=
  source_excluded a [8,4,3,7,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1874 : Excluded a [8,4,3,7,6,1] :=
  predecessor_excluded a [8,4,3,7,6,1] 0 4 5 1 (by decide) (by decide +kernel)

theorem node_1875 : Excluded a [8,4,3,7,6,2] :=
  source_excluded a [8,4,3,7,6,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1872 : Excluded a [8,4,3,7,6] :=
  branch_excluded a [8,4,3,7,6] (by decide)
    (fin9_cases _
      node_1873
      node_1874
      node_1875
      (invalid_excluded a [8,4,3,7,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,6,8] (by decide +kernel)))

theorem node_1865 : Excluded a [8,4,3,7] :=
  branch_excluded a [8,4,3,7] (by decide)
    (fin9_cases _
      node_1866
      node_1867
      node_1871
      (invalid_excluded a [8,4,3,7,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,5] (by decide +kernel))
      node_1872
      (invalid_excluded a [8,4,3,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,8] (by decide +kernel)))

theorem node_1846 : Excluded a [8,4,3] :=
  branch_excluded a [8,4,3] (by decide)
    (fin9_cases _
      node_1847
      node_1848
      node_1849
      (invalid_excluded a [8,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,4] (by decide +kernel))
      node_1850
      node_1851
      node_1865
      (invalid_excluded a [8,4,3,8] (by decide +kernel)))

theorem node_1876 : Excluded a [8,4,5] :=
  predecessor_excluded a [8,4,5] 0 5 1 2 (by decide) (by decide +kernel)

theorem node_1879 : Excluded a [8,4,6,0,1] :=
  predecessor_excluded a [8,4,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1880 : Excluded a [8,4,6,0,2] :=
  source_excluded a [8,4,6,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1881 : Excluded a [8,4,6,0,3] :=
  source_excluded a [8,4,6,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1883 : Excluded a [8,4,6,0,7,1] :=
  predecessor_excluded a [8,4,6,0,7,1] 0 4 5 1 (by decide) (by decide +kernel)

theorem node_1884 : Excluded a [8,4,6,0,7,2] :=
  predecessor_excluded a [8,4,6,0,7,2] 1 0 5 3 (by decide) (by decide +kernel)

theorem node_1882 : Excluded a [8,4,6,0,7] :=
  branch_excluded a [8,4,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,7,0] (by decide +kernel))
      node_1883
      node_1884
      (invalid_excluded a [8,4,6,0,7,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,8] (by decide +kernel)))

theorem node_1878 : Excluded a [8,4,6,0] :=
  branch_excluded a [8,4,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,0] (by decide +kernel))
      node_1879
      node_1880
      node_1881
      (invalid_excluded a [8,4,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,6] (by decide +kernel))
      node_1882
      (invalid_excluded a [8,4,6,0,8] (by decide +kernel)))

theorem node_1885 : Excluded a [8,4,6,1] :=
  source_excluded a [8,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1886 : Excluded a [8,4,6,2] :=
  source_excluded a [8,4,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1887 : Excluded a [8,4,6,5] :=
  source_excluded a [8,4,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1889 : Excluded a [8,4,6,7,0] :=
  predecessor_excluded a [8,4,6,7,0] 3 0 1 4 (by decide) (by decide +kernel)

def b_1894 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 6
  | 3 => 7
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_1894 : LosingRegion (edgeOf a b_1894) 0 :=
  losingMask a b_1894 0 1285914568141154561295360
    (by decide +kernel) (by decide +kernel)

theorem node_1894 : Excluded a [8,4,6,7,1,0,2,3,5] :=
  losing_excluded a [8,4,6,7,1,0,2,3,5] (by decide) b_1894 (by decide +kernel) 3 0 1 cert_1894 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1894 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1285914568141154561295360 3 1; decide +kernel)

theorem node_1893 : Excluded a [8,4,6,7,1,0,2,3] :=
  branch_excluded a [8,4,6,7,1,0,2,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,7,1,0,2,3,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,3,1] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,3,2] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,3,4] (by decide +kernel))
      node_1894
      (invalid_excluded a [8,4,6,7,1,0,2,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,3,8] (by decide +kernel)))

theorem node_1895 : Excluded a [8,4,6,7,1,0,2,5] :=
  predecessor_excluded a [8,4,6,7,1,0,2,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_1892 : Excluded a [8,4,6,7,1,0,2] :=
  branch_excluded a [8,4,6,7,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,7,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,2] (by decide +kernel))
      node_1893
      (invalid_excluded a [8,4,6,7,1,0,2,4] (by decide +kernel))
      node_1895
      (invalid_excluded a [8,4,6,7,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,2,8] (by decide +kernel)))

theorem node_1896 : Excluded a [8,4,6,7,1,0,3] :=
  source_excluded a [8,4,6,7,1,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1898 : Excluded a [8,4,6,7,1,0,5,2] :=
  predecessor_excluded a [8,4,6,7,1,0,5,2] 0 6 7 2 (by decide) (by decide +kernel)

theorem node_1899 : Excluded a [8,4,6,7,1,0,5,3] :=
  predecessor_excluded a [8,4,6,7,1,0,5,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_1897 : Excluded a [8,4,6,7,1,0,5] :=
  branch_excluded a [8,4,6,7,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,7,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,5,1] (by decide +kernel))
      node_1898
      node_1899
      (invalid_excluded a [8,4,6,7,1,0,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,5,8] (by decide +kernel)))

theorem node_1891 : Excluded a [8,4,6,7,1,0] :=
  branch_excluded a [8,4,6,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,1] (by decide +kernel))
      node_1892
      node_1896
      (invalid_excluded a [8,4,6,7,1,0,4] (by decide +kernel))
      node_1897
      (invalid_excluded a [8,4,6,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,0,8] (by decide +kernel)))

theorem node_1900 : Excluded a [8,4,6,7,1,2] :=
  predecessor_excluded a [8,4,6,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1890 : Excluded a [8,4,6,7,1] :=
  branch_excluded a [8,4,6,7,1] (by decide)
    (fin9_cases _
      node_1891
      (invalid_excluded a [8,4,6,7,1,1] (by decide +kernel))
      node_1900
      (invalid_excluded a [8,4,6,7,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,8] (by decide +kernel)))

theorem node_1901 : Excluded a [8,4,6,7,2] :=
  source_excluded a [8,4,6,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1902 : Excluded a [8,4,6,7,3] :=
  source_excluded a [8,4,6,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1888 : Excluded a [8,4,6,7] :=
  branch_excluded a [8,4,6,7] (by decide)
    (fin9_cases _
      node_1889
      node_1890
      node_1901
      node_1902
      (invalid_excluded a [8,4,6,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,8] (by decide +kernel)))

theorem node_1877 : Excluded a [8,4,6] :=
  branch_excluded a [8,4,6] (by decide)
    (fin9_cases _
      node_1878
      node_1885
      node_1886
      (invalid_excluded a [8,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,4] (by decide +kernel))
      node_1887
      (invalid_excluded a [8,4,6,6] (by decide +kernel))
      node_1888
      (invalid_excluded a [8,4,6,8] (by decide +kernel)))

theorem node_1903 : Excluded a [8,4,7] :=
  predecessor_excluded a [8,4,7] 1 8 2 0 (by decide) (by decide +kernel)

theorem node_1844 : Excluded a [8,4] :=
  branch_excluded a [8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0] (by decide +kernel))
      node_1845
      (invalid_excluded a [8,4,2] (by decide +kernel))
      node_1846
      (invalid_excluded a [8,4,4] (by decide +kernel))
      node_1876
      node_1877
      node_1903
      (invalid_excluded a [8,4,8] (by decide +kernel)))

theorem node_1905 : Excluded a [8,5,1] :=
  source_excluded a [8,5,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1906 : Excluded a [8,5,3] :=
  predecessor_excluded a [8,5,3] 0 3 1 2 (by decide) (by decide +kernel)

theorem node_1908 : Excluded a [8,5,4,0] :=
  source_excluded a [8,5,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1909 : Excluded a [8,5,4,1] :=
  predecessor_excluded a [8,5,4,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1910 : Excluded a [8,5,4,2] :=
  source_excluded a [8,5,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_1912 : Excluded a [8,5,4,6,0] :=
  source_excluded a [8,5,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1913 : Excluded a [8,5,4,6,1] :=
  source_excluded a [8,5,4,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1914 : Excluded a [8,5,4,6,2] :=
  source_excluded a [8,5,4,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1915 : Excluded a [8,5,4,6,3] :=
  source_excluded a [8,5,4,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1916 : Excluded a [8,5,4,6,7] :=
  predecessor_excluded a [8,5,4,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1911 : Excluded a [8,5,4,6] :=
  branch_excluded a [8,5,4,6] (by decide)
    (fin9_cases _
      node_1912
      node_1913
      node_1914
      node_1915
      (invalid_excluded a [8,5,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,4,6,6] (by decide +kernel))
      node_1916
      (invalid_excluded a [8,5,4,6,8] (by decide +kernel)))

theorem node_1918 : Excluded a [8,5,4,7,0] :=
  source_excluded a [8,5,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1919 : Excluded a [8,5,4,7,1] :=
  source_excluded a [8,5,4,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1920 : Excluded a [8,5,4,7,2] :=
  source_excluded a [8,5,4,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1921 : Excluded a [8,5,4,7,3] :=
  source_excluded a [8,5,4,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1923 : Excluded a [8,5,4,7,6,0] :=
  predecessor_excluded a [8,5,4,7,6,0] 3 0 1 5 (by decide) (by decide +kernel)

theorem node_1925 : Excluded a [8,5,4,7,6,1,0] :=
  predecessor_excluded a [8,5,4,7,6,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_1927 : Excluded a [8,5,4,7,6,1,2,0] :=
  source_excluded a [8,5,4,7,6,1,2,0] 7 1 0 (by decide) (by decide +kernel)

def b_1929 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 5
  | 2 => 4
  | 3 => 7
  | 4 => 6
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | 8 => 0
  | _ => 0

def cert_1929 : LosingRegion (edgeOf a b_1929) 0 :=
  losingMask a b_1929 0 1212478056045620377979904
    (by decide +kernel) (by decide +kernel)

theorem node_1929 : Excluded a [8,5,4,7,6,1,2,3,0] :=
  losing_excluded a [8,5,4,7,6,1,2,3,0] (by decide) b_1929 (by decide +kernel) 1 0 2 cert_1929 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1929 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212478056045620377979904 1 2; decide +kernel)

theorem node_1928 : Excluded a [8,5,4,7,6,1,2,3] :=
  branch_excluded a [8,5,4,7,6,1,2,3] (by decide)
    (fin9_cases _
      node_1929
      (invalid_excluded a [8,5,4,7,6,1,2,3,1] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,3,2] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,3,3] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,3,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,3,8] (by decide +kernel)))

theorem node_1926 : Excluded a [8,5,4,7,6,1,2] :=
  branch_excluded a [8,5,4,7,6,1,2] (by decide)
    (fin9_cases _
      node_1927
      (invalid_excluded a [8,5,4,7,6,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,2] (by decide +kernel))
      node_1928
      (invalid_excluded a [8,5,4,7,6,1,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,6] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,2,8] (by decide +kernel)))

theorem node_1930 : Excluded a [8,5,4,7,6,1,3] :=
  source_excluded a [8,5,4,7,6,1,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1924 : Excluded a [8,5,4,7,6,1] :=
  branch_excluded a [8,5,4,7,6,1] (by decide)
    (fin9_cases _
      node_1925
      (invalid_excluded a [8,5,4,7,6,1,1] (by decide +kernel))
      node_1926
      node_1930
      (invalid_excluded a [8,5,4,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,1,8] (by decide +kernel)))

theorem node_1931 : Excluded a [8,5,4,7,6,2] :=
  source_excluded a [8,5,4,7,6,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1922 : Excluded a [8,5,4,7,6] :=
  branch_excluded a [8,5,4,7,6] (by decide)
    (fin9_cases _
      node_1923
      node_1924
      node_1931
      (invalid_excluded a [8,5,4,7,6,3] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,6,8] (by decide +kernel)))

theorem node_1917 : Excluded a [8,5,4,7] :=
  branch_excluded a [8,5,4,7] (by decide)
    (fin9_cases _
      node_1918
      node_1919
      node_1920
      node_1921
      (invalid_excluded a [8,5,4,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,5] (by decide +kernel))
      node_1922
      (invalid_excluded a [8,5,4,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,8] (by decide +kernel)))

theorem node_1907 : Excluded a [8,5,4] :=
  branch_excluded a [8,5,4] (by decide)
    (fin9_cases _
      node_1908
      node_1909
      node_1910
      (invalid_excluded a [8,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,5] (by decide +kernel))
      node_1911
      node_1917
      (invalid_excluded a [8,5,4,8] (by decide +kernel)))

theorem node_1934 : Excluded a [8,5,6,0,1] :=
  source_excluded a [8,5,6,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1935 : Excluded a [8,5,6,0,2] :=
  source_excluded a [8,5,6,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1936 : Excluded a [8,5,6,0,3] :=
  source_excluded a [8,5,6,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1940 : Excluded a [8,5,6,0,7,1,2,3] :=
  predecessor_excluded a [8,5,6,0,7,1,2,3] 0 3 4 7 (by decide) (by decide +kernel)

def b_1942 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 5
  | 2 => 6
  | 3 => 0
  | 4 => 7
  | 5 => 1
  | 6 => 2
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_1942 : LosingRegion (edgeOf a b_1942) 0 :=
  losingMask a b_1942 0 1361693792798287445623808
    (by decide +kernel) (by decide +kernel)

theorem node_1942 : Excluded a [8,5,6,0,7,1,2,4,3] :=
  losing_excluded a [8,5,6,0,7,1,2,4,3] (by decide) b_1942 (by decide +kernel) 4 0 1 cert_1942 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1942 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1361693792798287445623808 4 1; decide +kernel)

theorem node_1941 : Excluded a [8,5,6,0,7,1,2,4] :=
  branch_excluded a [8,5,6,0,7,1,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,0,7,1,2,4,0] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,4,2] (by decide +kernel))
      node_1942
      (invalid_excluded a [8,5,6,0,7,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,4,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,4,8] (by decide +kernel)))

theorem node_1939 : Excluded a [8,5,6,0,7,1,2] :=
  branch_excluded a [8,5,6,0,7,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,0,7,1,2,0] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,2] (by decide +kernel))
      node_1940
      node_1941
      (invalid_excluded a [8,5,6,0,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,2,8] (by decide +kernel)))

theorem node_1944 : Excluded a [8,5,6,0,7,1,3,2] :=
  predecessor_excluded a [8,5,6,0,7,1,3,2] 0 6 7 2 (by decide) (by decide +kernel)

theorem node_1945 : Excluded a [8,5,6,0,7,1,3,4] :=
  predecessor_excluded a [8,5,6,0,7,1,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_1943 : Excluded a [8,5,6,0,7,1,3] :=
  branch_excluded a [8,5,6,0,7,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,0,7,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,3,1] (by decide +kernel))
      node_1944
      (invalid_excluded a [8,5,6,0,7,1,3,3] (by decide +kernel))
      node_1945
      (invalid_excluded a [8,5,6,0,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,3,8] (by decide +kernel)))

theorem node_1946 : Excluded a [8,5,6,0,7,1,4] :=
  source_excluded a [8,5,6,0,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1938 : Excluded a [8,5,6,0,7,1] :=
  branch_excluded a [8,5,6,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,1] (by decide +kernel))
      node_1939
      node_1943
      node_1946
      (invalid_excluded a [8,5,6,0,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,1,8] (by decide +kernel)))

theorem node_1947 : Excluded a [8,5,6,0,7,2] :=
  source_excluded a [8,5,6,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1948 : Excluded a [8,5,6,0,7,4] :=
  source_excluded a [8,5,6,0,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1937 : Excluded a [8,5,6,0,7] :=
  branch_excluded a [8,5,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,0,7,0] (by decide +kernel))
      node_1938
      node_1947
      (invalid_excluded a [8,5,6,0,7,3] (by decide +kernel))
      node_1948
      (invalid_excluded a [8,5,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,8] (by decide +kernel)))

theorem node_1933 : Excluded a [8,5,6,0] :=
  branch_excluded a [8,5,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,0,0] (by decide +kernel))
      node_1934
      node_1935
      node_1936
      (invalid_excluded a [8,5,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,6] (by decide +kernel))
      node_1937
      (invalid_excluded a [8,5,6,0,8] (by decide +kernel)))

theorem node_1949 : Excluded a [8,5,6,1] :=
  predecessor_excluded a [8,5,6,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1951 : Excluded a [8,5,6,2,0] :=
  predecessor_excluded a [8,5,6,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1952 : Excluded a [8,5,6,2,1] :=
  source_excluded a [8,5,6,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1953 : Excluded a [8,5,6,2,3] :=
  source_excluded a [8,5,6,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1955 : Excluded a [8,5,6,2,7,0] :=
  predecessor_excluded a [8,5,6,2,7,0] 3 0 1 5 (by decide) (by decide +kernel)

theorem node_1956 : Excluded a [8,5,6,2,7,1] :=
  predecessor_excluded a [8,5,6,2,7,1] 0 2 5 3 (by decide) (by decide +kernel)

theorem node_1957 : Excluded a [8,5,6,2,7,4] :=
  source_excluded a [8,5,6,2,7,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1954 : Excluded a [8,5,6,2,7] :=
  branch_excluded a [8,5,6,2,7] (by decide)
    (fin9_cases _
      node_1955
      node_1956
      (invalid_excluded a [8,5,6,2,7,2] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,7,3] (by decide +kernel))
      node_1957
      (invalid_excluded a [8,5,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,7,8] (by decide +kernel)))

theorem node_1950 : Excluded a [8,5,6,2] :=
  branch_excluded a [8,5,6,2] (by decide)
    (fin9_cases _
      node_1951
      node_1952
      (invalid_excluded a [8,5,6,2,2] (by decide +kernel))
      node_1953
      (invalid_excluded a [8,5,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,6] (by decide +kernel))
      node_1954
      (invalid_excluded a [8,5,6,2,8] (by decide +kernel)))

theorem node_1960 : Excluded a [8,5,6,7,0,1] :=
  predecessor_excluded a [8,5,6,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1961 : Excluded a [8,5,6,7,0,2] :=
  source_excluded a [8,5,6,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1962 : Excluded a [8,5,6,7,0,4] :=
  source_excluded a [8,5,6,7,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1959 : Excluded a [8,5,6,7,0] :=
  branch_excluded a [8,5,6,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,7,0,0] (by decide +kernel))
      node_1960
      node_1961
      (invalid_excluded a [8,5,6,7,0,3] (by decide +kernel))
      node_1962
      (invalid_excluded a [8,5,6,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,7,0,8] (by decide +kernel)))

theorem node_1963 : Excluded a [8,5,6,7,1] :=
  source_excluded a [8,5,6,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1964 : Excluded a [8,5,6,7,2] :=
  source_excluded a [8,5,6,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1965 : Excluded a [8,5,6,7,3] :=
  source_excluded a [8,5,6,7,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_1958 : Excluded a [8,5,6,7] :=
  branch_excluded a [8,5,6,7] (by decide)
    (fin9_cases _
      node_1959
      node_1963
      node_1964
      node_1965
      (invalid_excluded a [8,5,6,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,6,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,7,8] (by decide +kernel)))

theorem node_1932 : Excluded a [8,5,6] :=
  branch_excluded a [8,5,6] (by decide)
    (fin9_cases _
      node_1933
      node_1949
      node_1950
      (invalid_excluded a [8,5,6,3] (by decide +kernel))
      (invalid_excluded a [8,5,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,6] (by decide +kernel))
      node_1958
      (invalid_excluded a [8,5,6,8] (by decide +kernel)))

theorem node_1966 : Excluded a [8,5,7] :=
  predecessor_excluded a [8,5,7] 1 8 2 0 (by decide) (by decide +kernel)

theorem node_1904 : Excluded a [8,5] :=
  branch_excluded a [8,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0] (by decide +kernel))
      node_1905
      (invalid_excluded a [8,5,2] (by decide +kernel))
      node_1906
      node_1907
      (invalid_excluded a [8,5,5] (by decide +kernel))
      node_1932
      node_1966
      (invalid_excluded a [8,5,8] (by decide +kernel)))

theorem node_1967 : Excluded a [8,6] :=
  predecessor_excluded a [8,6] 2 6 0 1 (by decide) (by decide +kernel)

theorem node_1969 : Excluded a [8,7,1] :=
  source_excluded a [8,7,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1971 : Excluded a [8,7,3,0] :=
  source_excluded a [8,7,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1972 : Excluded a [8,7,3,1] :=
  predecessor_excluded a [8,7,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_1974 : Excluded a [8,7,3,2,0] :=
  predecessor_excluded a [8,7,3,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1976 : Excluded a [8,7,3,2,1,0] :=
  source_excluded a [8,7,3,2,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1977 : Excluded a [8,7,3,2,1,4] :=
  source_excluded a [8,7,3,2,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1979 : Excluded a [8,7,3,2,1,6,0] :=
  predecessor_excluded a [8,7,3,2,1,6,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_1980 : Excluded a [8,7,3,2,1,6,4] :=
  predecessor_excluded a [8,7,3,2,1,6,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1982 : Excluded a [8,7,3,2,1,6,5,0] :=
  source_excluded a [8,7,3,2,1,6,5,0] 7 1 0 (by decide) (by decide +kernel)

def b_1984 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 6
  | 6 => 5
  | 7 => 4
  | 8 => 0
  | _ => 0

def cert_1984 : LosingRegion (edgeOf a b_1984) 0 :=
  losingMask a b_1984 0 1212485016618887703170048
    (by decide +kernel) (by decide +kernel)

theorem node_1984 : Excluded a [8,7,3,2,1,6,5,4,0] :=
  losing_excluded a [8,7,3,2,1,6,5,4,0] (by decide) b_1984 (by decide +kernel) 1 0 2 cert_1984 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1984 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212485016618887703170048 1 2; decide +kernel)

theorem node_1983 : Excluded a [8,7,3,2,1,6,5,4] :=
  branch_excluded a [8,7,3,2,1,6,5,4] (by decide)
    (fin9_cases _
      node_1984
      (invalid_excluded a [8,7,3,2,1,6,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,4,8] (by decide +kernel)))

theorem node_1981 : Excluded a [8,7,3,2,1,6,5] :=
  branch_excluded a [8,7,3,2,1,6,5] (by decide)
    (fin9_cases _
      node_1982
      (invalid_excluded a [8,7,3,2,1,6,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,3] (by decide +kernel))
      node_1983
      (invalid_excluded a [8,7,3,2,1,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,5,8] (by decide +kernel)))

theorem node_1978 : Excluded a [8,7,3,2,1,6] :=
  branch_excluded a [8,7,3,2,1,6] (by decide)
    (fin9_cases _
      node_1979
      (invalid_excluded a [8,7,3,2,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,3] (by decide +kernel))
      node_1980
      node_1981
      (invalid_excluded a [8,7,3,2,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6,8] (by decide +kernel)))

theorem node_1975 : Excluded a [8,7,3,2,1] :=
  branch_excluded a [8,7,3,2,1] (by decide)
    (fin9_cases _
      node_1976
      (invalid_excluded a [8,7,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,3] (by decide +kernel))
      node_1977
      (invalid_excluded a [8,7,3,2,1,5] (by decide +kernel))
      node_1978
      (invalid_excluded a [8,7,3,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,8] (by decide +kernel)))

theorem node_1986 : Excluded a [8,7,3,2,6,0] :=
  source_excluded a [8,7,3,2,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1987 : Excluded a [8,7,3,2,6,1] :=
  predecessor_excluded a [8,7,3,2,6,1] 0 2 5 3 (by decide) (by decide +kernel)

theorem node_1988 : Excluded a [8,7,3,2,6,4] :=
  source_excluded a [8,7,3,2,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1985 : Excluded a [8,7,3,2,6] :=
  branch_excluded a [8,7,3,2,6] (by decide)
    (fin9_cases _
      node_1986
      node_1987
      (invalid_excluded a [8,7,3,2,6,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,6,3] (by decide +kernel))
      node_1988
      (invalid_excluded a [8,7,3,2,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,6,8] (by decide +kernel)))

theorem node_1973 : Excluded a [8,7,3,2] :=
  branch_excluded a [8,7,3,2] (by decide)
    (fin9_cases _
      node_1974
      node_1975
      (invalid_excluded a [8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,4] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,5] (by decide +kernel))
      node_1985
      (invalid_excluded a [8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,8] (by decide +kernel)))

theorem node_1989 : Excluded a [8,7,3,5] :=
  source_excluded a [8,7,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1992 : Excluded a [8,7,3,6,0,1] :=
  predecessor_excluded a [8,7,3,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1993 : Excluded a [8,7,3,6,0,2] :=
  source_excluded a [8,7,3,6,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1994 : Excluded a [8,7,3,6,0,4] :=
  source_excluded a [8,7,3,6,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1991 : Excluded a [8,7,3,6,0] :=
  branch_excluded a [8,7,3,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,3,6,0,0] (by decide +kernel))
      node_1992
      node_1993
      (invalid_excluded a [8,7,3,6,0,3] (by decide +kernel))
      node_1994
      (invalid_excluded a [8,7,3,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,0,8] (by decide +kernel)))

theorem node_1996 : Excluded a [8,7,3,6,1,0] :=
  source_excluded a [8,7,3,6,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1997 : Excluded a [8,7,3,6,1,2] :=
  source_excluded a [8,7,3,6,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1998 : Excluded a [8,7,3,6,1,4] :=
  source_excluded a [8,7,3,6,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_1995 : Excluded a [8,7,3,6,1] :=
  branch_excluded a [8,7,3,6,1] (by decide)
    (fin9_cases _
      node_1996
      (invalid_excluded a [8,7,3,6,1,1] (by decide +kernel))
      node_1997
      (invalid_excluded a [8,7,3,6,1,3] (by decide +kernel))
      node_1998
      (invalid_excluded a [8,7,3,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,1,8] (by decide +kernel)))

theorem node_1999 : Excluded a [8,7,3,6,2] :=
  predecessor_excluded a [8,7,3,6,2] 0 3 4 2 (by decide) (by decide +kernel)

theorem node_1990 : Excluded a [8,7,3,6] :=
  branch_excluded a [8,7,3,6] (by decide)
    (fin9_cases _
      node_1991
      node_1995
      node_1999
      (invalid_excluded a [8,7,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,8] (by decide +kernel)))

theorem node_1970 : Excluded a [8,7,3] :=
  branch_excluded a [8,7,3] (by decide)
    (fin9_cases _
      node_1971
      node_1972
      node_1973
      (invalid_excluded a [8,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,4] (by decide +kernel))
      node_1989
      node_1990
      (invalid_excluded a [8,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,8] (by decide +kernel)))

theorem node_2001 : Excluded a [8,7,4,0] :=
  source_excluded a [8,7,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2003 : Excluded a [8,7,4,1,0] :=
  source_excluded a [8,7,4,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2004 : Excluded a [8,7,4,1,2] :=
  predecessor_excluded a [8,7,4,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2005 : Excluded a [8,7,4,1,3] :=
  source_excluded a [8,7,4,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_2007 : Excluded a [8,7,4,1,6,0] :=
  predecessor_excluded a [8,7,4,1,6,0] 2 1 5 3 (by decide) (by decide +kernel)

theorem node_2008 : Excluded a [8,7,4,1,6,2] :=
  predecessor_excluded a [8,7,4,1,6,2] 0 4 5 2 (by decide) (by decide +kernel)

theorem node_2006 : Excluded a [8,7,4,1,6] :=
  branch_excluded a [8,7,4,1,6] (by decide)
    (fin9_cases _
      node_2007
      (invalid_excluded a [8,7,4,1,6,1] (by decide +kernel))
      node_2008
      (invalid_excluded a [8,7,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,6,8] (by decide +kernel)))

theorem node_2002 : Excluded a [8,7,4,1] :=
  branch_excluded a [8,7,4,1] (by decide)
    (fin9_cases _
      node_2003
      (invalid_excluded a [8,7,4,1,1] (by decide +kernel))
      node_2004
      node_2005
      (invalid_excluded a [8,7,4,1,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,5] (by decide +kernel))
      node_2006
      (invalid_excluded a [8,7,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,8] (by decide +kernel)))

theorem node_2009 : Excluded a [8,7,4,2] :=
  source_excluded a [8,7,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_2010 : Excluded a [8,7,4,5] :=
  source_excluded a [8,7,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2012 : Excluded a [8,7,4,6,0] :=
  source_excluded a [8,7,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2013 : Excluded a [8,7,4,6,1] :=
  predecessor_excluded a [8,7,4,6,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_2015 : Excluded a [8,7,4,6,2,0] :=
  predecessor_excluded a [8,7,4,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_2017 : Excluded a [8,7,4,6,2,1,0] :=
  predecessor_excluded a [8,7,4,6,2,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2019 : Excluded a [8,7,4,6,2,1,3,0] :=
  source_excluded a [8,7,4,6,2,1,3,0] 7 1 0 (by decide) (by decide +kernel)

def b_2021 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 4
  | 3 => 6
  | 4 => 2
  | 5 => 1
  | 6 => 3
  | 7 => 5
  | 8 => 0
  | _ => 0

def cert_2021 : LosingRegion (edgeOf a b_2021) 0 :=
  losingMask a b_2021 0 1212485016336800827837440
    (by decide +kernel) (by decide +kernel)

theorem node_2021 : Excluded a [8,7,4,6,2,1,3,5,0] :=
  losing_excluded a [8,7,4,6,2,1,3,5,0] (by decide) b_2021 (by decide +kernel) 1 0 2 cert_2021 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2021 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212485016336800827837440 1 2; decide +kernel)

theorem node_2020 : Excluded a [8,7,4,6,2,1,3,5] :=
  branch_excluded a [8,7,4,6,2,1,3,5] (by decide)
    (fin9_cases _
      node_2021
      (invalid_excluded a [8,7,4,6,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,5,8] (by decide +kernel)))

theorem node_2018 : Excluded a [8,7,4,6,2,1,3] :=
  branch_excluded a [8,7,4,6,2,1,3] (by decide)
    (fin9_cases _
      node_2019
      (invalid_excluded a [8,7,4,6,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,4] (by decide +kernel))
      node_2020
      (invalid_excluded a [8,7,4,6,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,3,8] (by decide +kernel)))

theorem node_2022 : Excluded a [8,7,4,6,2,1,5] :=
  predecessor_excluded a [8,7,4,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2016 : Excluded a [8,7,4,6,2,1] :=
  branch_excluded a [8,7,4,6,2,1] (by decide)
    (fin9_cases _
      node_2017
      (invalid_excluded a [8,7,4,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,2] (by decide +kernel))
      node_2018
      (invalid_excluded a [8,7,4,6,2,1,4] (by decide +kernel))
      node_2022
      (invalid_excluded a [8,7,4,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,1,8] (by decide +kernel)))

theorem node_2014 : Excluded a [8,7,4,6,2] :=
  branch_excluded a [8,7,4,6,2] (by decide)
    (fin9_cases _
      node_2015
      node_2016
      (invalid_excluded a [8,7,4,6,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,8] (by decide +kernel)))

theorem node_2023 : Excluded a [8,7,4,6,3] :=
  source_excluded a [8,7,4,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_2011 : Excluded a [8,7,4,6] :=
  branch_excluded a [8,7,4,6] (by decide)
    (fin9_cases _
      node_2012
      node_2013
      node_2014
      node_2023
      (invalid_excluded a [8,7,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,8] (by decide +kernel)))

theorem node_2000 : Excluded a [8,7,4] :=
  branch_excluded a [8,7,4] (by decide)
    (fin9_cases _
      node_2001
      node_2002
      node_2009
      (invalid_excluded a [8,7,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,4] (by decide +kernel))
      node_2010
      node_2011
      (invalid_excluded a [8,7,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,8] (by decide +kernel)))

theorem node_2026 : Excluded a [8,7,5,0,1] :=
  predecessor_excluded a [8,7,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2027 : Excluded a [8,7,5,0,2] :=
  source_excluded a [8,7,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2028 : Excluded a [8,7,5,0,3] :=
  source_excluded a [8,7,5,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_2030 : Excluded a [8,7,5,0,6,1] :=
  predecessor_excluded a [8,7,5,0,6,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_2031 : Excluded a [8,7,5,0,6,2] :=
  predecessor_excluded a [8,7,5,0,6,2] 1 0 5 3 (by decide) (by decide +kernel)

theorem node_2032 : Excluded a [8,7,5,0,6,4] :=
  source_excluded a [8,7,5,0,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_2029 : Excluded a [8,7,5,0,6] :=
  branch_excluded a [8,7,5,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,0,6,0] (by decide +kernel))
      node_2030
      node_2031
      (invalid_excluded a [8,7,5,0,6,3] (by decide +kernel))
      node_2032
      (invalid_excluded a [8,7,5,0,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,6,8] (by decide +kernel)))

theorem node_2025 : Excluded a [8,7,5,0] :=
  branch_excluded a [8,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,0,0] (by decide +kernel))
      node_2026
      node_2027
      node_2028
      (invalid_excluded a [8,7,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,5] (by decide +kernel))
      node_2029
      (invalid_excluded a [8,7,5,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,8] (by decide +kernel)))

theorem node_2034 : Excluded a [8,7,5,1,0] :=
  source_excluded a [8,7,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2035 : Excluded a [8,7,5,1,2] :=
  source_excluded a [8,7,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2036 : Excluded a [8,7,5,1,3] :=
  source_excluded a [8,7,5,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_2038 : Excluded a [8,7,5,1,6,0] :=
  source_excluded a [8,7,5,1,6,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2040 : Excluded a [8,7,5,1,6,2,0] :=
  predecessor_excluded a [8,7,5,1,6,2,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2041 : Excluded a [8,7,5,1,6,2,3] :=
  predecessor_excluded a [8,7,5,1,6,2,3] 0 3 4 6 (by decide) (by decide +kernel)

theorem node_2043 : Excluded a [8,7,5,1,6,2,4,0] :=
  source_excluded a [8,7,5,1,6,2,4,0] 7 1 0 (by decide) (by decide +kernel)

def b_2045 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 5
  | 3 => 1
  | 4 => 6
  | 5 => 2
  | 6 => 4
  | 7 => 3
  | 8 => 0
  | _ => 0

def cert_2045 : LosingRegion (edgeOf a b_2045) 0 :=
  losingMask a b_2045 0 1212485015741481853389824
    (by decide +kernel) (by decide +kernel)

theorem node_2045 : Excluded a [8,7,5,1,6,2,4,3,0] :=
  losing_excluded a [8,7,5,1,6,2,4,3,0] (by decide) b_2045 (by decide +kernel) 1 0 2 cert_2045 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2045 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212485015741481853389824 1 2; decide +kernel)

theorem node_2044 : Excluded a [8,7,5,1,6,2,4,3] :=
  branch_excluded a [8,7,5,1,6,2,4,3] (by decide)
    (fin9_cases _
      node_2045
      (invalid_excluded a [8,7,5,1,6,2,4,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,3,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,3,8] (by decide +kernel)))

theorem node_2042 : Excluded a [8,7,5,1,6,2,4] :=
  branch_excluded a [8,7,5,1,6,2,4] (by decide)
    (fin9_cases _
      node_2043
      (invalid_excluded a [8,7,5,1,6,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,2] (by decide +kernel))
      node_2044
      (invalid_excluded a [8,7,5,1,6,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,4,8] (by decide +kernel)))

theorem node_2039 : Excluded a [8,7,5,1,6,2] :=
  branch_excluded a [8,7,5,1,6,2] (by decide)
    (fin9_cases _
      node_2040
      (invalid_excluded a [8,7,5,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,2] (by decide +kernel))
      node_2041
      node_2042
      (invalid_excluded a [8,7,5,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,2,8] (by decide +kernel)))

theorem node_2046 : Excluded a [8,7,5,1,6,4] :=
  source_excluded a [8,7,5,1,6,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_2037 : Excluded a [8,7,5,1,6] :=
  branch_excluded a [8,7,5,1,6] (by decide)
    (fin9_cases _
      node_2038
      (invalid_excluded a [8,7,5,1,6,1] (by decide +kernel))
      node_2039
      (invalid_excluded a [8,7,5,1,6,3] (by decide +kernel))
      node_2046
      (invalid_excluded a [8,7,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,6,8] (by decide +kernel)))

theorem node_2033 : Excluded a [8,7,5,1] :=
  branch_excluded a [8,7,5,1] (by decide)
    (fin9_cases _
      node_2034
      (invalid_excluded a [8,7,5,1,1] (by decide +kernel))
      node_2035
      node_2036
      (invalid_excluded a [8,7,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,5] (by decide +kernel))
      node_2037
      (invalid_excluded a [8,7,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,8] (by decide +kernel)))

theorem node_2047 : Excluded a [8,7,5,2] :=
  predecessor_excluded a [8,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2049 : Excluded a [8,7,5,6,0] :=
  source_excluded a [8,7,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2051 : Excluded a [8,7,5,6,1,0] :=
  source_excluded a [8,7,5,6,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2052 : Excluded a [8,7,5,6,1,2] :=
  predecessor_excluded a [8,7,5,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2053 : Excluded a [8,7,5,6,1,4] :=
  source_excluded a [8,7,5,6,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_2050 : Excluded a [8,7,5,6,1] :=
  branch_excluded a [8,7,5,6,1] (by decide)
    (fin9_cases _
      node_2051
      (invalid_excluded a [8,7,5,6,1,1] (by decide +kernel))
      node_2052
      (invalid_excluded a [8,7,5,6,1,3] (by decide +kernel))
      node_2053
      (invalid_excluded a [8,7,5,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,1,8] (by decide +kernel)))

theorem node_2054 : Excluded a [8,7,5,6,2] :=
  source_excluded a [8,7,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2055 : Excluded a [8,7,5,6,3] :=
  source_excluded a [8,7,5,6,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_2048 : Excluded a [8,7,5,6] :=
  branch_excluded a [8,7,5,6] (by decide)
    (fin9_cases _
      node_2049
      node_2050
      node_2054
      node_2055
      (invalid_excluded a [8,7,5,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,8] (by decide +kernel)))

theorem node_2024 : Excluded a [8,7,5] :=
  branch_excluded a [8,7,5] (by decide)
    (fin9_cases _
      node_2025
      node_2033
      node_2047
      (invalid_excluded a [8,7,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,5] (by decide +kernel))
      node_2048
      (invalid_excluded a [8,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,8] (by decide +kernel)))

theorem node_2058 : Excluded a [8,7,6,0,1] :=
  predecessor_excluded a [8,7,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2062 : Excluded a [8,7,6,0,2,1,3,4] :=
  predecessor_excluded a [8,7,6,0,2,1,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_2064 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 3
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_2064 : LosingRegion (edgeOf a b_2064) 0 :=
  losingMask a b_2064 0 1324551886374561100344320
    (by decide +kernel) (by decide +kernel)

theorem node_2064 : Excluded a [8,7,6,0,2,1,3,5,4] :=
  losing_excluded a [8,7,6,0,2,1,3,5,4] (by decide) b_2064 (by decide +kernel) 1 0 2 cert_2064 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2064 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1324551886374561100344320 1 2; decide +kernel)

theorem node_2063 : Excluded a [8,7,6,0,2,1,3,5] :=
  branch_excluded a [8,7,6,0,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,5,3] (by decide +kernel))
      node_2064
      (invalid_excluded a [8,7,6,0,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,5,8] (by decide +kernel)))

theorem node_2061 : Excluded a [8,7,6,0,2,1,3] :=
  branch_excluded a [8,7,6,0,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,3] (by decide +kernel))
      node_2062
      node_2063
      (invalid_excluded a [8,7,6,0,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,3,8] (by decide +kernel)))

def b_2067 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 4
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_2067 : LosingRegion (edgeOf a b_2067) 0 :=
  losingMask a b_2067 0 2079392365640379800757248
    (by decide +kernel) (by decide +kernel)

theorem node_2067 : Excluded a [8,7,6,0,2,1,4,3,5] :=
  losing_excluded a [8,7,6,0,2,1,4,3,5] (by decide) b_2067 (by decide +kernel) 1 0 4 cert_2067 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2067 1 0 ∧ 4 ≠ 1 ∧ maskRegion 2079392365640379800757248 1 4; decide +kernel)

theorem node_2066 : Excluded a [8,7,6,0,2,1,4,3] :=
  branch_excluded a [8,7,6,0,2,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,2,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,3,4] (by decide +kernel))
      node_2067
      (invalid_excluded a [8,7,6,0,2,1,4,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,3,8] (by decide +kernel)))

theorem node_2068 : Excluded a [8,7,6,0,2,1,4,5] :=
  predecessor_excluded a [8,7,6,0,2,1,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_2065 : Excluded a [8,7,6,0,2,1,4] :=
  branch_excluded a [8,7,6,0,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,2] (by decide +kernel))
      node_2066
      (invalid_excluded a [8,7,6,0,2,1,4,4] (by decide +kernel))
      node_2068
      (invalid_excluded a [8,7,6,0,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,4,8] (by decide +kernel)))

theorem node_2070 : Excluded a [8,7,6,0,2,1,5,3] :=
  predecessor_excluded a [8,7,6,0,2,1,5,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_2072 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_2072 : LosingRegion (edgeOf a b_2072) 0 :=
  losingMask a b_2072 0 1399229206301331944383488
    (by decide +kernel) (by decide +kernel)

theorem node_2072 : Excluded a [8,7,6,0,2,1,5,4,3] :=
  losing_excluded a [8,7,6,0,2,1,5,4,3] (by decide) b_2072 (by decide +kernel) 1 0 4 cert_2072 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2072 1 0 ∧ 4 ≠ 1 ∧ maskRegion 1399229206301331944383488 1 4; decide +kernel)

theorem node_2071 : Excluded a [8,7,6,0,2,1,5,4] :=
  branch_excluded a [8,7,6,0,2,1,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,2,1,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,4,2] (by decide +kernel))
      node_2072
      (invalid_excluded a [8,7,6,0,2,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,4,8] (by decide +kernel)))

theorem node_2069 : Excluded a [8,7,6,0,2,1,5] :=
  branch_excluded a [8,7,6,0,2,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,2,1,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,2] (by decide +kernel))
      node_2070
      node_2071
      (invalid_excluded a [8,7,6,0,2,1,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,5,8] (by decide +kernel)))

theorem node_2060 : Excluded a [8,7,6,0,2,1] :=
  branch_excluded a [8,7,6,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,2] (by decide +kernel))
      node_2061
      node_2065
      node_2069
      (invalid_excluded a [8,7,6,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,1,8] (by decide +kernel)))

theorem node_2073 : Excluded a [8,7,6,0,2,4] :=
  source_excluded a [8,7,6,0,2,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_2059 : Excluded a [8,7,6,0,2] :=
  branch_excluded a [8,7,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,2,0] (by decide +kernel))
      node_2060
      (invalid_excluded a [8,7,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,3] (by decide +kernel))
      node_2073
      (invalid_excluded a [8,7,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,2,8] (by decide +kernel)))

theorem node_2074 : Excluded a [8,7,6,0,3] :=
  source_excluded a [8,7,6,0,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_2057 : Excluded a [8,7,6,0] :=
  branch_excluded a [8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,0] (by decide +kernel))
      node_2058
      node_2059
      node_2074
      (invalid_excluded a [8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,8] (by decide +kernel)))

theorem node_2079 : Excluded a [8,7,6,1,0,2,3,4] :=
  predecessor_excluded a [8,7,6,1,0,2,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_2081 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 3
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_2081 : LosingRegion (edgeOf a b_2081) 0 :=
  losingMask a b_2081 0 1323892703222829306364928
    (by decide +kernel) (by decide +kernel)

theorem node_2081 : Excluded a [8,7,6,1,0,2,3,5,4] :=
  losing_excluded a [8,7,6,1,0,2,3,5,4] (by decide) b_2081 (by decide +kernel) 1 0 5 cert_2081 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2081 1 0 ∧ 5 ≠ 1 ∧ maskRegion 1323892703222829306364928 1 5; decide +kernel)

theorem node_2080 : Excluded a [8,7,6,1,0,2,3,5] :=
  branch_excluded a [8,7,6,1,0,2,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,2,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,5,3] (by decide +kernel))
      node_2081
      (invalid_excluded a [8,7,6,1,0,2,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,5,8] (by decide +kernel)))

theorem node_2078 : Excluded a [8,7,6,1,0,2,3] :=
  branch_excluded a [8,7,6,1,0,2,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,2,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,3] (by decide +kernel))
      node_2079
      node_2080
      (invalid_excluded a [8,7,6,1,0,2,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,3,8] (by decide +kernel)))

def b_2084 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 4
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_2084 : LosingRegion (edgeOf a b_2084) 0 :=
  losingMask a b_2084 0 1437888393451583604542464
    (by decide +kernel) (by decide +kernel)

theorem node_2084 : Excluded a [8,7,6,1,0,2,4,3,5] :=
  losing_excluded a [8,7,6,1,0,2,4,3,5] (by decide) b_2084 (by decide +kernel) 1 0 2 cert_2084 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2084 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1437888393451583604542464 1 2; decide +kernel)

theorem node_2083 : Excluded a [8,7,6,1,0,2,4,3] :=
  branch_excluded a [8,7,6,1,0,2,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,2,4,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,3,4] (by decide +kernel))
      node_2084
      (invalid_excluded a [8,7,6,1,0,2,4,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,3,8] (by decide +kernel)))

theorem node_2085 : Excluded a [8,7,6,1,0,2,4,5] :=
  predecessor_excluded a [8,7,6,1,0,2,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_2082 : Excluded a [8,7,6,1,0,2,4] :=
  branch_excluded a [8,7,6,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,2] (by decide +kernel))
      node_2083
      (invalid_excluded a [8,7,6,1,0,2,4,4] (by decide +kernel))
      node_2085
      (invalid_excluded a [8,7,6,1,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,4,8] (by decide +kernel)))

theorem node_2087 : Excluded a [8,7,6,1,0,2,5,3] :=
  predecessor_excluded a [8,7,6,1,0,2,5,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_2089 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_2089 : LosingRegion (edgeOf a b_2089) 0 :=
  losingMask a b_2089 0 2079245223751881522693120
    (by decide +kernel) (by decide +kernel)

theorem node_2089 : Excluded a [8,7,6,1,0,2,5,4,3] :=
  losing_excluded a [8,7,6,1,0,2,5,4,3] (by decide) b_2089 (by decide +kernel) 1 0 5 cert_2089 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2089 1 0 ∧ 5 ≠ 1 ∧ maskRegion 2079245223751881522693120 1 5; decide +kernel)

theorem node_2088 : Excluded a [8,7,6,1,0,2,5,4] :=
  branch_excluded a [8,7,6,1,0,2,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,2,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,4,2] (by decide +kernel))
      node_2089
      (invalid_excluded a [8,7,6,1,0,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,4,8] (by decide +kernel)))

theorem node_2086 : Excluded a [8,7,6,1,0,2,5] :=
  branch_excluded a [8,7,6,1,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,2,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,2] (by decide +kernel))
      node_2087
      node_2088
      (invalid_excluded a [8,7,6,1,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,5,8] (by decide +kernel)))

theorem node_2077 : Excluded a [8,7,6,1,0,2] :=
  branch_excluded a [8,7,6,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,2] (by decide +kernel))
      node_2078
      node_2082
      node_2086
      (invalid_excluded a [8,7,6,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,2,8] (by decide +kernel)))

theorem node_2090 : Excluded a [8,7,6,1,0,4] :=
  source_excluded a [8,7,6,1,0,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_2076 : Excluded a [8,7,6,1,0] :=
  branch_excluded a [8,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,1] (by decide +kernel))
      node_2077
      (invalid_excluded a [8,7,6,1,0,3] (by decide +kernel))
      node_2090
      (invalid_excluded a [8,7,6,1,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,8] (by decide +kernel)))

theorem node_2091 : Excluded a [8,7,6,1,2] :=
  predecessor_excluded a [8,7,6,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2092 : Excluded a [8,7,6,1,3] :=
  source_excluded a [8,7,6,1,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_2075 : Excluded a [8,7,6,1] :=
  branch_excluded a [8,7,6,1] (by decide)
    (fin9_cases _
      node_2076
      (invalid_excluded a [8,7,6,1,1] (by decide +kernel))
      node_2091
      node_2092
      (invalid_excluded a [8,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,8] (by decide +kernel)))

theorem node_2094 : Excluded a [8,7,6,2,0] :=
  predecessor_excluded a [8,7,6,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2098 : Excluded a [8,7,6,2,1,0,3,4] :=
  predecessor_excluded a [8,7,6,2,1,0,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_2100 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 3
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_2100 : LosingRegion (edgeOf a b_2100) 0 :=
  losingMask a b_2100 0 2079466440567774837216256
    (by decide +kernel) (by decide +kernel)

theorem node_2100 : Excluded a [8,7,6,2,1,0,3,5,4] :=
  losing_excluded a [8,7,6,2,1,0,3,5,4] (by decide) b_2100 (by decide +kernel) 1 0 3 cert_2100 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2100 1 0 ∧ 3 ≠ 1 ∧ maskRegion 2079466440567774837216256 1 3; decide +kernel)

theorem node_2099 : Excluded a [8,7,6,2,1,0,3,5] :=
  branch_excluded a [8,7,6,2,1,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,5,3] (by decide +kernel))
      node_2100
      (invalid_excluded a [8,7,6,2,1,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,5,8] (by decide +kernel)))

theorem node_2097 : Excluded a [8,7,6,2,1,0,3] :=
  branch_excluded a [8,7,6,2,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,3] (by decide +kernel))
      node_2098
      node_2099
      (invalid_excluded a [8,7,6,2,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,3,8] (by decide +kernel)))

def b_2103 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 4
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_2103 : LosingRegion (edgeOf a b_2103) 0 :=
  losingMask a b_2103 0 1437155711837602829046784
    (by decide +kernel) (by decide +kernel)

theorem node_2103 : Excluded a [8,7,6,2,1,0,4,3,5] :=
  losing_excluded a [8,7,6,2,1,0,4,3,5] (by decide) b_2103 (by decide +kernel) 1 0 3 cert_2103 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2103 1 0 ∧ 3 ≠ 1 ∧ maskRegion 1437155711837602829046784 1 3; decide +kernel)

theorem node_2102 : Excluded a [8,7,6,2,1,0,4,3] :=
  branch_excluded a [8,7,6,2,1,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,4,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,3,4] (by decide +kernel))
      node_2103
      (invalid_excluded a [8,7,6,2,1,0,4,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,3,8] (by decide +kernel)))

theorem node_2104 : Excluded a [8,7,6,2,1,0,4,5] :=
  predecessor_excluded a [8,7,6,2,1,0,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_2101 : Excluded a [8,7,6,2,1,0,4] :=
  branch_excluded a [8,7,6,2,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,2] (by decide +kernel))
      node_2102
      (invalid_excluded a [8,7,6,2,1,0,4,4] (by decide +kernel))
      node_2104
      (invalid_excluded a [8,7,6,2,1,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,4,8] (by decide +kernel)))

theorem node_2106 : Excluded a [8,7,6,2,1,0,5,3] :=
  predecessor_excluded a [8,7,6,2,1,0,5,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_2108 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_2108 : LosingRegion (edgeOf a b_2108) 0 :=
  losingMask a b_2108 0 1400109893936387546160128
    (by decide +kernel) (by decide +kernel)

theorem node_2108 : Excluded a [8,7,6,2,1,0,5,4,3] :=
  losing_excluded a [8,7,6,2,1,0,5,4,3] (by decide) b_2108 (by decide +kernel) 1 0 2 cert_2108 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2108 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1400109893936387546160128 1 2; decide +kernel)

theorem node_2107 : Excluded a [8,7,6,2,1,0,5,4] :=
  branch_excluded a [8,7,6,2,1,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,2] (by decide +kernel))
      node_2108
      (invalid_excluded a [8,7,6,2,1,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,8] (by decide +kernel)))

theorem node_2105 : Excluded a [8,7,6,2,1,0,5] :=
  branch_excluded a [8,7,6,2,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,2] (by decide +kernel))
      node_2106
      node_2107
      (invalid_excluded a [8,7,6,2,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,8] (by decide +kernel)))

theorem node_2096 : Excluded a [8,7,6,2,1,0] :=
  branch_excluded a [8,7,6,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,2] (by decide +kernel))
      node_2097
      node_2101
      node_2105
      (invalid_excluded a [8,7,6,2,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,8] (by decide +kernel)))

theorem node_2109 : Excluded a [8,7,6,2,1,4] :=
  source_excluded a [8,7,6,2,1,4] 5 0 3 (by decide) (by decide +kernel)

theorem node_2095 : Excluded a [8,7,6,2,1] :=
  branch_excluded a [8,7,6,2,1] (by decide)
    (fin9_cases _
      node_2096
      (invalid_excluded a [8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3] (by decide +kernel))
      node_2109
      (invalid_excluded a [8,7,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,8] (by decide +kernel)))

theorem node_2110 : Excluded a [8,7,6,2,3] :=
  source_excluded a [8,7,6,2,3] 4 0 5 (by decide) (by decide +kernel)

theorem node_2093 : Excluded a [8,7,6,2] :=
  branch_excluded a [8,7,6,2] (by decide)
    (fin9_cases _
      node_2094
      node_2095
      (invalid_excluded a [8,7,6,2,2] (by decide +kernel))
      node_2110
      (invalid_excluded a [8,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,8] (by decide +kernel)))

theorem node_2111 : Excluded a [8,7,6,5] :=
  source_excluded a [8,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2056 : Excluded a [8,7,6] :=
  branch_excluded a [8,7,6] (by decide)
    (fin9_cases _
      node_2057
      node_2075
      node_2093
      (invalid_excluded a [8,7,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,4] (by decide +kernel))
      node_2111
      (invalid_excluded a [8,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,8] (by decide +kernel)))

theorem node_1968 : Excluded a [8,7] :=
  branch_excluded a [8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0] (by decide +kernel))
      node_1969
      (invalid_excluded a [8,7,2] (by decide +kernel))
      node_1970
      node_2000
      node_2024
      node_2056
      (invalid_excluded a [8,7,7] (by decide +kernel))
      (invalid_excluded a [8,7,8] (by decide +kernel)))

theorem node_1770 : Excluded a [8] :=
  branch_excluded a [8] (by decide)
    (fin9_cases _
      node_1771
      (invalid_excluded a [8,1] (by decide +kernel))
      (invalid_excluded a [8,2] (by decide +kernel))
      node_1772
      node_1844
      node_1904
      node_1967
      node_1968
      (invalid_excluded a [8,8] (by decide +kernel)))

theorem node_1 : Excluded a [] :=
  branch_excluded a [] (by decide)
    (fin9_cases _
      (invalid_excluded a [0] (by decide +kernel))
      (invalid_excluded a [1] (by decide +kernel))
      node_2
      node_3
      node_384
      node_714
      node_1086
      node_1428
      node_1770)

theorem every_second_factor_blocked (b : Assignment 9) (valid : Valid a b) : Blocked a b :=
  node_1 b valid (by intro i h; simp at h)

theorem primary_loopless : ∀ i : Fin 9, a i ≠ i := by decide +kernel

#print axioms every_second_factor_blocked
end Delivery.FiniteExclusion.Cycle3x3x3
