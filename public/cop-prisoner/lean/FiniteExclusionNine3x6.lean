import FiniteExclusionKernel

set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

namespace Delivery.FiniteExclusion.Cycle3x6
open FiniteGame Extremal

def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 3
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
  predecessor_excluded a [3,5,4,6,8,0] 3 0 1 5 (by decide) (by decide +kernel)

def b_22 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 1
  | 6 => 0
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_22 : LosingRegion (edgeOf a b_22) 0 :=
  losingMask a b_22 0 1375445732418851154428928
    (by decide +kernel) (by decide +kernel)

theorem node_22 : Excluded a [3,5,4,6,8,1,0,2,7] :=
  losing_excluded a [3,5,4,6,8,1,0,2,7] (by decide) b_22 (by decide +kernel) 3 0 5 cert_22 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_22 3 0 ∧ 5 ≠ 3 ∧ maskRegion 1375445732418851154428928 3 5; decide +kernel)

theorem node_21 : Excluded a [3,5,4,6,8,1,0,2] :=
  branch_excluded a [3,5,4,6,8,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,6,8,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,2,6] (by decide +kernel))
      node_22
      (invalid_excluded a [3,5,4,6,8,1,0,2,8] (by decide +kernel)))

theorem node_20 : Excluded a [3,5,4,6,8,1,0] :=
  branch_excluded a [3,5,4,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,1] (by decide +kernel))
      node_21
      (invalid_excluded a [3,5,4,6,8,1,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,0,8] (by decide +kernel)))

theorem node_23 : Excluded a [3,5,4,6,8,1,2] :=
  predecessor_excluded a [3,5,4,6,8,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_19 : Excluded a [3,5,4,6,8,1] :=
  branch_excluded a [3,5,4,6,8,1] (by decide)
    (fin9_cases _
      node_20
      (invalid_excluded a [3,5,4,6,8,1,1] (by decide +kernel))
      node_23
      (invalid_excluded a [3,5,4,6,8,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,1,8] (by decide +kernel)))

theorem node_24 : Excluded a [3,5,4,6,8,2] :=
  source_excluded a [3,5,4,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_25 : Excluded a [3,5,4,6,8,7] :=
  source_excluded a [3,5,4,6,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_17 : Excluded a [3,5,4,6,8] :=
  branch_excluded a [3,5,4,6,8] (by decide)
    (fin9_cases _
      node_18
      node_19
      node_24
      (invalid_excluded a [3,5,4,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,6,8,6] (by decide +kernel))
      node_25
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

theorem node_27 : Excluded a [3,5,4,7,0] :=
  source_excluded a [3,5,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_28 : Excluded a [3,5,4,7,1] :=
  source_excluded a [3,5,4,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_29 : Excluded a [3,5,4,7,2] :=
  source_excluded a [3,5,4,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_30 : Excluded a [3,5,4,7,6] :=
  source_excluded a [3,5,4,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_31 : Excluded a [3,5,4,7,8] :=
  predecessor_excluded a [3,5,4,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_26 : Excluded a [3,5,4,7] :=
  branch_excluded a [3,5,4,7] (by decide)
    (fin9_cases _
      node_27
      node_28
      node_29
      (invalid_excluded a [3,5,4,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,7,5] (by decide +kernel))
      node_30
      (invalid_excluded a [3,5,4,7,7] (by decide +kernel))
      node_31)

theorem node_33 : Excluded a [3,5,4,8,0] :=
  source_excluded a [3,5,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_34 : Excluded a [3,5,4,8,1] :=
  source_excluded a [3,5,4,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_35 : Excluded a [3,5,4,8,2] :=
  source_excluded a [3,5,4,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_36 : Excluded a [3,5,4,8,6] :=
  source_excluded a [3,5,4,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_38 : Excluded a [3,5,4,8,7,0] :=
  predecessor_excluded a [3,5,4,8,7,0] 3 0 1 5 (by decide) (by decide +kernel)

def b_42 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 8
  | 4 => 7
  | 5 => 1
  | 6 => 0
  | 7 => 2
  | 8 => 6
  | _ => 0

def cert_42 : LosingRegion (edgeOf a b_42) 0 :=
  losingMask a b_42 0 1361241739482097215603712
    (by decide +kernel) (by decide +kernel)

theorem node_42 : Excluded a [3,5,4,8,7,1,0,2,6] :=
  losing_excluded a [3,5,4,8,7,1,0,2,6] (by decide) b_42 (by decide +kernel) 3 0 1 cert_42 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_42 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1361241739482097215603712 3 1; decide +kernel)

theorem node_41 : Excluded a [3,5,4,8,7,1,0,2] :=
  branch_excluded a [3,5,4,8,7,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,8,7,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,2,5] (by decide +kernel))
      node_42
      (invalid_excluded a [3,5,4,8,7,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,2,8] (by decide +kernel)))

theorem node_43 : Excluded a [3,5,4,8,7,1,0,6] :=
  predecessor_excluded a [3,5,4,8,7,1,0,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_40 : Excluded a [3,5,4,8,7,1,0] :=
  branch_excluded a [3,5,4,8,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,4,8,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,1] (by decide +kernel))
      node_41
      (invalid_excluded a [3,5,4,8,7,1,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,5] (by decide +kernel))
      node_43
      (invalid_excluded a [3,5,4,8,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,0,8] (by decide +kernel)))

theorem node_44 : Excluded a [3,5,4,8,7,1,2] :=
  predecessor_excluded a [3,5,4,8,7,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_39 : Excluded a [3,5,4,8,7,1] :=
  branch_excluded a [3,5,4,8,7,1] (by decide)
    (fin9_cases _
      node_40
      (invalid_excluded a [3,5,4,8,7,1,1] (by decide +kernel))
      node_44
      (invalid_excluded a [3,5,4,8,7,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,1,8] (by decide +kernel)))

theorem node_45 : Excluded a [3,5,4,8,7,2] :=
  source_excluded a [3,5,4,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_37 : Excluded a [3,5,4,8,7] :=
  branch_excluded a [3,5,4,8,7] (by decide)
    (fin9_cases _
      node_38
      node_39
      node_45
      (invalid_excluded a [3,5,4,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,7,8] (by decide +kernel)))

theorem node_32 : Excluded a [3,5,4,8] :=
  branch_excluded a [3,5,4,8] (by decide)
    (fin9_cases _
      node_33
      node_34
      node_35
      (invalid_excluded a [3,5,4,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,4,8,5] (by decide +kernel))
      node_36
      node_37
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
      node_26
      node_32)

theorem node_46 : Excluded a [3,5,6] :=
  predecessor_excluded a [3,5,6] 0 6 1 2 (by decide) (by decide +kernel)

theorem node_49 : Excluded a [3,5,7,0,1] :=
  source_excluded a [3,5,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_50 : Excluded a [3,5,7,0,2] :=
  source_excluded a [3,5,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_51 : Excluded a [3,5,7,0,6] :=
  source_excluded a [3,5,7,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_54 : Excluded a [3,5,7,0,8,1,2] :=
  source_excluded a [3,5,7,0,8,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_55 : Excluded a [3,5,7,0,8,1,4] :=
  predecessor_excluded a [3,5,7,0,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_53 : Excluded a [3,5,7,0,8,1] :=
  branch_excluded a [3,5,7,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,1,1] (by decide +kernel))
      node_54
      (invalid_excluded a [3,5,7,0,8,1,3] (by decide +kernel))
      node_55
      (invalid_excluded a [3,5,7,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,1,8] (by decide +kernel)))

theorem node_56 : Excluded a [3,5,7,0,8,2] :=
  source_excluded a [3,5,7,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_59 : Excluded a [3,5,7,0,8,4,1,2] :=
  predecessor_excluded a [3,5,7,0,8,4,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_61 : Excluded a [3,5,7,0,8,4,1,6,2] :=
  predecessor_excluded a [3,5,7,0,8,4,1,6,2] 1 0 8 3 (by decide) (by decide +kernel)

theorem node_60 : Excluded a [3,5,7,0,8,4,1,6] :=
  branch_excluded a [3,5,7,0,8,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,1] (by decide +kernel))
      node_61
      (invalid_excluded a [3,5,7,0,8,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,8] (by decide +kernel)))

theorem node_58 : Excluded a [3,5,7,0,8,4,1] :=
  branch_excluded a [3,5,7,0,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,1] (by decide +kernel))
      node_59
      (invalid_excluded a [3,5,7,0,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,5] (by decide +kernel))
      node_60
      (invalid_excluded a [3,5,7,0,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,8] (by decide +kernel)))

theorem node_62 : Excluded a [3,5,7,0,8,4,2] :=
  source_excluded a [3,5,7,0,8,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_57 : Excluded a [3,5,7,0,8,4] :=
  branch_excluded a [3,5,7,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,4,0] (by decide +kernel))
      node_58
      node_62
      (invalid_excluded a [3,5,7,0,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,8] (by decide +kernel)))

theorem node_52 : Excluded a [3,5,7,0,8] :=
  branch_excluded a [3,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,0] (by decide +kernel))
      node_53
      node_56
      (invalid_excluded a [3,5,7,0,8,3] (by decide +kernel))
      node_57
      (invalid_excluded a [3,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,8] (by decide +kernel)))

theorem node_48 : Excluded a [3,5,7,0] :=
  branch_excluded a [3,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,0] (by decide +kernel))
      node_49
      node_50
      (invalid_excluded a [3,5,7,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,5] (by decide +kernel))
      node_51
      (invalid_excluded a [3,5,7,0,7] (by decide +kernel))
      node_52)

theorem node_63 : Excluded a [3,5,7,1] :=
  source_excluded a [3,5,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_64 : Excluded a [3,5,7,2] :=
  predecessor_excluded a [3,5,7,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_67 : Excluded a [3,5,7,6,0,1] :=
  predecessor_excluded a [3,5,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_68 : Excluded a [3,5,7,6,0,2] :=
  source_excluded a [3,5,7,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_69 : Excluded a [3,5,7,6,0,4] :=
  source_excluded a [3,5,7,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_72 : Excluded a [3,5,7,6,0,8,1,2] :=
  predecessor_excluded a [3,5,7,6,0,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

def b_74 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 6
  | 4 => 0
  | 5 => 8
  | 6 => 1
  | 7 => 4
  | 8 => 2
  | _ => 0

def cert_74 : LosingRegion (edgeOf a b_74) 0 :=
  losingMask a b_74 0 1228999422837855813241856
    (by decide +kernel) (by decide +kernel)

theorem node_74 : Excluded a [3,5,7,6,0,8,1,4,2] :=
  losing_excluded a [3,5,7,6,0,8,1,4,2] (by decide) b_74 (by decide +kernel) 1 0 2 cert_74 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_74 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1228999422837855813241856 1 2; decide +kernel)

theorem node_73 : Excluded a [3,5,7,6,0,8,1,4] :=
  branch_excluded a [3,5,7,6,0,8,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,0,8,1,4,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,4,1] (by decide +kernel))
      node_74
      (invalid_excluded a [3,5,7,6,0,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,4,8] (by decide +kernel)))

theorem node_71 : Excluded a [3,5,7,6,0,8,1] :=
  branch_excluded a [3,5,7,6,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,1] (by decide +kernel))
      node_72
      (invalid_excluded a [3,5,7,6,0,8,1,3] (by decide +kernel))
      node_73
      (invalid_excluded a [3,5,7,6,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,8] (by decide +kernel)))

theorem node_75 : Excluded a [3,5,7,6,0,8,2] :=
  source_excluded a [3,5,7,6,0,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_76 : Excluded a [3,5,7,6,0,8,4] :=
  source_excluded a [3,5,7,6,0,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_70 : Excluded a [3,5,7,6,0,8] :=
  branch_excluded a [3,5,7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,0,8,0] (by decide +kernel))
      node_71
      node_75
      (invalid_excluded a [3,5,7,6,0,8,3] (by decide +kernel))
      node_76
      (invalid_excluded a [3,5,7,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,8] (by decide +kernel)))

theorem node_66 : Excluded a [3,5,7,6,0] :=
  branch_excluded a [3,5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,0,0] (by decide +kernel))
      node_67
      node_68
      (invalid_excluded a [3,5,7,6,0,3] (by decide +kernel))
      node_69
      (invalid_excluded a [3,5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,7] (by decide +kernel))
      node_70)

theorem node_77 : Excluded a [3,5,7,6,1] :=
  source_excluded a [3,5,7,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_78 : Excluded a [3,5,7,6,2] :=
  source_excluded a [3,5,7,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_80 : Excluded a [3,5,7,6,8,0] :=
  predecessor_excluded a [3,5,7,6,8,0] 3 0 1 5 (by decide) (by decide +kernel)

theorem node_82 : Excluded a [3,5,7,6,8,1,0] :=
  source_excluded a [3,5,7,6,8,1,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_83 : Excluded a [3,5,7,6,8,1,2] :=
  source_excluded a [3,5,7,6,8,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_84 : Excluded a [3,5,7,6,8,1,4] :=
  source_excluded a [3,5,7,6,8,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_81 : Excluded a [3,5,7,6,8,1] :=
  branch_excluded a [3,5,7,6,8,1] (by decide)
    (fin9_cases _
      node_82
      (invalid_excluded a [3,5,7,6,8,1,1] (by decide +kernel))
      node_83
      (invalid_excluded a [3,5,7,6,8,1,3] (by decide +kernel))
      node_84
      (invalid_excluded a [3,5,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,8] (by decide +kernel)))

theorem node_85 : Excluded a [3,5,7,6,8,2] :=
  source_excluded a [3,5,7,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_86 : Excluded a [3,5,7,6,8,4] :=
  source_excluded a [3,5,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_79 : Excluded a [3,5,7,6,8] :=
  branch_excluded a [3,5,7,6,8] (by decide)
    (fin9_cases _
      node_80
      node_81
      node_85
      (invalid_excluded a [3,5,7,6,8,3] (by decide +kernel))
      node_86
      (invalid_excluded a [3,5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,8] (by decide +kernel)))

theorem node_65 : Excluded a [3,5,7,6] :=
  branch_excluded a [3,5,7,6] (by decide)
    (fin9_cases _
      node_66
      node_77
      node_78
      (invalid_excluded a [3,5,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,7] (by decide +kernel))
      node_79)

theorem node_89 : Excluded a [3,5,7,8,0,1] :=
  predecessor_excluded a [3,5,7,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_90 : Excluded a [3,5,7,8,0,2] :=
  source_excluded a [3,5,7,8,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_93 : Excluded a [3,5,7,8,0,4,1,2] :=
  predecessor_excluded a [3,5,7,8,0,4,1,2] 0 2 6 7 (by decide) (by decide +kernel)

def b_95 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 8
  | 4 => 0
  | 5 => 4
  | 6 => 1
  | 7 => 6
  | 8 => 2
  | _ => 0

def cert_95 : LosingRegion (edgeOf a b_95) 0 :=
  losingMask a b_95 0 1212549616004620503614464
    (by decide +kernel) (by decide +kernel)

theorem node_95 : Excluded a [3,5,7,8,0,4,1,6,2] :=
  losing_excluded a [3,5,7,8,0,4,1,6,2] (by decide) b_95 (by decide +kernel) 1 0 8 cert_95 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_95 1 0 ∧ 8 ≠ 1 ∧ maskRegion 1212549616004620503614464 1 8; decide +kernel)

theorem node_94 : Excluded a [3,5,7,8,0,4,1,6] :=
  branch_excluded a [3,5,7,8,0,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,8,0,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,6,1] (by decide +kernel))
      node_95
      (invalid_excluded a [3,5,7,8,0,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,6,8] (by decide +kernel)))

theorem node_92 : Excluded a [3,5,7,8,0,4,1] :=
  branch_excluded a [3,5,7,8,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,8,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,1] (by decide +kernel))
      node_93
      (invalid_excluded a [3,5,7,8,0,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,5] (by decide +kernel))
      node_94
      (invalid_excluded a [3,5,7,8,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,1,8] (by decide +kernel)))

theorem node_96 : Excluded a [3,5,7,8,0,4,2] :=
  source_excluded a [3,5,7,8,0,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_91 : Excluded a [3,5,7,8,0,4] :=
  branch_excluded a [3,5,7,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,8,0,4,0] (by decide +kernel))
      node_92
      node_96
      (invalid_excluded a [3,5,7,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,4,8] (by decide +kernel)))

theorem node_88 : Excluded a [3,5,7,8,0] :=
  branch_excluded a [3,5,7,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,8,0,0] (by decide +kernel))
      node_89
      node_90
      (invalid_excluded a [3,5,7,8,0,3] (by decide +kernel))
      node_91
      (invalid_excluded a [3,5,7,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,0,8] (by decide +kernel)))

theorem node_97 : Excluded a [3,5,7,8,1] :=
  source_excluded a [3,5,7,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_98 : Excluded a [3,5,7,8,2] :=
  source_excluded a [3,5,7,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_99 : Excluded a [3,5,7,8,6] :=
  source_excluded a [3,5,7,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_87 : Excluded a [3,5,7,8] :=
  branch_excluded a [3,5,7,8] (by decide)
    (fin9_cases _
      node_88
      node_97
      node_98
      (invalid_excluded a [3,5,7,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,5] (by decide +kernel))
      node_99
      (invalid_excluded a [3,5,7,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,8,8] (by decide +kernel)))

theorem node_47 : Excluded a [3,5,7] :=
  branch_excluded a [3,5,7] (by decide)
    (fin9_cases _
      node_48
      node_63
      node_64
      (invalid_excluded a [3,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,5] (by decide +kernel))
      node_65
      (invalid_excluded a [3,5,7,7] (by decide +kernel))
      node_87)

theorem node_100 : Excluded a [3,5,8] :=
  predecessor_excluded a [3,5,8] 1 3 2 0 (by decide) (by decide +kernel)

theorem node_6 : Excluded a [3,5] :=
  branch_excluded a [3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,0] (by decide +kernel))
      node_7
      (invalid_excluded a [3,5,2] (by decide +kernel))
      (invalid_excluded a [3,5,3] (by decide +kernel))
      node_8
      (invalid_excluded a [3,5,5] (by decide +kernel))
      node_46
      node_47
      node_100)

theorem node_102 : Excluded a [3,6,1] :=
  source_excluded a [3,6,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_104 : Excluded a [3,6,4,0] :=
  source_excluded a [3,6,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_105 : Excluded a [3,6,4,1] :=
  source_excluded a [3,6,4,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_106 : Excluded a [3,6,4,2] :=
  source_excluded a [3,6,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_107 : Excluded a [3,6,4,5] :=
  source_excluded a [3,6,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_109 : Excluded a [3,6,4,7,0] :=
  source_excluded a [3,6,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_110 : Excluded a [3,6,4,7,1] :=
  predecessor_excluded a [3,6,4,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_112 : Excluded a [3,6,4,7,2,0] :=
  predecessor_excluded a [3,6,4,7,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_113 : Excluded a [3,6,4,7,2,1] :=
  source_excluded a [3,6,4,7,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_115 : Excluded a [3,6,4,7,2,8,0] :=
  predecessor_excluded a [3,6,4,7,2,8,0] 3 0 1 6 (by decide) (by decide +kernel)

theorem node_117 : Excluded a [3,6,4,7,2,8,1,0] :=
  predecessor_excluded a [3,6,4,7,2,8,1,0] 1 3 7 0 (by decide) (by decide +kernel)

theorem node_118 : Excluded a [3,6,4,7,2,8,1,5] :=
  source_excluded a [3,6,4,7,2,8,1,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_116 : Excluded a [3,6,4,7,2,8,1] :=
  branch_excluded a [3,6,4,7,2,8,1] (by decide)
    (fin9_cases _
      node_117
      (invalid_excluded a [3,6,4,7,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,2] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,4] (by decide +kernel))
      node_118
      (invalid_excluded a [3,6,4,7,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,1,8] (by decide +kernel)))

theorem node_119 : Excluded a [3,6,4,7,2,8,5] :=
  predecessor_excluded a [3,6,4,7,2,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_114 : Excluded a [3,6,4,7,2,8] :=
  branch_excluded a [3,6,4,7,2,8] (by decide)
    (fin9_cases _
      node_115
      node_116
      (invalid_excluded a [3,6,4,7,2,8,2] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,4] (by decide +kernel))
      node_119
      (invalid_excluded a [3,6,4,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,8,8] (by decide +kernel)))

theorem node_111 : Excluded a [3,6,4,7,2] :=
  branch_excluded a [3,6,4,7,2] (by decide)
    (fin9_cases _
      node_112
      node_113
      (invalid_excluded a [3,6,4,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,2,7] (by decide +kernel))
      node_114)

theorem node_120 : Excluded a [3,6,4,7,8] :=
  predecessor_excluded a [3,6,4,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_108 : Excluded a [3,6,4,7] :=
  branch_excluded a [3,6,4,7] (by decide)
    (fin9_cases _
      node_109
      node_110
      node_111
      (invalid_excluded a [3,6,4,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,7,7] (by decide +kernel))
      node_120)

theorem node_122 : Excluded a [3,6,4,8,0] :=
  source_excluded a [3,6,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_123 : Excluded a [3,6,4,8,1] :=
  predecessor_excluded a [3,6,4,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_125 : Excluded a [3,6,4,8,2,0] :=
  predecessor_excluded a [3,6,4,8,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_126 : Excluded a [3,6,4,8,2,1] :=
  source_excluded a [3,6,4,8,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_127 : Excluded a [3,6,4,8,2,7] :=
  source_excluded a [3,6,4,8,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_124 : Excluded a [3,6,4,8,2] :=
  branch_excluded a [3,6,4,8,2] (by decide)
    (fin9_cases _
      node_125
      node_126
      (invalid_excluded a [3,6,4,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,2,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,2,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,2,6] (by decide +kernel))
      node_127
      (invalid_excluded a [3,6,4,8,2,8] (by decide +kernel)))

theorem node_130 : Excluded a [3,6,4,8,7,0,1] :=
  predecessor_excluded a [3,6,4,8,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_131 : Excluded a [3,6,4,8,7,0,2] :=
  source_excluded a [3,6,4,8,7,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_132 : Excluded a [3,6,4,8,7,0,5] :=
  source_excluded a [3,6,4,8,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_129 : Excluded a [3,6,4,8,7,0] :=
  branch_excluded a [3,6,4,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,4,8,7,0,0] (by decide +kernel))
      node_130
      node_131
      (invalid_excluded a [3,6,4,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,0,4] (by decide +kernel))
      node_132
      (invalid_excluded a [3,6,4,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,0,8] (by decide +kernel)))

theorem node_133 : Excluded a [3,6,4,8,7,1] :=
  source_excluded a [3,6,4,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_134 : Excluded a [3,6,4,8,7,2] :=
  source_excluded a [3,6,4,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_128 : Excluded a [3,6,4,8,7] :=
  branch_excluded a [3,6,4,8,7] (by decide)
    (fin9_cases _
      node_129
      node_133
      node_134
      (invalid_excluded a [3,6,4,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,7,8] (by decide +kernel)))

theorem node_121 : Excluded a [3,6,4,8] :=
  branch_excluded a [3,6,4,8] (by decide)
    (fin9_cases _
      node_122
      node_123
      node_124
      (invalid_excluded a [3,6,4,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,4] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,4,8,6] (by decide +kernel))
      node_128
      (invalid_excluded a [3,6,4,8,8] (by decide +kernel)))

theorem node_103 : Excluded a [3,6,4] :=
  branch_excluded a [3,6,4] (by decide)
    (fin9_cases _
      node_104
      node_105
      node_106
      (invalid_excluded a [3,6,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,4,4] (by decide +kernel))
      node_107
      (invalid_excluded a [3,6,4,6] (by decide +kernel))
      node_108
      node_121)

theorem node_137 : Excluded a [3,6,5,0,1] :=
  predecessor_excluded a [3,6,5,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_138 : Excluded a [3,6,5,0,2] :=
  source_excluded a [3,6,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_140 : Excluded a [3,6,5,0,7,1] :=
  source_excluded a [3,6,5,0,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_141 : Excluded a [3,6,5,0,7,2] :=
  source_excluded a [3,6,5,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_142 : Excluded a [3,6,5,0,7,4] :=
  predecessor_excluded a [3,6,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_143 : Excluded a [3,6,5,0,7,8] :=
  predecessor_excluded a [3,6,5,0,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_139 : Excluded a [3,6,5,0,7] :=
  branch_excluded a [3,6,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,0,7,0] (by decide +kernel))
      node_140
      node_141
      (invalid_excluded a [3,6,5,0,7,3] (by decide +kernel))
      node_142
      (invalid_excluded a [3,6,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,7,7] (by decide +kernel))
      node_143)

theorem node_145 : Excluded a [3,6,5,0,8,1] :=
  source_excluded a [3,6,5,0,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_146 : Excluded a [3,6,5,0,8,2] :=
  source_excluded a [3,6,5,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_149 : Excluded a [3,6,5,0,8,4,1,2] :=
  predecessor_excluded a [3,6,5,0,8,4,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_148 : Excluded a [3,6,5,0,8,4,1] :=
  branch_excluded a [3,6,5,0,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,0,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,1,1] (by decide +kernel))
      node_149
      (invalid_excluded a [3,6,5,0,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,1,8] (by decide +kernel)))

theorem node_150 : Excluded a [3,6,5,0,8,4,2] :=
  source_excluded a [3,6,5,0,8,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_147 : Excluded a [3,6,5,0,8,4] :=
  branch_excluded a [3,6,5,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,0,8,4,0] (by decide +kernel))
      node_148
      node_150
      (invalid_excluded a [3,6,5,0,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,4,8] (by decide +kernel)))

theorem node_151 : Excluded a [3,6,5,0,8,7] :=
  source_excluded a [3,6,5,0,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_144 : Excluded a [3,6,5,0,8] :=
  branch_excluded a [3,6,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,0,8,0] (by decide +kernel))
      node_145
      node_146
      (invalid_excluded a [3,6,5,0,8,3] (by decide +kernel))
      node_147
      (invalid_excluded a [3,6,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,6] (by decide +kernel))
      node_151
      (invalid_excluded a [3,6,5,0,8,8] (by decide +kernel)))

theorem node_136 : Excluded a [3,6,5,0] :=
  branch_excluded a [3,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,0,0] (by decide +kernel))
      node_137
      node_138
      (invalid_excluded a [3,6,5,0,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,6] (by decide +kernel))
      node_139
      node_144)

theorem node_152 : Excluded a [3,6,5,1] :=
  source_excluded a [3,6,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_153 : Excluded a [3,6,5,2] :=
  predecessor_excluded a [3,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_155 : Excluded a [3,6,5,7,0] :=
  source_excluded a [3,6,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_156 : Excluded a [3,6,5,7,1] :=
  predecessor_excluded a [3,6,5,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_157 : Excluded a [3,6,5,7,2] :=
  source_excluded a [3,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_158 : Excluded a [3,6,5,7,8] :=
  predecessor_excluded a [3,6,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_154 : Excluded a [3,6,5,7] :=
  branch_excluded a [3,6,5,7] (by decide)
    (fin9_cases _
      node_155
      node_156
      node_157
      (invalid_excluded a [3,6,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,7] (by decide +kernel))
      node_158)

theorem node_160 : Excluded a [3,6,5,8,0] :=
  source_excluded a [3,6,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_161 : Excluded a [3,6,5,8,1] :=
  predecessor_excluded a [3,6,5,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_162 : Excluded a [3,6,5,8,2] :=
  source_excluded a [3,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_164 : Excluded a [3,6,5,8,7,0] :=
  source_excluded a [3,6,5,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_165 : Excluded a [3,6,5,8,7,1] :=
  source_excluded a [3,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_166 : Excluded a [3,6,5,8,7,2] :=
  source_excluded a [3,6,5,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_167 : Excluded a [3,6,5,8,7,4] :=
  predecessor_excluded a [3,6,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_163 : Excluded a [3,6,5,8,7] :=
  branch_excluded a [3,6,5,8,7] (by decide)
    (fin9_cases _
      node_164
      node_165
      node_166
      (invalid_excluded a [3,6,5,8,7,3] (by decide +kernel))
      node_167
      (invalid_excluded a [3,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,8] (by decide +kernel)))

theorem node_159 : Excluded a [3,6,5,8] :=
  branch_excluded a [3,6,5,8] (by decide)
    (fin9_cases _
      node_160
      node_161
      node_162
      (invalid_excluded a [3,6,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,6] (by decide +kernel))
      node_163
      (invalid_excluded a [3,6,5,8,8] (by decide +kernel)))

theorem node_135 : Excluded a [3,6,5] :=
  branch_excluded a [3,6,5] (by decide)
    (fin9_cases _
      node_136
      node_152
      node_153
      (invalid_excluded a [3,6,5,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,6] (by decide +kernel))
      node_154
      node_159)

theorem node_168 : Excluded a [3,6,7] :=
  predecessor_excluded a [3,6,7] 0 7 1 2 (by decide) (by decide +kernel)

theorem node_169 : Excluded a [3,6,8] :=
  predecessor_excluded a [3,6,8] 1 3 2 0 (by decide) (by decide +kernel)

theorem node_101 : Excluded a [3,6] :=
  branch_excluded a [3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,0] (by decide +kernel))
      node_102
      (invalid_excluded a [3,6,2] (by decide +kernel))
      (invalid_excluded a [3,6,3] (by decide +kernel))
      node_103
      node_135
      (invalid_excluded a [3,6,6] (by decide +kernel))
      node_168
      node_169)

theorem node_171 : Excluded a [3,7,1] :=
  source_excluded a [3,7,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_173 : Excluded a [3,7,4,0] :=
  source_excluded a [3,7,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_174 : Excluded a [3,7,4,1] :=
  source_excluded a [3,7,4,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_175 : Excluded a [3,7,4,2] :=
  source_excluded a [3,7,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_176 : Excluded a [3,7,4,5] :=
  source_excluded a [3,7,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_178 : Excluded a [3,7,4,6,0] :=
  source_excluded a [3,7,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_179 : Excluded a [3,7,4,6,1] :=
  predecessor_excluded a [3,7,4,6,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_181 : Excluded a [3,7,4,6,2,0] :=
  predecessor_excluded a [3,7,4,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_182 : Excluded a [3,7,4,6,2,1] :=
  predecessor_excluded a [3,7,4,6,2,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_185 : Excluded a [3,7,4,6,2,8,0,1] :=
  predecessor_excluded a [3,7,4,6,2,8,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_186 : Excluded a [3,7,4,6,2,8,0,5] :=
  source_excluded a [3,7,4,6,2,8,0,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_184 : Excluded a [3,7,4,6,2,8,0] :=
  branch_excluded a [3,7,4,6,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,4,6,2,8,0,0] (by decide +kernel))
      node_185
      (invalid_excluded a [3,7,4,6,2,8,0,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,8,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,8,0,4] (by decide +kernel))
      node_186
      (invalid_excluded a [3,7,4,6,2,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,8,0,8] (by decide +kernel)))

theorem node_187 : Excluded a [3,7,4,6,2,8,1] :=
  source_excluded a [3,7,4,6,2,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_188 : Excluded a [3,7,4,6,2,8,5] :=
  predecessor_excluded a [3,7,4,6,2,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_183 : Excluded a [3,7,4,6,2,8] :=
  branch_excluded a [3,7,4,6,2,8] (by decide)
    (fin9_cases _
      node_184
      node_187
      (invalid_excluded a [3,7,4,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,8,4] (by decide +kernel))
      node_188
      (invalid_excluded a [3,7,4,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,8,8] (by decide +kernel)))

theorem node_180 : Excluded a [3,7,4,6,2] :=
  branch_excluded a [3,7,4,6,2] (by decide)
    (fin9_cases _
      node_181
      node_182
      (invalid_excluded a [3,7,4,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,2,7] (by decide +kernel))
      node_183)

theorem node_191 : Excluded a [3,7,4,6,8,0,1] :=
  source_excluded a [3,7,4,6,8,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_192 : Excluded a [3,7,4,6,8,0,2] :=
  source_excluded a [3,7,4,6,8,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_193 : Excluded a [3,7,4,6,8,0,5] :=
  predecessor_excluded a [3,7,4,6,8,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_190 : Excluded a [3,7,4,6,8,0] :=
  branch_excluded a [3,7,4,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,4,6,8,0,0] (by decide +kernel))
      node_191
      node_192
      (invalid_excluded a [3,7,4,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,0,4] (by decide +kernel))
      node_193
      (invalid_excluded a [3,7,4,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,0,8] (by decide +kernel)))

theorem node_194 : Excluded a [3,7,4,6,8,1] :=
  predecessor_excluded a [3,7,4,6,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_196 : Excluded a [3,7,4,6,8,2,0] :=
  predecessor_excluded a [3,7,4,6,8,2,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_197 : Excluded a [3,7,4,6,8,2,1] :=
  source_excluded a [3,7,4,6,8,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_198 : Excluded a [3,7,4,6,8,2,5] :=
  predecessor_excluded a [3,7,4,6,8,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_195 : Excluded a [3,7,4,6,8,2] :=
  branch_excluded a [3,7,4,6,8,2] (by decide)
    (fin9_cases _
      node_196
      node_197
      (invalid_excluded a [3,7,4,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,2,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,2,4] (by decide +kernel))
      node_198
      (invalid_excluded a [3,7,4,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,2,8] (by decide +kernel)))

theorem node_189 : Excluded a [3,7,4,6,8] :=
  branch_excluded a [3,7,4,6,8] (by decide)
    (fin9_cases _
      node_190
      node_194
      node_195
      (invalid_excluded a [3,7,4,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,8,8] (by decide +kernel)))

theorem node_177 : Excluded a [3,7,4,6] :=
  branch_excluded a [3,7,4,6] (by decide)
    (fin9_cases _
      node_178
      node_179
      node_180
      (invalid_excluded a [3,7,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,6,7] (by decide +kernel))
      node_189)

theorem node_200 : Excluded a [3,7,4,8,0] :=
  source_excluded a [3,7,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_201 : Excluded a [3,7,4,8,1] :=
  predecessor_excluded a [3,7,4,8,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_203 : Excluded a [3,7,4,8,2,0] :=
  predecessor_excluded a [3,7,4,8,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_204 : Excluded a [3,7,4,8,2,1] :=
  predecessor_excluded a [3,7,4,8,2,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_202 : Excluded a [3,7,4,8,2] :=
  branch_excluded a [3,7,4,8,2] (by decide)
    (fin9_cases _
      node_203
      node_204
      (invalid_excluded a [3,7,4,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,2,8] (by decide +kernel)))

theorem node_205 : Excluded a [3,7,4,8,6] :=
  source_excluded a [3,7,4,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_199 : Excluded a [3,7,4,8] :=
  branch_excluded a [3,7,4,8] (by decide)
    (fin9_cases _
      node_200
      node_201
      node_202
      (invalid_excluded a [3,7,4,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,5] (by decide +kernel))
      node_205
      (invalid_excluded a [3,7,4,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,4,8,8] (by decide +kernel)))

theorem node_172 : Excluded a [3,7,4] :=
  branch_excluded a [3,7,4] (by decide)
    (fin9_cases _
      node_173
      node_174
      node_175
      (invalid_excluded a [3,7,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,4,4] (by decide +kernel))
      node_176
      node_177
      (invalid_excluded a [3,7,4,7] (by decide +kernel))
      node_199)

theorem node_208 : Excluded a [3,7,5,0,1] :=
  predecessor_excluded a [3,7,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_209 : Excluded a [3,7,5,0,2] :=
  source_excluded a [3,7,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_210 : Excluded a [3,7,5,0,6] :=
  source_excluded a [3,7,5,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_212 : Excluded a [3,7,5,0,8,1] :=
  predecessor_excluded a [3,7,5,0,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_214 : Excluded a [3,7,5,0,8,2,1] :=
  source_excluded a [3,7,5,0,8,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_215 : Excluded a [3,7,5,0,8,2,4] :=
  predecessor_excluded a [3,7,5,0,8,2,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_213 : Excluded a [3,7,5,0,8,2] :=
  branch_excluded a [3,7,5,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,0,8,2,0] (by decide +kernel))
      node_214
      (invalid_excluded a [3,7,5,0,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,2,3] (by decide +kernel))
      node_215
      (invalid_excluded a [3,7,5,0,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,2,8] (by decide +kernel)))

theorem node_217 : Excluded a [3,7,5,0,8,4,1] :=
  source_excluded a [3,7,5,0,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_218 : Excluded a [3,7,5,0,8,4,2] :=
  source_excluded a [3,7,5,0,8,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_216 : Excluded a [3,7,5,0,8,4] :=
  branch_excluded a [3,7,5,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,0,8,4,0] (by decide +kernel))
      node_217
      node_218
      (invalid_excluded a [3,7,5,0,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,4,8] (by decide +kernel)))

theorem node_211 : Excluded a [3,7,5,0,8] :=
  branch_excluded a [3,7,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,0,8,0] (by decide +kernel))
      node_212
      node_213
      (invalid_excluded a [3,7,5,0,8,3] (by decide +kernel))
      node_216
      (invalid_excluded a [3,7,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,8] (by decide +kernel)))

theorem node_207 : Excluded a [3,7,5,0] :=
  branch_excluded a [3,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,0,0] (by decide +kernel))
      node_208
      node_209
      (invalid_excluded a [3,7,5,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,5] (by decide +kernel))
      node_210
      (invalid_excluded a [3,7,5,0,7] (by decide +kernel))
      node_211)

theorem node_219 : Excluded a [3,7,5,1] :=
  source_excluded a [3,7,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_220 : Excluded a [3,7,5,2] :=
  predecessor_excluded a [3,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_222 : Excluded a [3,7,5,6,0] :=
  source_excluded a [3,7,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_224 : Excluded a [3,7,5,6,1,0] :=
  source_excluded a [3,7,5,6,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_225 : Excluded a [3,7,5,6,1,2] :=
  predecessor_excluded a [3,7,5,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_226 : Excluded a [3,7,5,6,1,4] :=
  source_excluded a [3,7,5,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_229 : Excluded a [3,7,5,6,1,8,0,2] :=
  source_excluded a [3,7,5,6,1,8,0,2] 1 0 7 (by decide) (by decide +kernel)

def b_231 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 5
  | 3 => 6
  | 4 => 1
  | 5 => 8
  | 6 => 0
  | 7 => 4
  | 8 => 2
  | _ => 0

def cert_231 : LosingRegion (edgeOf a b_231) 0 :=
  losingMask a b_231 0 1231708702596643767323648
    (by decide +kernel) (by decide +kernel)

theorem node_231 : Excluded a [3,7,5,6,1,8,0,4,2] :=
  losing_excluded a [3,7,5,6,1,8,0,4,2] (by decide) b_231 (by decide +kernel) 1 0 2 cert_231 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_231 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1231708702596643767323648 1 2; decide +kernel)

theorem node_230 : Excluded a [3,7,5,6,1,8,0,4] :=
  branch_excluded a [3,7,5,6,1,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,6,1,8,0,4,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,4,1] (by decide +kernel))
      node_231
      (invalid_excluded a [3,7,5,6,1,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,4,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,4,8] (by decide +kernel)))

theorem node_228 : Excluded a [3,7,5,6,1,8,0] :=
  branch_excluded a [3,7,5,6,1,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,6,1,8,0,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,1] (by decide +kernel))
      node_229
      (invalid_excluded a [3,7,5,6,1,8,0,3] (by decide +kernel))
      node_230
      (invalid_excluded a [3,7,5,6,1,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,0,8] (by decide +kernel)))

theorem node_232 : Excluded a [3,7,5,6,1,8,2] :=
  source_excluded a [3,7,5,6,1,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_233 : Excluded a [3,7,5,6,1,8,4] :=
  source_excluded a [3,7,5,6,1,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_227 : Excluded a [3,7,5,6,1,8] :=
  branch_excluded a [3,7,5,6,1,8] (by decide)
    (fin9_cases _
      node_228
      (invalid_excluded a [3,7,5,6,1,8,1] (by decide +kernel))
      node_232
      (invalid_excluded a [3,7,5,6,1,8,3] (by decide +kernel))
      node_233
      (invalid_excluded a [3,7,5,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,8,8] (by decide +kernel)))

theorem node_223 : Excluded a [3,7,5,6,1] :=
  branch_excluded a [3,7,5,6,1] (by decide)
    (fin9_cases _
      node_224
      (invalid_excluded a [3,7,5,6,1,1] (by decide +kernel))
      node_225
      (invalid_excluded a [3,7,5,6,1,3] (by decide +kernel))
      node_226
      (invalid_excluded a [3,7,5,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,1,7] (by decide +kernel))
      node_227)

theorem node_234 : Excluded a [3,7,5,6,2] :=
  source_excluded a [3,7,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_236 : Excluded a [3,7,5,6,8,0] :=
  source_excluded a [3,7,5,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_237 : Excluded a [3,7,5,6,8,1] :=
  predecessor_excluded a [3,7,5,6,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_239 : Excluded a [3,7,5,6,8,2,0] :=
  predecessor_excluded a [3,7,5,6,8,2,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_240 : Excluded a [3,7,5,6,8,2,1] :=
  source_excluded a [3,7,5,6,8,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_241 : Excluded a [3,7,5,6,8,2,4] :=
  source_excluded a [3,7,5,6,8,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_238 : Excluded a [3,7,5,6,8,2] :=
  branch_excluded a [3,7,5,6,8,2] (by decide)
    (fin9_cases _
      node_239
      node_240
      (invalid_excluded a [3,7,5,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,8,2,3] (by decide +kernel))
      node_241
      (invalid_excluded a [3,7,5,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,8,2,8] (by decide +kernel)))

theorem node_242 : Excluded a [3,7,5,6,8,4] :=
  source_excluded a [3,7,5,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_235 : Excluded a [3,7,5,6,8] :=
  branch_excluded a [3,7,5,6,8] (by decide)
    (fin9_cases _
      node_236
      node_237
      node_238
      (invalid_excluded a [3,7,5,6,8,3] (by decide +kernel))
      node_242
      (invalid_excluded a [3,7,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,8,8] (by decide +kernel)))

theorem node_221 : Excluded a [3,7,5,6] :=
  branch_excluded a [3,7,5,6] (by decide)
    (fin9_cases _
      node_222
      node_223
      node_234
      (invalid_excluded a [3,7,5,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,6,7] (by decide +kernel))
      node_235)

theorem node_244 : Excluded a [3,7,5,8,0] :=
  source_excluded a [3,7,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_246 : Excluded a [3,7,5,8,1,0] :=
  source_excluded a [3,7,5,8,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_247 : Excluded a [3,7,5,8,1,2] :=
  predecessor_excluded a [3,7,5,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_250 : Excluded a [3,7,5,8,1,4,0,2] :=
  source_excluded a [3,7,5,8,1,4,0,2] 1 0 7 (by decide) (by decide +kernel)

def b_252 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 5
  | 3 => 8
  | 4 => 1
  | 5 => 4
  | 6 => 0
  | 7 => 6
  | 8 => 2
  | _ => 0

def cert_252 : LosingRegion (edgeOf a b_252) 3 :=
  losingMask a b_252 3 1210107572054780672050177
    (by decide +kernel) (by decide +kernel)

theorem node_252 : Excluded a [3,7,5,8,1,4,0,6,2] :=
  losing_excluded a [3,7,5,8,1,4,0,6,2] (by decide) b_252 (by decide +kernel) 1 3 6 cert_252 (by change 1 ≠ 3 ∧ ¬ edgeOf a b_252 1 3 ∧ 6 ≠ 1 ∧ maskRegion 1210107572054780672050177 1 6; decide +kernel)

theorem node_251 : Excluded a [3,7,5,8,1,4,0,6] :=
  branch_excluded a [3,7,5,8,1,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,4,0,6,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,6,1] (by decide +kernel))
      node_252
      (invalid_excluded a [3,7,5,8,1,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,6,8] (by decide +kernel)))

theorem node_249 : Excluded a [3,7,5,8,1,4,0] :=
  branch_excluded a [3,7,5,8,1,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,4,0,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,1] (by decide +kernel))
      node_250
      (invalid_excluded a [3,7,5,8,1,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,5] (by decide +kernel))
      node_251
      (invalid_excluded a [3,7,5,8,1,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,0,8] (by decide +kernel)))

theorem node_253 : Excluded a [3,7,5,8,1,4,2] :=
  source_excluded a [3,7,5,8,1,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_248 : Excluded a [3,7,5,8,1,4] :=
  branch_excluded a [3,7,5,8,1,4] (by decide)
    (fin9_cases _
      node_249
      (invalid_excluded a [3,7,5,8,1,4,1] (by decide +kernel))
      node_253
      (invalid_excluded a [3,7,5,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,4,8] (by decide +kernel)))

theorem node_245 : Excluded a [3,7,5,8,1] :=
  branch_excluded a [3,7,5,8,1] (by decide)
    (fin9_cases _
      node_246
      (invalid_excluded a [3,7,5,8,1,1] (by decide +kernel))
      node_247
      (invalid_excluded a [3,7,5,8,1,3] (by decide +kernel))
      node_248
      (invalid_excluded a [3,7,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,8] (by decide +kernel)))

theorem node_254 : Excluded a [3,7,5,8,2] :=
  source_excluded a [3,7,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_255 : Excluded a [3,7,5,8,6] :=
  source_excluded a [3,7,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_243 : Excluded a [3,7,5,8] :=
  branch_excluded a [3,7,5,8] (by decide)
    (fin9_cases _
      node_244
      node_245
      node_254
      (invalid_excluded a [3,7,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,5] (by decide +kernel))
      node_255
      (invalid_excluded a [3,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,8] (by decide +kernel)))

theorem node_206 : Excluded a [3,7,5] :=
  branch_excluded a [3,7,5] (by decide)
    (fin9_cases _
      node_207
      node_219
      node_220
      (invalid_excluded a [3,7,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,5] (by decide +kernel))
      node_221
      (invalid_excluded a [3,7,5,7] (by decide +kernel))
      node_243)

theorem node_258 : Excluded a [3,7,6,0,1] :=
  predecessor_excluded a [3,7,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_259 : Excluded a [3,7,6,0,2] :=
  predecessor_excluded a [3,7,6,0,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_261 : Excluded a [3,7,6,0,8,1] :=
  predecessor_excluded a [3,7,6,0,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_262 : Excluded a [3,7,6,0,8,2] :=
  source_excluded a [3,7,6,0,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_264 : Excluded a [3,7,6,0,8,4,1] :=
  source_excluded a [3,7,6,0,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_265 : Excluded a [3,7,6,0,8,4,2] :=
  source_excluded a [3,7,6,0,8,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_266 : Excluded a [3,7,6,0,8,4,5] :=
  predecessor_excluded a [3,7,6,0,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_263 : Excluded a [3,7,6,0,8,4] :=
  branch_excluded a [3,7,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,8,4,0] (by decide +kernel))
      node_264
      node_265
      (invalid_excluded a [3,7,6,0,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,4,4] (by decide +kernel))
      node_266
      (invalid_excluded a [3,7,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,4,8] (by decide +kernel)))

theorem node_260 : Excluded a [3,7,6,0,8] :=
  branch_excluded a [3,7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,8,0] (by decide +kernel))
      node_261
      node_262
      (invalid_excluded a [3,7,6,0,8,3] (by decide +kernel))
      node_263
      (invalid_excluded a [3,7,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,8] (by decide +kernel)))

theorem node_257 : Excluded a [3,7,6,0] :=
  branch_excluded a [3,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,0] (by decide +kernel))
      node_258
      node_259
      (invalid_excluded a [3,7,6,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,7] (by decide +kernel))
      node_260)

theorem node_267 : Excluded a [3,7,6,1] :=
  source_excluded a [3,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_268 : Excluded a [3,7,6,2] :=
  predecessor_excluded a [3,7,6,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_269 : Excluded a [3,7,6,5] :=
  source_excluded a [3,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_272 : Excluded a [3,7,6,8,0,1] :=
  predecessor_excluded a [3,7,6,8,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_273 : Excluded a [3,7,6,8,0,2] :=
  source_excluded a [3,7,6,8,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_275 : Excluded a [3,7,6,8,0,4,1] :=
  source_excluded a [3,7,6,8,0,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_276 : Excluded a [3,7,6,8,0,4,2] :=
  source_excluded a [3,7,6,8,0,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_277 : Excluded a [3,7,6,8,0,4,5] :=
  predecessor_excluded a [3,7,6,8,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_274 : Excluded a [3,7,6,8,0,4] :=
  branch_excluded a [3,7,6,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,0,4,0] (by decide +kernel))
      node_275
      node_276
      (invalid_excluded a [3,7,6,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,4] (by decide +kernel))
      node_277
      (invalid_excluded a [3,7,6,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,8] (by decide +kernel)))

theorem node_271 : Excluded a [3,7,6,8,0] :=
  branch_excluded a [3,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,0,0] (by decide +kernel))
      node_272
      node_273
      (invalid_excluded a [3,7,6,8,0,3] (by decide +kernel))
      node_274
      (invalid_excluded a [3,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,8] (by decide +kernel)))

theorem node_279 : Excluded a [3,7,6,8,1,0] :=
  source_excluded a [3,7,6,8,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_280 : Excluded a [3,7,6,8,1,2] :=
  source_excluded a [3,7,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_282 : Excluded a [3,7,6,8,1,4,0] :=
  source_excluded a [3,7,6,8,1,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_283 : Excluded a [3,7,6,8,1,4,2] :=
  source_excluded a [3,7,6,8,1,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_284 : Excluded a [3,7,6,8,1,4,5] :=
  predecessor_excluded a [3,7,6,8,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_281 : Excluded a [3,7,6,8,1,4] :=
  branch_excluded a [3,7,6,8,1,4] (by decide)
    (fin9_cases _
      node_282
      (invalid_excluded a [3,7,6,8,1,4,1] (by decide +kernel))
      node_283
      (invalid_excluded a [3,7,6,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,4] (by decide +kernel))
      node_284
      (invalid_excluded a [3,7,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,8] (by decide +kernel)))

theorem node_278 : Excluded a [3,7,6,8,1] :=
  branch_excluded a [3,7,6,8,1] (by decide)
    (fin9_cases _
      node_279
      (invalid_excluded a [3,7,6,8,1,1] (by decide +kernel))
      node_280
      (invalid_excluded a [3,7,6,8,1,3] (by decide +kernel))
      node_281
      (invalid_excluded a [3,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,8] (by decide +kernel)))

theorem node_285 : Excluded a [3,7,6,8,2] :=
  predecessor_excluded a [3,7,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_270 : Excluded a [3,7,6,8] :=
  branch_excluded a [3,7,6,8] (by decide)
    (fin9_cases _
      node_271
      node_278
      node_285
      (invalid_excluded a [3,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,8] (by decide +kernel)))

theorem node_256 : Excluded a [3,7,6] :=
  branch_excluded a [3,7,6] (by decide)
    (fin9_cases _
      node_257
      node_267
      node_268
      (invalid_excluded a [3,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,4] (by decide +kernel))
      node_269
      (invalid_excluded a [3,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,7] (by decide +kernel))
      node_270)

theorem node_286 : Excluded a [3,7,8] :=
  predecessor_excluded a [3,7,8] 1 3 2 0 (by decide) (by decide +kernel)

theorem node_170 : Excluded a [3,7] :=
  branch_excluded a [3,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,0] (by decide +kernel))
      node_171
      (invalid_excluded a [3,7,2] (by decide +kernel))
      (invalid_excluded a [3,7,3] (by decide +kernel))
      node_172
      node_206
      node_256
      (invalid_excluded a [3,7,7] (by decide +kernel))
      node_286)

theorem node_288 : Excluded a [3,8,1] :=
  source_excluded a [3,8,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_290 : Excluded a [3,8,4,0] :=
  source_excluded a [3,8,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_291 : Excluded a [3,8,4,1] :=
  source_excluded a [3,8,4,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_292 : Excluded a [3,8,4,2] :=
  source_excluded a [3,8,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_293 : Excluded a [3,8,4,5] :=
  source_excluded a [3,8,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_295 : Excluded a [3,8,4,6,0] :=
  source_excluded a [3,8,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_296 : Excluded a [3,8,4,6,1] :=
  predecessor_excluded a [3,8,4,6,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_298 : Excluded a [3,8,4,6,2,0] :=
  predecessor_excluded a [3,8,4,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

def b_302 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 4
  | 3 => 6
  | 4 => 2
  | 5 => 1
  | 6 => 0
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_302 : LosingRegion (edgeOf a b_302) 1 :=
  losingMask a b_302 1 1342481472814388150796289
    (by decide +kernel) (by decide +kernel)

theorem node_302 : Excluded a [3,8,4,6,2,1,0,5,7] :=
  losing_excluded a [3,8,4,6,2,1,0,5,7] (by decide) b_302 (by decide +kernel) 3 1 2 cert_302 (by change 3 ≠ 1 ∧ ¬ edgeOf a b_302 3 1 ∧ 2 ≠ 3 ∧ maskRegion 1342481472814388150796289 3 2; decide +kernel)

theorem node_301 : Excluded a [3,8,4,6,2,1,0,5] :=
  branch_excluded a [3,8,4,6,2,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,4,6,2,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,5,1] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,5,6] (by decide +kernel))
      node_302
      (invalid_excluded a [3,8,4,6,2,1,0,5,8] (by decide +kernel)))

theorem node_300 : Excluded a [3,8,4,6,2,1,0] :=
  branch_excluded a [3,8,4,6,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,4,6,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,4] (by decide +kernel))
      node_301
      (invalid_excluded a [3,8,4,6,2,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,0,8] (by decide +kernel)))

theorem node_303 : Excluded a [3,8,4,6,2,1,5] :=
  predecessor_excluded a [3,8,4,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_299 : Excluded a [3,8,4,6,2,1] :=
  branch_excluded a [3,8,4,6,2,1] (by decide)
    (fin9_cases _
      node_300
      (invalid_excluded a [3,8,4,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,4] (by decide +kernel))
      node_303
      (invalid_excluded a [3,8,4,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,1,8] (by decide +kernel)))

theorem node_304 : Excluded a [3,8,4,6,2,7] :=
  source_excluded a [3,8,4,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_297 : Excluded a [3,8,4,6,2] :=
  branch_excluded a [3,8,4,6,2] (by decide)
    (fin9_cases _
      node_298
      node_299
      (invalid_excluded a [3,8,4,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,2,6] (by decide +kernel))
      node_304
      (invalid_excluded a [3,8,4,6,2,8] (by decide +kernel)))

theorem node_305 : Excluded a [3,8,4,6,7] :=
  predecessor_excluded a [3,8,4,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_294 : Excluded a [3,8,4,6] :=
  branch_excluded a [3,8,4,6] (by decide)
    (fin9_cases _
      node_295
      node_296
      node_297
      (invalid_excluded a [3,8,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,4,6,6] (by decide +kernel))
      node_305
      (invalid_excluded a [3,8,4,6,8] (by decide +kernel)))

theorem node_307 : Excluded a [3,8,4,7,0] :=
  source_excluded a [3,8,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_308 : Excluded a [3,8,4,7,1] :=
  predecessor_excluded a [3,8,4,7,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_310 : Excluded a [3,8,4,7,2,0] :=
  predecessor_excluded a [3,8,4,7,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_313 : Excluded a [3,8,4,7,2,1,0,5] :=
  predecessor_excluded a [3,8,4,7,2,1,0,5] 0 5 3 7 (by decide) (by decide +kernel)

def b_315 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 4
  | 3 => 7
  | 4 => 2
  | 5 => 1
  | 6 => 0
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_315 : LosingRegion (edgeOf a b_315) 1 :=
  losingMask a b_315 1 1285868433266572046368769
    (by decide +kernel) (by decide +kernel)

theorem node_315 : Excluded a [3,8,4,7,2,1,0,6,5] :=
  losing_excluded a [3,8,4,7,2,1,0,6,5] (by decide) b_315 (by decide +kernel) 3 1 2 cert_315 (by change 3 ≠ 1 ∧ ¬ edgeOf a b_315 3 1 ∧ 2 ≠ 3 ∧ maskRegion 1285868433266572046368769 3 2; decide +kernel)

theorem node_314 : Excluded a [3,8,4,7,2,1,0,6] :=
  branch_excluded a [3,8,4,7,2,1,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,4,7,2,1,0,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,6,1] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,6,4] (by decide +kernel))
      node_315
      (invalid_excluded a [3,8,4,7,2,1,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,6,8] (by decide +kernel)))

theorem node_312 : Excluded a [3,8,4,7,2,1,0] :=
  branch_excluded a [3,8,4,7,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,4,7,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,4] (by decide +kernel))
      node_313
      node_314
      (invalid_excluded a [3,8,4,7,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,0,8] (by decide +kernel)))

theorem node_317 : Excluded a [3,8,4,7,2,1,5,0] :=
  predecessor_excluded a [3,8,4,7,2,1,5,0] 1 3 7 0 (by decide) (by decide +kernel)

theorem node_318 : Excluded a [3,8,4,7,2,1,5,6] :=
  predecessor_excluded a [3,8,4,7,2,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_316 : Excluded a [3,8,4,7,2,1,5] :=
  branch_excluded a [3,8,4,7,2,1,5] (by decide)
    (fin9_cases _
      node_317
      (invalid_excluded a [3,8,4,7,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,5,5] (by decide +kernel))
      node_318
      (invalid_excluded a [3,8,4,7,2,1,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,5,8] (by decide +kernel)))

theorem node_311 : Excluded a [3,8,4,7,2,1] :=
  branch_excluded a [3,8,4,7,2,1] (by decide)
    (fin9_cases _
      node_312
      (invalid_excluded a [3,8,4,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,4] (by decide +kernel))
      node_316
      (invalid_excluded a [3,8,4,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,1,8] (by decide +kernel)))

theorem node_309 : Excluded a [3,8,4,7,2] :=
  branch_excluded a [3,8,4,7,2] (by decide)
    (fin9_cases _
      node_310
      node_311
      (invalid_excluded a [3,8,4,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,2,8] (by decide +kernel)))

theorem node_319 : Excluded a [3,8,4,7,6] :=
  source_excluded a [3,8,4,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_306 : Excluded a [3,8,4,7] :=
  branch_excluded a [3,8,4,7] (by decide)
    (fin9_cases _
      node_307
      node_308
      node_309
      (invalid_excluded a [3,8,4,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,4] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,5] (by decide +kernel))
      node_319
      (invalid_excluded a [3,8,4,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,4,7,8] (by decide +kernel)))

theorem node_289 : Excluded a [3,8,4] :=
  branch_excluded a [3,8,4] (by decide)
    (fin9_cases _
      node_290
      node_291
      node_292
      (invalid_excluded a [3,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,4,4] (by decide +kernel))
      node_293
      node_294
      node_306
      (invalid_excluded a [3,8,4,8] (by decide +kernel)))

theorem node_322 : Excluded a [3,8,5,0,1] :=
  predecessor_excluded a [3,8,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_323 : Excluded a [3,8,5,0,2] :=
  source_excluded a [3,8,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_324 : Excluded a [3,8,5,0,6] :=
  source_excluded a [3,8,5,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_326 : Excluded a [3,8,5,0,7,1] :=
  predecessor_excluded a [3,8,5,0,7,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_328 : Excluded a [3,8,5,0,7,2,1] :=
  predecessor_excluded a [3,8,5,0,7,2,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_329 : Excluded a [3,8,5,0,7,2,4] :=
  source_excluded a [3,8,5,0,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_327 : Excluded a [3,8,5,0,7,2] :=
  branch_excluded a [3,8,5,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,0,7,2,0] (by decide +kernel))
      node_328
      (invalid_excluded a [3,8,5,0,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,2,3] (by decide +kernel))
      node_329
      (invalid_excluded a [3,8,5,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,2,8] (by decide +kernel)))

theorem node_330 : Excluded a [3,8,5,0,7,4] :=
  predecessor_excluded a [3,8,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_325 : Excluded a [3,8,5,0,7] :=
  branch_excluded a [3,8,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,0,7,0] (by decide +kernel))
      node_326
      node_327
      (invalid_excluded a [3,8,5,0,7,3] (by decide +kernel))
      node_330
      (invalid_excluded a [3,8,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,8] (by decide +kernel)))

theorem node_321 : Excluded a [3,8,5,0] :=
  branch_excluded a [3,8,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,0,0] (by decide +kernel))
      node_322
      node_323
      (invalid_excluded a [3,8,5,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,5] (by decide +kernel))
      node_324
      node_325
      (invalid_excluded a [3,8,5,0,8] (by decide +kernel)))

theorem node_331 : Excluded a [3,8,5,1] :=
  source_excluded a [3,8,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_332 : Excluded a [3,8,5,2] :=
  predecessor_excluded a [3,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_334 : Excluded a [3,8,5,6,0] :=
  source_excluded a [3,8,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_336 : Excluded a [3,8,5,6,1,0] :=
  source_excluded a [3,8,5,6,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_337 : Excluded a [3,8,5,6,1,2] :=
  predecessor_excluded a [3,8,5,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_338 : Excluded a [3,8,5,6,1,4] :=
  source_excluded a [3,8,5,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_339 : Excluded a [3,8,5,6,1,7] :=
  source_excluded a [3,8,5,6,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_335 : Excluded a [3,8,5,6,1] :=
  branch_excluded a [3,8,5,6,1] (by decide)
    (fin9_cases _
      node_336
      (invalid_excluded a [3,8,5,6,1,1] (by decide +kernel))
      node_337
      (invalid_excluded a [3,8,5,6,1,3] (by decide +kernel))
      node_338
      (invalid_excluded a [3,8,5,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,6,1,6] (by decide +kernel))
      node_339
      (invalid_excluded a [3,8,5,6,1,8] (by decide +kernel)))

theorem node_340 : Excluded a [3,8,5,6,2] :=
  source_excluded a [3,8,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_341 : Excluded a [3,8,5,6,7] :=
  predecessor_excluded a [3,8,5,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_333 : Excluded a [3,8,5,6] :=
  branch_excluded a [3,8,5,6] (by decide)
    (fin9_cases _
      node_334
      node_335
      node_340
      (invalid_excluded a [3,8,5,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,6,6] (by decide +kernel))
      node_341
      (invalid_excluded a [3,8,5,6,8] (by decide +kernel)))

theorem node_343 : Excluded a [3,8,5,7,0] :=
  source_excluded a [3,8,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_345 : Excluded a [3,8,5,7,1,0] :=
  source_excluded a [3,8,5,7,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_346 : Excluded a [3,8,5,7,1,2] :=
  predecessor_excluded a [3,8,5,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_349 : Excluded a [3,8,5,7,1,4,0,2] :=
  source_excluded a [3,8,5,7,1,4,0,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_351 : Excluded a [3,8,5,7,1,4,0,6,2] :=
  source_excluded a [3,8,5,7,1,4,0,6,2] 1 0 8 (by decide) (by decide +kernel)

theorem node_350 : Excluded a [3,8,5,7,1,4,0,6] :=
  branch_excluded a [3,8,5,7,1,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,4,0,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,6,1] (by decide +kernel))
      node_351
      (invalid_excluded a [3,8,5,7,1,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,6,8] (by decide +kernel)))

theorem node_348 : Excluded a [3,8,5,7,1,4,0] :=
  branch_excluded a [3,8,5,7,1,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,4,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,1] (by decide +kernel))
      node_349
      (invalid_excluded a [3,8,5,7,1,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,5] (by decide +kernel))
      node_350
      (invalid_excluded a [3,8,5,7,1,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,0,8] (by decide +kernel)))

theorem node_353 : Excluded a [3,8,5,7,1,4,2,0] :=
  predecessor_excluded a [3,8,5,7,1,4,2,0] 1 3 7 0 (by decide) (by decide +kernel)

theorem node_355 : Excluded a [3,8,5,7,1,4,2,6,0] :=
  source_excluded a [3,8,5,7,1,4,2,6,0] 8 1 0 (by decide) (by decide +kernel)

theorem node_354 : Excluded a [3,8,5,7,1,4,2,6] :=
  branch_excluded a [3,8,5,7,1,4,2,6] (by decide)
    (fin9_cases _
      node_355
      (invalid_excluded a [3,8,5,7,1,4,2,6,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,6,8] (by decide +kernel)))

theorem node_352 : Excluded a [3,8,5,7,1,4,2] :=
  branch_excluded a [3,8,5,7,1,4,2] (by decide)
    (fin9_cases _
      node_353
      (invalid_excluded a [3,8,5,7,1,4,2,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,5] (by decide +kernel))
      node_354
      (invalid_excluded a [3,8,5,7,1,4,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,2,8] (by decide +kernel)))

theorem node_347 : Excluded a [3,8,5,7,1,4] :=
  branch_excluded a [3,8,5,7,1,4] (by decide)
    (fin9_cases _
      node_348
      (invalid_excluded a [3,8,5,7,1,4,1] (by decide +kernel))
      node_352
      (invalid_excluded a [3,8,5,7,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,4,8] (by decide +kernel)))

theorem node_344 : Excluded a [3,8,5,7,1] :=
  branch_excluded a [3,8,5,7,1] (by decide)
    (fin9_cases _
      node_345
      (invalid_excluded a [3,8,5,7,1,1] (by decide +kernel))
      node_346
      (invalid_excluded a [3,8,5,7,1,3] (by decide +kernel))
      node_347
      (invalid_excluded a [3,8,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,8] (by decide +kernel)))

theorem node_356 : Excluded a [3,8,5,7,2] :=
  source_excluded a [3,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_357 : Excluded a [3,8,5,7,6] :=
  source_excluded a [3,8,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_342 : Excluded a [3,8,5,7] :=
  branch_excluded a [3,8,5,7] (by decide)
    (fin9_cases _
      node_343
      node_344
      node_356
      (invalid_excluded a [3,8,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,5] (by decide +kernel))
      node_357
      (invalid_excluded a [3,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,8] (by decide +kernel)))

theorem node_320 : Excluded a [3,8,5] :=
  branch_excluded a [3,8,5] (by decide)
    (fin9_cases _
      node_321
      node_331
      node_332
      (invalid_excluded a [3,8,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,5] (by decide +kernel))
      node_333
      node_342
      (invalid_excluded a [3,8,5,8] (by decide +kernel)))

theorem node_360 : Excluded a [3,8,6,0,1] :=
  predecessor_excluded a [3,8,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_361 : Excluded a [3,8,6,0,2] :=
  predecessor_excluded a [3,8,6,0,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_364 : Excluded a [3,8,6,0,7,1,2] :=
  predecessor_excluded a [3,8,6,0,7,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_365 : Excluded a [3,8,6,0,7,1,4] :=
  source_excluded a [3,8,6,0,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_366 : Excluded a [3,8,6,0,7,1,5] :=
  source_excluded a [3,8,6,0,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_363 : Excluded a [3,8,6,0,7,1] :=
  branch_excluded a [3,8,6,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,1,1] (by decide +kernel))
      node_364
      (invalid_excluded a [3,8,6,0,7,1,3] (by decide +kernel))
      node_365
      node_366
      (invalid_excluded a [3,8,6,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,1,8] (by decide +kernel)))

theorem node_367 : Excluded a [3,8,6,0,7,2] :=
  source_excluded a [3,8,6,0,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_368 : Excluded a [3,8,6,0,7,4] :=
  predecessor_excluded a [3,8,6,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_362 : Excluded a [3,8,6,0,7] :=
  branch_excluded a [3,8,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,0,7,0] (by decide +kernel))
      node_363
      node_367
      (invalid_excluded a [3,8,6,0,7,3] (by decide +kernel))
      node_368
      (invalid_excluded a [3,8,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,8] (by decide +kernel)))

theorem node_359 : Excluded a [3,8,6,0] :=
  branch_excluded a [3,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,0,0] (by decide +kernel))
      node_360
      node_361
      (invalid_excluded a [3,8,6,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,4] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,6] (by decide +kernel))
      node_362
      (invalid_excluded a [3,8,6,0,8] (by decide +kernel)))

theorem node_369 : Excluded a [3,8,6,1] :=
  source_excluded a [3,8,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_370 : Excluded a [3,8,6,2] :=
  predecessor_excluded a [3,8,6,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_371 : Excluded a [3,8,6,5] :=
  source_excluded a [3,8,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_374 : Excluded a [3,8,6,7,0,1] :=
  predecessor_excluded a [3,8,6,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_375 : Excluded a [3,8,6,7,0,2] :=
  source_excluded a [3,8,6,7,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_377 : Excluded a [3,8,6,7,0,4,1] :=
  predecessor_excluded a [3,8,6,7,0,4,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_379 : Excluded a [3,8,6,7,0,4,2,1] :=
  source_excluded a [3,8,6,7,0,4,2,1] 7 0 1 (by decide) (by decide +kernel)

theorem node_380 : Excluded a [3,8,6,7,0,4,2,5] :=
  predecessor_excluded a [3,8,6,7,0,4,2,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_378 : Excluded a [3,8,6,7,0,4,2] :=
  branch_excluded a [3,8,6,7,0,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,7,0,4,2,0] (by decide +kernel))
      node_379
      (invalid_excluded a [3,8,6,7,0,4,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,4,2,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,4,2,4] (by decide +kernel))
      node_380
      (invalid_excluded a [3,8,6,7,0,4,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,4,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,4,2,8] (by decide +kernel)))

theorem node_381 : Excluded a [3,8,6,7,0,4,5] :=
  predecessor_excluded a [3,8,6,7,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_376 : Excluded a [3,8,6,7,0,4] :=
  branch_excluded a [3,8,6,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,7,0,4,0] (by decide +kernel))
      node_377
      node_378
      (invalid_excluded a [3,8,6,7,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,4,4] (by decide +kernel))
      node_381
      (invalid_excluded a [3,8,6,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,4,8] (by decide +kernel)))

theorem node_373 : Excluded a [3,8,6,7,0] :=
  branch_excluded a [3,8,6,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,7,0,0] (by decide +kernel))
      node_374
      node_375
      (invalid_excluded a [3,8,6,7,0,3] (by decide +kernel))
      node_376
      (invalid_excluded a [3,8,6,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,0,8] (by decide +kernel)))

theorem node_383 : Excluded a [3,8,6,7,1,0] :=
  source_excluded a [3,8,6,7,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_384 : Excluded a [3,8,6,7,1,2] :=
  source_excluded a [3,8,6,7,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_386 : Excluded a [3,8,6,7,1,4,0] :=
  source_excluded a [3,8,6,7,1,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_388 : Excluded a [3,8,6,7,1,4,2,0] :=
  predecessor_excluded a [3,8,6,7,1,4,2,0] 1 3 7 0 (by decide) (by decide +kernel)

theorem node_389 : Excluded a [3,8,6,7,1,4,2,5] :=
  predecessor_excluded a [3,8,6,7,1,4,2,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_387 : Excluded a [3,8,6,7,1,4,2] :=
  branch_excluded a [3,8,6,7,1,4,2] (by decide)
    (fin9_cases _
      node_388
      (invalid_excluded a [3,8,6,7,1,4,2,1] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,4,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,4,2,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,4,2,4] (by decide +kernel))
      node_389
      (invalid_excluded a [3,8,6,7,1,4,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,4,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,4,2,8] (by decide +kernel)))

theorem node_390 : Excluded a [3,8,6,7,1,4,5] :=
  predecessor_excluded a [3,8,6,7,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_385 : Excluded a [3,8,6,7,1,4] :=
  branch_excluded a [3,8,6,7,1,4] (by decide)
    (fin9_cases _
      node_386
      (invalid_excluded a [3,8,6,7,1,4,1] (by decide +kernel))
      node_387
      (invalid_excluded a [3,8,6,7,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,4,4] (by decide +kernel))
      node_390
      (invalid_excluded a [3,8,6,7,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,4,8] (by decide +kernel)))

theorem node_382 : Excluded a [3,8,6,7,1] :=
  branch_excluded a [3,8,6,7,1] (by decide)
    (fin9_cases _
      node_383
      (invalid_excluded a [3,8,6,7,1,1] (by decide +kernel))
      node_384
      (invalid_excluded a [3,8,6,7,1,3] (by decide +kernel))
      node_385
      (invalid_excluded a [3,8,6,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,1,8] (by decide +kernel)))

theorem node_391 : Excluded a [3,8,6,7,2] :=
  predecessor_excluded a [3,8,6,7,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_372 : Excluded a [3,8,6,7] :=
  branch_excluded a [3,8,6,7] (by decide)
    (fin9_cases _
      node_373
      node_382
      node_391
      (invalid_excluded a [3,8,6,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,4] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,7,8] (by decide +kernel)))

theorem node_358 : Excluded a [3,8,6] :=
  branch_excluded a [3,8,6] (by decide)
    (fin9_cases _
      node_359
      node_369
      node_370
      (invalid_excluded a [3,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,4] (by decide +kernel))
      node_371
      (invalid_excluded a [3,8,6,6] (by decide +kernel))
      node_372
      (invalid_excluded a [3,8,6,8] (by decide +kernel)))

theorem node_394 : Excluded a [3,8,7,0,1] :=
  predecessor_excluded a [3,8,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_398 : Excluded a [3,8,7,0,2,1,4,5] :=
  predecessor_excluded a [3,8,7,0,2,1,4,5] 0 5 6 7 (by decide) (by decide +kernel)

def b_400 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 7
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 4
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_400 : LosingRegion (edgeOf a b_400) 0 :=
  losingMask a b_400 0 1255109533168425109556224
    (by decide +kernel) (by decide +kernel)

theorem node_400 : Excluded a [3,8,7,0,2,1,4,6,5] :=
  losing_excluded a [3,8,7,0,2,1,4,6,5] (by decide) b_400 (by decide +kernel) 1 0 2 cert_400 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_400 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1255109533168425109556224 1 2; decide +kernel)

theorem node_399 : Excluded a [3,8,7,0,2,1,4,6] :=
  branch_excluded a [3,8,7,0,2,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,4] (by decide +kernel))
      node_400
      (invalid_excluded a [3,8,7,0,2,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,8] (by decide +kernel)))

theorem node_397 : Excluded a [3,8,7,0,2,1,4] :=
  branch_excluded a [3,8,7,0,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,4] (by decide +kernel))
      node_398
      node_399
      (invalid_excluded a [3,8,7,0,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,8] (by decide +kernel)))

def b_403 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 7
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 5
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_403 : LosingRegion (edgeOf a b_403) 0 :=
  losingMask a b_403 0 1252750655769999500643328
    (by decide +kernel) (by decide +kernel)

theorem node_403 : Excluded a [3,8,7,0,2,1,5,4,6] :=
  losing_excluded a [3,8,7,0,2,1,5,4,6] (by decide) b_403 (by decide +kernel) 1 0 2 cert_403 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_403 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1252750655769999500643328 1 2; decide +kernel)

theorem node_402 : Excluded a [3,8,7,0,2,1,5,4] :=
  branch_excluded a [3,8,7,0,2,1,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,1,5,4,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,4,5] (by decide +kernel))
      node_403
      (invalid_excluded a [3,8,7,0,2,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,4,8] (by decide +kernel)))

theorem node_404 : Excluded a [3,8,7,0,2,1,5,6] :=
  predecessor_excluded a [3,8,7,0,2,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_401 : Excluded a [3,8,7,0,2,1,5] :=
  branch_excluded a [3,8,7,0,2,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,1,5,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,3] (by decide +kernel))
      node_402
      (invalid_excluded a [3,8,7,0,2,1,5,5] (by decide +kernel))
      node_404
      (invalid_excluded a [3,8,7,0,2,1,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,8] (by decide +kernel)))

theorem node_396 : Excluded a [3,8,7,0,2,1] :=
  branch_excluded a [3,8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,3] (by decide +kernel))
      node_397
      node_401
      (invalid_excluded a [3,8,7,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,8] (by decide +kernel)))

theorem node_406 : Excluded a [3,8,7,0,2,4,1] :=
  predecessor_excluded a [3,8,7,0,2,4,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_407 : Excluded a [3,8,7,0,2,4,5] :=
  predecessor_excluded a [3,8,7,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_405 : Excluded a [3,8,7,0,2,4] :=
  branch_excluded a [3,8,7,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,4,0] (by decide +kernel))
      node_406
      (invalid_excluded a [3,8,7,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,4,4] (by decide +kernel))
      node_407
      (invalid_excluded a [3,8,7,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,4,8] (by decide +kernel)))

theorem node_395 : Excluded a [3,8,7,0,2] :=
  branch_excluded a [3,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,0] (by decide +kernel))
      node_396
      (invalid_excluded a [3,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,3] (by decide +kernel))
      node_405
      (invalid_excluded a [3,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,8] (by decide +kernel)))

theorem node_408 : Excluded a [3,8,7,0,6] :=
  source_excluded a [3,8,7,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_393 : Excluded a [3,8,7,0] :=
  branch_excluded a [3,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,0] (by decide +kernel))
      node_394
      node_395
      (invalid_excluded a [3,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,5] (by decide +kernel))
      node_408
      (invalid_excluded a [3,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,8] (by decide +kernel)))

theorem node_409 : Excluded a [3,8,7,1] :=
  source_excluded a [3,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_410 : Excluded a [3,8,7,2] :=
  predecessor_excluded a [3,8,7,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_411 : Excluded a [3,8,7,5] :=
  source_excluded a [3,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_414 : Excluded a [3,8,7,6,0,1] :=
  predecessor_excluded a [3,8,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_415 : Excluded a [3,8,7,6,0,2] :=
  predecessor_excluded a [3,8,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_416 : Excluded a [3,8,7,6,0,4] :=
  source_excluded a [3,8,7,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_413 : Excluded a [3,8,7,6,0] :=
  branch_excluded a [3,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,0,0] (by decide +kernel))
      node_414
      node_415
      (invalid_excluded a [3,8,7,6,0,3] (by decide +kernel))
      node_416
      (invalid_excluded a [3,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,0,8] (by decide +kernel)))

theorem node_419 : Excluded a [3,8,7,6,1,0,2] :=
  source_excluded a [3,8,7,6,1,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_420 : Excluded a [3,8,7,6,1,0,4] :=
  source_excluded a [3,8,7,6,1,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_421 : Excluded a [3,8,7,6,1,0,5] :=
  predecessor_excluded a [3,8,7,6,1,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_418 : Excluded a [3,8,7,6,1,0] :=
  branch_excluded a [3,8,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,1] (by decide +kernel))
      node_419
      (invalid_excluded a [3,8,7,6,1,0,3] (by decide +kernel))
      node_420
      node_421
      (invalid_excluded a [3,8,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,8] (by decide +kernel)))

theorem node_422 : Excluded a [3,8,7,6,1,2] :=
  predecessor_excluded a [3,8,7,6,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_423 : Excluded a [3,8,7,6,1,4] :=
  source_excluded a [3,8,7,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_417 : Excluded a [3,8,7,6,1] :=
  branch_excluded a [3,8,7,6,1] (by decide)
    (fin9_cases _
      node_418
      (invalid_excluded a [3,8,7,6,1,1] (by decide +kernel))
      node_422
      (invalid_excluded a [3,8,7,6,1,3] (by decide +kernel))
      node_423
      (invalid_excluded a [3,8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,8] (by decide +kernel)))

theorem node_425 : Excluded a [3,8,7,6,2,0] :=
  predecessor_excluded a [3,8,7,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_427 : Excluded a [3,8,7,6,2,1,0] :=
  source_excluded a [3,8,7,6,2,1,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_428 : Excluded a [3,8,7,6,2,1,4] :=
  source_excluded a [3,8,7,6,2,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_429 : Excluded a [3,8,7,6,2,1,5] :=
  predecessor_excluded a [3,8,7,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_426 : Excluded a [3,8,7,6,2,1] :=
  branch_excluded a [3,8,7,6,2,1] (by decide)
    (fin9_cases _
      node_427
      (invalid_excluded a [3,8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,3] (by decide +kernel))
      node_428
      node_429
      (invalid_excluded a [3,8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,8] (by decide +kernel)))

theorem node_430 : Excluded a [3,8,7,6,2,4] :=
  source_excluded a [3,8,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_424 : Excluded a [3,8,7,6,2] :=
  branch_excluded a [3,8,7,6,2] (by decide)
    (fin9_cases _
      node_425
      node_426
      (invalid_excluded a [3,8,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,3] (by decide +kernel))
      node_430
      (invalid_excluded a [3,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,8] (by decide +kernel)))

theorem node_412 : Excluded a [3,8,7,6] :=
  branch_excluded a [3,8,7,6] (by decide)
    (fin9_cases _
      node_413
      node_417
      node_424
      (invalid_excluded a [3,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,8] (by decide +kernel)))

theorem node_392 : Excluded a [3,8,7] :=
  branch_excluded a [3,8,7] (by decide)
    (fin9_cases _
      node_393
      node_409
      node_410
      (invalid_excluded a [3,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,4] (by decide +kernel))
      node_411
      node_412
      (invalid_excluded a [3,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,8] (by decide +kernel)))

theorem node_287 : Excluded a [3,8] :=
  branch_excluded a [3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,0] (by decide +kernel))
      node_288
      (invalid_excluded a [3,8,2] (by decide +kernel))
      (invalid_excluded a [3,8,3] (by decide +kernel))
      node_289
      node_320
      node_358
      node_392
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
      node_101
      node_170
      node_287)

theorem node_432 : Excluded a [4,0] :=
  source_excluded a [4,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_434 : Excluded a [4,3,1] :=
  source_excluded a [4,3,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_436 : Excluded a [4,3,5,0] :=
  source_excluded a [4,3,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_437 : Excluded a [4,3,5,1] :=
  source_excluded a [4,3,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_438 : Excluded a [4,3,5,2] :=
  source_excluded a [4,3,5,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_440 : Excluded a [4,3,5,6,0] :=
  source_excluded a [4,3,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_441 : Excluded a [4,3,5,6,1] :=
  source_excluded a [4,3,5,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_442 : Excluded a [4,3,5,6,2] :=
  source_excluded a [4,3,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_443 : Excluded a [4,3,5,6,7] :=
  predecessor_excluded a [4,3,5,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_445 : Excluded a [4,3,5,6,8,0] :=
  source_excluded a [4,3,5,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_446 : Excluded a [4,3,5,6,8,1] :=
  predecessor_excluded a [4,3,5,6,8,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_448 : Excluded a [4,3,5,6,8,2,0] :=
  predecessor_excluded a [4,3,5,6,8,2,0] 1 0 5 6 (by decide) (by decide +kernel)

def b_451 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 6
  | 4 => 8
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_451 : LosingRegion (edgeOf a b_451) 1 :=
  losingMask a b_451 1 1389603608495560674246657
    (by decide +kernel) (by decide +kernel)

theorem node_451 : Excluded a [4,3,5,6,8,2,1,0,7] :=
  losing_excluded a [4,3,5,6,8,2,1,0,7] (by decide) b_451 (by decide +kernel) 3 1 5 cert_451 (by change 3 ≠ 1 ∧ ¬ edgeOf a b_451 3 1 ∧ 5 ≠ 3 ∧ maskRegion 1389603608495560674246657 3 5; decide +kernel)

theorem node_450 : Excluded a [4,3,5,6,8,2,1,0] :=
  branch_excluded a [4,3,5,6,8,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,6,8,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,0,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,0,6] (by decide +kernel))
      node_451
      (invalid_excluded a [4,3,5,6,8,2,1,0,8] (by decide +kernel)))

theorem node_449 : Excluded a [4,3,5,6,8,2,1] :=
  branch_excluded a [4,3,5,6,8,2,1] (by decide)
    (fin9_cases _
      node_450
      (invalid_excluded a [4,3,5,6,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,1,8] (by decide +kernel)))

theorem node_447 : Excluded a [4,3,5,6,8,2] :=
  branch_excluded a [4,3,5,6,8,2] (by decide)
    (fin9_cases _
      node_448
      node_449
      (invalid_excluded a [4,3,5,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,2,8] (by decide +kernel)))

theorem node_452 : Excluded a [4,3,5,6,8,7] :=
  source_excluded a [4,3,5,6,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_444 : Excluded a [4,3,5,6,8] :=
  branch_excluded a [4,3,5,6,8] (by decide)
    (fin9_cases _
      node_445
      node_446
      node_447
      (invalid_excluded a [4,3,5,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,8,6] (by decide +kernel))
      node_452
      (invalid_excluded a [4,3,5,6,8,8] (by decide +kernel)))

theorem node_439 : Excluded a [4,3,5,6] :=
  branch_excluded a [4,3,5,6] (by decide)
    (fin9_cases _
      node_440
      node_441
      node_442
      (invalid_excluded a [4,3,5,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,6,6] (by decide +kernel))
      node_443
      node_444)

theorem node_454 : Excluded a [4,3,5,7,0] :=
  source_excluded a [4,3,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_455 : Excluded a [4,3,5,7,1] :=
  source_excluded a [4,3,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_456 : Excluded a [4,3,5,7,2] :=
  source_excluded a [4,3,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_457 : Excluded a [4,3,5,7,6] :=
  source_excluded a [4,3,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_458 : Excluded a [4,3,5,7,8] :=
  predecessor_excluded a [4,3,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_453 : Excluded a [4,3,5,7] :=
  branch_excluded a [4,3,5,7] (by decide)
    (fin9_cases _
      node_454
      node_455
      node_456
      (invalid_excluded a [4,3,5,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,7,5] (by decide +kernel))
      node_457
      (invalid_excluded a [4,3,5,7,7] (by decide +kernel))
      node_458)

theorem node_460 : Excluded a [4,3,5,8,0] :=
  source_excluded a [4,3,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_461 : Excluded a [4,3,5,8,1] :=
  source_excluded a [4,3,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_462 : Excluded a [4,3,5,8,2] :=
  source_excluded a [4,3,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_463 : Excluded a [4,3,5,8,6] :=
  source_excluded a [4,3,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_465 : Excluded a [4,3,5,8,7,0] :=
  source_excluded a [4,3,5,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_466 : Excluded a [4,3,5,8,7,1] :=
  predecessor_excluded a [4,3,5,8,7,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_468 : Excluded a [4,3,5,8,7,2,0] :=
  predecessor_excluded a [4,3,5,8,7,2,0] 1 0 5 6 (by decide) (by decide +kernel)

def b_471 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | 4 => 7
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 6
  | _ => 0

def cert_471 : LosingRegion (edgeOf a b_471) 1 :=
  losingMask a b_471 1 1361260186226308632543233
    (by decide +kernel) (by decide +kernel)

theorem node_471 : Excluded a [4,3,5,8,7,2,1,0,6] :=
  losing_excluded a [4,3,5,8,7,2,1,0,6] (by decide) b_471 (by decide +kernel) 3 1 2 cert_471 (by change 3 ≠ 1 ∧ ¬ edgeOf a b_471 3 1 ∧ 2 ≠ 3 ∧ maskRegion 1361260186226308632543233 3 2; decide +kernel)

theorem node_470 : Excluded a [4,3,5,8,7,2,1,0] :=
  branch_excluded a [4,3,5,8,7,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,5,8,7,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,0,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,0,5] (by decide +kernel))
      node_471
      (invalid_excluded a [4,3,5,8,7,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,0,8] (by decide +kernel)))

theorem node_472 : Excluded a [4,3,5,8,7,2,1,6] :=
  predecessor_excluded a [4,3,5,8,7,2,1,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_469 : Excluded a [4,3,5,8,7,2,1] :=
  branch_excluded a [4,3,5,8,7,2,1] (by decide)
    (fin9_cases _
      node_470
      (invalid_excluded a [4,3,5,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,5] (by decide +kernel))
      node_472
      (invalid_excluded a [4,3,5,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,1,8] (by decide +kernel)))

theorem node_467 : Excluded a [4,3,5,8,7,2] :=
  branch_excluded a [4,3,5,8,7,2] (by decide)
    (fin9_cases _
      node_468
      node_469
      (invalid_excluded a [4,3,5,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,2,8] (by decide +kernel)))

theorem node_464 : Excluded a [4,3,5,8,7] :=
  branch_excluded a [4,3,5,8,7] (by decide)
    (fin9_cases _
      node_465
      node_466
      node_467
      (invalid_excluded a [4,3,5,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,7,8] (by decide +kernel)))

theorem node_459 : Excluded a [4,3,5,8] :=
  branch_excluded a [4,3,5,8] (by decide)
    (fin9_cases _
      node_460
      node_461
      node_462
      (invalid_excluded a [4,3,5,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,8,5] (by decide +kernel))
      node_463
      node_464
      (invalid_excluded a [4,3,5,8,8] (by decide +kernel)))

theorem node_435 : Excluded a [4,3,5] :=
  branch_excluded a [4,3,5] (by decide)
    (fin9_cases _
      node_436
      node_437
      node_438
      (invalid_excluded a [4,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,3,5,5] (by decide +kernel))
      node_439
      node_453
      node_459)

theorem node_474 : Excluded a [4,3,6,0] :=
  source_excluded a [4,3,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_475 : Excluded a [4,3,6,1] :=
  source_excluded a [4,3,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_476 : Excluded a [4,3,6,2] :=
  source_excluded a [4,3,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_477 : Excluded a [4,3,6,5] :=
  source_excluded a [4,3,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_480 : Excluded a [4,3,6,7,0,1] :=
  predecessor_excluded a [4,3,6,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_481 : Excluded a [4,3,6,7,0,2] :=
  source_excluded a [4,3,6,7,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_483 : Excluded a [4,3,6,7,0,8,1] :=
  predecessor_excluded a [4,3,6,7,0,8,1] 3 1 2 6 (by decide) (by decide +kernel)

theorem node_485 : Excluded a [4,3,6,7,0,8,2,1] :=
  predecessor_excluded a [4,3,6,7,0,8,2,1] 0 3 7 1 (by decide) (by decide +kernel)

theorem node_486 : Excluded a [4,3,6,7,0,8,2,5] :=
  source_excluded a [4,3,6,7,0,8,2,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_484 : Excluded a [4,3,6,7,0,8,2] :=
  branch_excluded a [4,3,6,7,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,6,7,0,8,2,0] (by decide +kernel))
      node_485
      (invalid_excluded a [4,3,6,7,0,8,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,4] (by decide +kernel))
      node_486
      (invalid_excluded a [4,3,6,7,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,2,8] (by decide +kernel)))

theorem node_487 : Excluded a [4,3,6,7,0,8,5] :=
  predecessor_excluded a [4,3,6,7,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_482 : Excluded a [4,3,6,7,0,8] :=
  branch_excluded a [4,3,6,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,6,7,0,8,0] (by decide +kernel))
      node_483
      node_484
      (invalid_excluded a [4,3,6,7,0,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,4] (by decide +kernel))
      node_487
      (invalid_excluded a [4,3,6,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,8,8] (by decide +kernel)))

theorem node_479 : Excluded a [4,3,6,7,0] :=
  branch_excluded a [4,3,6,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,6,7,0,0] (by decide +kernel))
      node_480
      node_481
      (invalid_excluded a [4,3,6,7,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,0,7] (by decide +kernel))
      node_482)

theorem node_488 : Excluded a [4,3,6,7,1] :=
  source_excluded a [4,3,6,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_489 : Excluded a [4,3,6,7,2] :=
  predecessor_excluded a [4,3,6,7,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_490 : Excluded a [4,3,6,7,8] :=
  predecessor_excluded a [4,3,6,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_478 : Excluded a [4,3,6,7] :=
  branch_excluded a [4,3,6,7] (by decide)
    (fin9_cases _
      node_479
      node_488
      node_489
      (invalid_excluded a [4,3,6,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,7,7] (by decide +kernel))
      node_490)

theorem node_493 : Excluded a [4,3,6,8,0,1] :=
  predecessor_excluded a [4,3,6,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_494 : Excluded a [4,3,6,8,0,2] :=
  source_excluded a [4,3,6,8,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_495 : Excluded a [4,3,6,8,0,7] :=
  source_excluded a [4,3,6,8,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_492 : Excluded a [4,3,6,8,0] :=
  branch_excluded a [4,3,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,6,8,0,0] (by decide +kernel))
      node_493
      node_494
      (invalid_excluded a [4,3,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,0,6] (by decide +kernel))
      node_495
      (invalid_excluded a [4,3,6,8,0,8] (by decide +kernel)))

theorem node_496 : Excluded a [4,3,6,8,1] :=
  source_excluded a [4,3,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_497 : Excluded a [4,3,6,8,2] :=
  predecessor_excluded a [4,3,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_499 : Excluded a [4,3,6,8,7,0] :=
  source_excluded a [4,3,6,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_501 : Excluded a [4,3,6,8,7,1,0] :=
  source_excluded a [4,3,6,8,7,1,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_502 : Excluded a [4,3,6,8,7,1,2] :=
  predecessor_excluded a [4,3,6,8,7,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_503 : Excluded a [4,3,6,8,7,1,5] :=
  source_excluded a [4,3,6,8,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_500 : Excluded a [4,3,6,8,7,1] :=
  branch_excluded a [4,3,6,8,7,1] (by decide)
    (fin9_cases _
      node_501
      (invalid_excluded a [4,3,6,8,7,1,1] (by decide +kernel))
      node_502
      (invalid_excluded a [4,3,6,8,7,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,1,4] (by decide +kernel))
      node_503
      (invalid_excluded a [4,3,6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,1,8] (by decide +kernel)))

theorem node_504 : Excluded a [4,3,6,8,7,2] :=
  source_excluded a [4,3,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_498 : Excluded a [4,3,6,8,7] :=
  branch_excluded a [4,3,6,8,7] (by decide)
    (fin9_cases _
      node_499
      node_500
      node_504
      (invalid_excluded a [4,3,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,7,8] (by decide +kernel)))

theorem node_491 : Excluded a [4,3,6,8] :=
  branch_excluded a [4,3,6,8] (by decide)
    (fin9_cases _
      node_492
      node_496
      node_497
      (invalid_excluded a [4,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,3,6,8,6] (by decide +kernel))
      node_498
      (invalid_excluded a [4,3,6,8,8] (by decide +kernel)))

theorem node_473 : Excluded a [4,3,6] :=
  branch_excluded a [4,3,6] (by decide)
    (fin9_cases _
      node_474
      node_475
      node_476
      (invalid_excluded a [4,3,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,6,4] (by decide +kernel))
      node_477
      (invalid_excluded a [4,3,6,6] (by decide +kernel))
      node_478
      node_491)

theorem node_506 : Excluded a [4,3,7,0] :=
  source_excluded a [4,3,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_507 : Excluded a [4,3,7,1] :=
  source_excluded a [4,3,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_508 : Excluded a [4,3,7,2] :=
  source_excluded a [4,3,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_509 : Excluded a [4,3,7,5] :=
  source_excluded a [4,3,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_512 : Excluded a [4,3,7,6,0,1] :=
  predecessor_excluded a [4,3,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_513 : Excluded a [4,3,7,6,0,2] :=
  predecessor_excluded a [4,3,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_516 : Excluded a [4,3,7,6,0,8,1,2] :=
  predecessor_excluded a [4,3,7,6,0,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_517 : Excluded a [4,3,7,6,0,8,1,5] :=
  source_excluded a [4,3,7,6,0,8,1,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_515 : Excluded a [4,3,7,6,0,8,1] :=
  branch_excluded a [4,3,7,6,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,6,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,8,1,1] (by decide +kernel))
      node_516
      (invalid_excluded a [4,3,7,6,0,8,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,8,1,4] (by decide +kernel))
      node_517
      (invalid_excluded a [4,3,7,6,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,8,1,8] (by decide +kernel)))

theorem node_518 : Excluded a [4,3,7,6,0,8,2] :=
  source_excluded a [4,3,7,6,0,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_519 : Excluded a [4,3,7,6,0,8,5] :=
  predecessor_excluded a [4,3,7,6,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_514 : Excluded a [4,3,7,6,0,8] :=
  branch_excluded a [4,3,7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,6,0,8,0] (by decide +kernel))
      node_515
      node_518
      (invalid_excluded a [4,3,7,6,0,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,8,4] (by decide +kernel))
      node_519
      (invalid_excluded a [4,3,7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,8,8] (by decide +kernel)))

theorem node_511 : Excluded a [4,3,7,6,0] :=
  branch_excluded a [4,3,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,6,0,0] (by decide +kernel))
      node_512
      node_513
      (invalid_excluded a [4,3,7,6,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,0,7] (by decide +kernel))
      node_514)

theorem node_520 : Excluded a [4,3,7,6,1] :=
  source_excluded a [4,3,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_521 : Excluded a [4,3,7,6,2] :=
  predecessor_excluded a [4,3,7,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_524 : Excluded a [4,3,7,6,8,0,1] :=
  predecessor_excluded a [4,3,7,6,8,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_525 : Excluded a [4,3,7,6,8,0,2] :=
  source_excluded a [4,3,7,6,8,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_526 : Excluded a [4,3,7,6,8,0,5] :=
  predecessor_excluded a [4,3,7,6,8,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_523 : Excluded a [4,3,7,6,8,0] :=
  branch_excluded a [4,3,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,6,8,0,0] (by decide +kernel))
      node_524
      node_525
      (invalid_excluded a [4,3,7,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,0,4] (by decide +kernel))
      node_526
      (invalid_excluded a [4,3,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,0,8] (by decide +kernel)))

theorem node_528 : Excluded a [4,3,7,6,8,1,0] :=
  source_excluded a [4,3,7,6,8,1,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_529 : Excluded a [4,3,7,6,8,1,2] :=
  source_excluded a [4,3,7,6,8,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_530 : Excluded a [4,3,7,6,8,1,5] :=
  predecessor_excluded a [4,3,7,6,8,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_527 : Excluded a [4,3,7,6,8,1] :=
  branch_excluded a [4,3,7,6,8,1] (by decide)
    (fin9_cases _
      node_528
      (invalid_excluded a [4,3,7,6,8,1,1] (by decide +kernel))
      node_529
      (invalid_excluded a [4,3,7,6,8,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,1,4] (by decide +kernel))
      node_530
      (invalid_excluded a [4,3,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,1,8] (by decide +kernel)))

theorem node_531 : Excluded a [4,3,7,6,8,2] :=
  predecessor_excluded a [4,3,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_522 : Excluded a [4,3,7,6,8] :=
  branch_excluded a [4,3,7,6,8] (by decide)
    (fin9_cases _
      node_523
      node_527
      node_531
      (invalid_excluded a [4,3,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,8,8] (by decide +kernel)))

theorem node_510 : Excluded a [4,3,7,6] :=
  branch_excluded a [4,3,7,6] (by decide)
    (fin9_cases _
      node_511
      node_520
      node_521
      (invalid_excluded a [4,3,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,6,7] (by decide +kernel))
      node_522)

theorem node_534 : Excluded a [4,3,7,8,0,1] :=
  predecessor_excluded a [4,3,7,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_535 : Excluded a [4,3,7,8,0,2] :=
  predecessor_excluded a [4,3,7,8,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_533 : Excluded a [4,3,7,8,0] :=
  branch_excluded a [4,3,7,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,7,8,0,0] (by decide +kernel))
      node_534
      node_535
      (invalid_excluded a [4,3,7,8,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,0,8] (by decide +kernel)))

theorem node_536 : Excluded a [4,3,7,8,1] :=
  source_excluded a [4,3,7,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_537 : Excluded a [4,3,7,8,2] :=
  predecessor_excluded a [4,3,7,8,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_538 : Excluded a [4,3,7,8,6] :=
  source_excluded a [4,3,7,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_532 : Excluded a [4,3,7,8] :=
  branch_excluded a [4,3,7,8] (by decide)
    (fin9_cases _
      node_533
      node_536
      node_537
      (invalid_excluded a [4,3,7,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,4] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,5] (by decide +kernel))
      node_538
      (invalid_excluded a [4,3,7,8,7] (by decide +kernel))
      (invalid_excluded a [4,3,7,8,8] (by decide +kernel)))

theorem node_505 : Excluded a [4,3,7] :=
  branch_excluded a [4,3,7] (by decide)
    (fin9_cases _
      node_506
      node_507
      node_508
      (invalid_excluded a [4,3,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,7,4] (by decide +kernel))
      node_509
      node_510
      (invalid_excluded a [4,3,7,7] (by decide +kernel))
      node_532)

theorem node_540 : Excluded a [4,3,8,0] :=
  source_excluded a [4,3,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_541 : Excluded a [4,3,8,1] :=
  source_excluded a [4,3,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_542 : Excluded a [4,3,8,2] :=
  source_excluded a [4,3,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_543 : Excluded a [4,3,8,5] :=
  source_excluded a [4,3,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_546 : Excluded a [4,3,8,6,0,1] :=
  predecessor_excluded a [4,3,8,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

def b_550 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 8
  | 3 => 6
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_550 : LosingRegion (edgeOf a b_550) 0 :=
  losingMask a b_550 0 1357599210297846790097920
    (by decide +kernel) (by decide +kernel)

theorem node_550 : Excluded a [4,3,8,6,0,2,1,5,7] :=
  losing_excluded a [4,3,8,6,0,2,1,5,7] (by decide) b_550 (by decide +kernel) 1 0 2 cert_550 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_550 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1357599210297846790097920 1 2; decide +kernel)

theorem node_549 : Excluded a [4,3,8,6,0,2,1,5] :=
  branch_excluded a [4,3,8,6,0,2,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,6,0,2,1,5,0] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,5,2] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,5,5] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,5,6] (by decide +kernel))
      node_550
      (invalid_excluded a [4,3,8,6,0,2,1,5,8] (by decide +kernel)))

theorem node_548 : Excluded a [4,3,8,6,0,2,1] :=
  branch_excluded a [4,3,8,6,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,6,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,4] (by decide +kernel))
      node_549
      (invalid_excluded a [4,3,8,6,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,1,8] (by decide +kernel)))

theorem node_551 : Excluded a [4,3,8,6,0,2,5] :=
  predecessor_excluded a [4,3,8,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_547 : Excluded a [4,3,8,6,0,2] :=
  branch_excluded a [4,3,8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,6,0,2,0] (by decide +kernel))
      node_548
      (invalid_excluded a [4,3,8,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,4] (by decide +kernel))
      node_551
      (invalid_excluded a [4,3,8,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,2,8] (by decide +kernel)))

theorem node_552 : Excluded a [4,3,8,6,0,7] :=
  source_excluded a [4,3,8,6,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_545 : Excluded a [4,3,8,6,0] :=
  branch_excluded a [4,3,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,6,0,0] (by decide +kernel))
      node_546
      node_547
      (invalid_excluded a [4,3,8,6,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,0,6] (by decide +kernel))
      node_552
      (invalid_excluded a [4,3,8,6,0,8] (by decide +kernel)))

theorem node_553 : Excluded a [4,3,8,6,1] :=
  source_excluded a [4,3,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_554 : Excluded a [4,3,8,6,2] :=
  predecessor_excluded a [4,3,8,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_555 : Excluded a [4,3,8,6,7] :=
  predecessor_excluded a [4,3,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_544 : Excluded a [4,3,8,6] :=
  branch_excluded a [4,3,8,6] (by decide)
    (fin9_cases _
      node_545
      node_553
      node_554
      (invalid_excluded a [4,3,8,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,5] (by decide +kernel))
      (invalid_excluded a [4,3,8,6,6] (by decide +kernel))
      node_555
      (invalid_excluded a [4,3,8,6,8] (by decide +kernel)))

theorem node_558 : Excluded a [4,3,8,7,0,1] :=
  predecessor_excluded a [4,3,8,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_561 : Excluded a [4,3,8,7,0,2,1,5] :=
  predecessor_excluded a [4,3,8,7,0,2,1,5] 0 5 3 7 (by decide) (by decide +kernel)

def b_563 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 3
  | 2 => 8
  | 3 => 7
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_563 : LosingRegion (edgeOf a b_563) 0 :=
  losingMask a b_563 0 1322181461676324450995200
    (by decide +kernel) (by decide +kernel)

theorem node_563 : Excluded a [4,3,8,7,0,2,1,6,5] :=
  losing_excluded a [4,3,8,7,0,2,1,6,5] (by decide) b_563 (by decide +kernel) 1 0 2 cert_563 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_563 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1322181461676324450995200 1 2; decide +kernel)

theorem node_562 : Excluded a [4,3,8,7,0,2,1,6] :=
  branch_excluded a [4,3,8,7,0,2,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,7,0,2,1,6,0] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,6,1] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,6,2] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,6,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,6,4] (by decide +kernel))
      node_563
      (invalid_excluded a [4,3,8,7,0,2,1,6,6] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,6,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,6,8] (by decide +kernel)))

theorem node_560 : Excluded a [4,3,8,7,0,2,1] :=
  branch_excluded a [4,3,8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,4] (by decide +kernel))
      node_561
      node_562
      (invalid_excluded a [4,3,8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,1,8] (by decide +kernel)))

theorem node_565 : Excluded a [4,3,8,7,0,2,5,1] :=
  predecessor_excluded a [4,3,8,7,0,2,5,1] 0 3 7 1 (by decide) (by decide +kernel)

theorem node_566 : Excluded a [4,3,8,7,0,2,5,6] :=
  predecessor_excluded a [4,3,8,7,0,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_564 : Excluded a [4,3,8,7,0,2,5] :=
  branch_excluded a [4,3,8,7,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,7,0,2,5,0] (by decide +kernel))
      node_565
      (invalid_excluded a [4,3,8,7,0,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,5,5] (by decide +kernel))
      node_566
      (invalid_excluded a [4,3,8,7,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,5,8] (by decide +kernel)))

theorem node_559 : Excluded a [4,3,8,7,0,2] :=
  branch_excluded a [4,3,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,7,0,2,0] (by decide +kernel))
      node_560
      (invalid_excluded a [4,3,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,4] (by decide +kernel))
      node_564
      (invalid_excluded a [4,3,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,2,8] (by decide +kernel)))

theorem node_557 : Excluded a [4,3,8,7,0] :=
  branch_excluded a [4,3,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,8,7,0,0] (by decide +kernel))
      node_558
      node_559
      (invalid_excluded a [4,3,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,0,8] (by decide +kernel)))

theorem node_567 : Excluded a [4,3,8,7,1] :=
  source_excluded a [4,3,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_568 : Excluded a [4,3,8,7,2] :=
  predecessor_excluded a [4,3,8,7,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_569 : Excluded a [4,3,8,7,6] :=
  source_excluded a [4,3,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_556 : Excluded a [4,3,8,7] :=
  branch_excluded a [4,3,8,7] (by decide)
    (fin9_cases _
      node_557
      node_567
      node_568
      (invalid_excluded a [4,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,5] (by decide +kernel))
      node_569
      (invalid_excluded a [4,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,3,8,7,8] (by decide +kernel)))

theorem node_539 : Excluded a [4,3,8] :=
  branch_excluded a [4,3,8] (by decide)
    (fin9_cases _
      node_540
      node_541
      node_542
      (invalid_excluded a [4,3,8,3] (by decide +kernel))
      (invalid_excluded a [4,3,8,4] (by decide +kernel))
      node_543
      node_544
      node_556
      (invalid_excluded a [4,3,8,8] (by decide +kernel)))

theorem node_433 : Excluded a [4,3] :=
  branch_excluded a [4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,3,0] (by decide +kernel))
      node_434
      (invalid_excluded a [4,3,2] (by decide +kernel))
      (invalid_excluded a [4,3,3] (by decide +kernel))
      (invalid_excluded a [4,3,4] (by decide +kernel))
      node_435
      node_473
      node_505
      node_539)

theorem node_570 : Excluded a [4,5] :=
  predecessor_excluded a [4,5] 2 5 0 1 (by decide) (by decide +kernel)

theorem node_572 : Excluded a [4,6,1] :=
  source_excluded a [4,6,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_573 : Excluded a [4,6,3] :=
  predecessor_excluded a [4,6,3] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_575 : Excluded a [4,6,5,0] :=
  source_excluded a [4,6,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_576 : Excluded a [4,6,5,1] :=
  source_excluded a [4,6,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_577 : Excluded a [4,6,5,2] :=
  predecessor_excluded a [4,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_579 : Excluded a [4,6,5,7,0] :=
  source_excluded a [4,6,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_580 : Excluded a [4,6,5,7,1] :=
  source_excluded a [4,6,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_581 : Excluded a [4,6,5,7,2] :=
  source_excluded a [4,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_583 : Excluded a [4,6,5,7,3,0] :=
  source_excluded a [4,6,5,7,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_584 : Excluded a [4,6,5,7,3,1] :=
  source_excluded a [4,6,5,7,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_585 : Excluded a [4,6,5,7,3,2] :=
  source_excluded a [4,6,5,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_587 : Excluded a [4,6,5,7,3,8,0] :=
  predecessor_excluded a [4,6,5,7,3,8,0] 3 0 1 6 (by decide) (by decide +kernel)

def b_590 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 3
  | 5 => 8
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_590 : LosingRegion (edgeOf a b_590) 0 :=
  losingMask a b_590 0 1219552300578502633063424
    (by decide +kernel) (by decide +kernel)

theorem node_590 : Excluded a [4,6,5,7,3,8,1,0,2] :=
  losing_excluded a [4,6,5,7,3,8,1,0,2] (by decide) b_590 (by decide +kernel) 3 0 6 cert_590 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_590 3 0 ∧ 6 ≠ 3 ∧ maskRegion 1219552300578502633063424 3 6; decide +kernel)

theorem node_589 : Excluded a [4,6,5,7,3,8,1,0] :=
  branch_excluded a [4,6,5,7,3,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,5,7,3,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,0,1] (by decide +kernel))
      node_590
      (invalid_excluded a [4,6,5,7,3,8,1,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,0,8] (by decide +kernel)))

theorem node_591 : Excluded a [4,6,5,7,3,8,1,2] :=
  predecessor_excluded a [4,6,5,7,3,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_588 : Excluded a [4,6,5,7,3,8,1] :=
  branch_excluded a [4,6,5,7,3,8,1] (by decide)
    (fin9_cases _
      node_589
      (invalid_excluded a [4,6,5,7,3,8,1,1] (by decide +kernel))
      node_591
      (invalid_excluded a [4,6,5,7,3,8,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,1,8] (by decide +kernel)))

theorem node_592 : Excluded a [4,6,5,7,3,8,2] :=
  source_excluded a [4,6,5,7,3,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_586 : Excluded a [4,6,5,7,3,8] :=
  branch_excluded a [4,6,5,7,3,8] (by decide)
    (fin9_cases _
      node_587
      node_588
      node_592
      (invalid_excluded a [4,6,5,7,3,8,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,8,8] (by decide +kernel)))

theorem node_582 : Excluded a [4,6,5,7,3] :=
  branch_excluded a [4,6,5,7,3] (by decide)
    (fin9_cases _
      node_583
      node_584
      node_585
      (invalid_excluded a [4,6,5,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,3,7] (by decide +kernel))
      node_586)

theorem node_593 : Excluded a [4,6,5,7,8] :=
  predecessor_excluded a [4,6,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_578 : Excluded a [4,6,5,7] :=
  branch_excluded a [4,6,5,7] (by decide)
    (fin9_cases _
      node_579
      node_580
      node_581
      node_582
      (invalid_excluded a [4,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,7] (by decide +kernel))
      node_593)

theorem node_595 : Excluded a [4,6,5,8,0] :=
  source_excluded a [4,6,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_596 : Excluded a [4,6,5,8,1] :=
  source_excluded a [4,6,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_597 : Excluded a [4,6,5,8,2] :=
  source_excluded a [4,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_598 : Excluded a [4,6,5,8,3] :=
  predecessor_excluded a [4,6,5,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_600 : Excluded a [4,6,5,8,7,0] :=
  source_excluded a [4,6,5,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_601 : Excluded a [4,6,5,8,7,1] :=
  source_excluded a [4,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_602 : Excluded a [4,6,5,8,7,2] :=
  source_excluded a [4,6,5,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_604 : Excluded a [4,6,5,8,7,3,0] :=
  predecessor_excluded a [4,6,5,8,7,3,0] 3 0 1 6 (by decide) (by decide +kernel)

def b_607 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 5
  | 3 => 8
  | 4 => 7
  | 5 => 3
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_607 : LosingRegion (edgeOf a b_607) 0 :=
  losingMask a b_607 0 1238441766507645154362368
    (by decide +kernel) (by decide +kernel)

theorem node_607 : Excluded a [4,6,5,8,7,3,1,0,2] :=
  losing_excluded a [4,6,5,8,7,3,1,0,2] (by decide) b_607 (by decide +kernel) 3 0 0 cert_607 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_607 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1238441766507645154362368 3 0; decide +kernel)

theorem node_606 : Excluded a [4,6,5,8,7,3,1,0] :=
  branch_excluded a [4,6,5,8,7,3,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,5,8,7,3,1,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,0,1] (by decide +kernel))
      node_607
      (invalid_excluded a [4,6,5,8,7,3,1,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,0,8] (by decide +kernel)))

theorem node_608 : Excluded a [4,6,5,8,7,3,1,2] :=
  predecessor_excluded a [4,6,5,8,7,3,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_605 : Excluded a [4,6,5,8,7,3,1] :=
  branch_excluded a [4,6,5,8,7,3,1] (by decide)
    (fin9_cases _
      node_606
      (invalid_excluded a [4,6,5,8,7,3,1,1] (by decide +kernel))
      node_608
      (invalid_excluded a [4,6,5,8,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,1,8] (by decide +kernel)))

theorem node_609 : Excluded a [4,6,5,8,7,3,2] :=
  source_excluded a [4,6,5,8,7,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_603 : Excluded a [4,6,5,8,7,3] :=
  branch_excluded a [4,6,5,8,7,3] (by decide)
    (fin9_cases _
      node_604
      node_605
      node_609
      (invalid_excluded a [4,6,5,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,3,8] (by decide +kernel)))

theorem node_599 : Excluded a [4,6,5,8,7] :=
  branch_excluded a [4,6,5,8,7] (by decide)
    (fin9_cases _
      node_600
      node_601
      node_602
      node_603
      (invalid_excluded a [4,6,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,8] (by decide +kernel)))

theorem node_594 : Excluded a [4,6,5,8] :=
  branch_excluded a [4,6,5,8] (by decide)
    (fin9_cases _
      node_595
      node_596
      node_597
      node_598
      (invalid_excluded a [4,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,6] (by decide +kernel))
      node_599
      (invalid_excluded a [4,6,5,8,8] (by decide +kernel)))

theorem node_574 : Excluded a [4,6,5] :=
  branch_excluded a [4,6,5] (by decide)
    (fin9_cases _
      node_575
      node_576
      node_577
      (invalid_excluded a [4,6,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,6] (by decide +kernel))
      node_578
      node_594)

theorem node_610 : Excluded a [4,6,7] :=
  predecessor_excluded a [4,6,7] 0 7 1 2 (by decide) (by decide +kernel)

theorem node_612 : Excluded a [4,6,8,0] :=
  source_excluded a [4,6,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_613 : Excluded a [4,6,8,1] :=
  source_excluded a [4,6,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_615 : Excluded a [4,6,8,2,0] :=
  predecessor_excluded a [4,6,8,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_616 : Excluded a [4,6,8,2,1] :=
  source_excluded a [4,6,8,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_619 : Excluded a [4,6,8,2,3,0,1] :=
  predecessor_excluded a [4,6,8,2,3,0,1] 2 1 5 6 (by decide) (by decide +kernel)

def b_622 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 8
  | 3 => 2
  | 4 => 3
  | 5 => 0
  | 6 => 5
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_622 : LosingRegion (edgeOf a b_622) 0 :=
  losingMask a b_622 0 1326036993106207818388480
    (by decide +kernel) (by decide +kernel)

theorem node_622 : Excluded a [4,6,8,2,3,0,5,1,7] :=
  losing_excluded a [4,6,8,2,3,0,5,1,7] (by decide) b_622 (by decide +kernel) 1 0 3 cert_622 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_622 1 0 ∧ 3 ≠ 1 ∧ maskRegion 1326036993106207818388480 1 3; decide +kernel)

theorem node_621 : Excluded a [4,6,8,2,3,0,5,1] :=
  branch_excluded a [4,6,8,2,3,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,3,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,1,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,1,6] (by decide +kernel))
      node_622
      (invalid_excluded a [4,6,8,2,3,0,5,1,8] (by decide +kernel)))

theorem node_620 : Excluded a [4,6,8,2,3,0,5] :=
  branch_excluded a [4,6,8,2,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,3,0,5,0] (by decide +kernel))
      node_621
      (invalid_excluded a [4,6,8,2,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,5,8] (by decide +kernel)))

theorem node_618 : Excluded a [4,6,8,2,3,0] :=
  branch_excluded a [4,6,8,2,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,3,0,0] (by decide +kernel))
      node_619
      (invalid_excluded a [4,6,8,2,3,0,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,4] (by decide +kernel))
      node_620
      (invalid_excluded a [4,6,8,2,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,0,8] (by decide +kernel)))

theorem node_623 : Excluded a [4,6,8,2,3,1] :=
  source_excluded a [4,6,8,2,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_624 : Excluded a [4,6,8,2,3,7] :=
  source_excluded a [4,6,8,2,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_617 : Excluded a [4,6,8,2,3] :=
  branch_excluded a [4,6,8,2,3] (by decide)
    (fin9_cases _
      node_618
      node_623
      (invalid_excluded a [4,6,8,2,3,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,3,6] (by decide +kernel))
      node_624
      (invalid_excluded a [4,6,8,2,3,8] (by decide +kernel)))

theorem node_627 : Excluded a [4,6,8,2,7,0,1] :=
  predecessor_excluded a [4,6,8,2,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

def b_630 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 8
  | 3 => 2
  | 4 => 7
  | 5 => 0
  | 6 => 3
  | 7 => 1
  | 8 => 5
  | _ => 0

def cert_630 : LosingRegion (edgeOf a b_630) 0 :=
  losingMask a b_630 0 1212510505918624210885632
    (by decide +kernel) (by decide +kernel)

theorem node_630 : Excluded a [4,6,8,2,7,0,3,1,5] :=
  losing_excluded a [4,6,8,2,7,0,3,1,5] (by decide) b_630 (by decide +kernel) 1 0 2 cert_630 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_630 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212510505918624210885632 1 2; decide +kernel)

theorem node_629 : Excluded a [4,6,8,2,7,0,3,1] :=
  branch_excluded a [4,6,8,2,7,0,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,7,0,3,1,0] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,1,4] (by decide +kernel))
      node_630
      (invalid_excluded a [4,6,8,2,7,0,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,1,8] (by decide +kernel)))

theorem node_631 : Excluded a [4,6,8,2,7,0,3,5] :=
  source_excluded a [4,6,8,2,7,0,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_628 : Excluded a [4,6,8,2,7,0,3] :=
  branch_excluded a [4,6,8,2,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,7,0,3,0] (by decide +kernel))
      node_629
      (invalid_excluded a [4,6,8,2,7,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,4] (by decide +kernel))
      node_631
      (invalid_excluded a [4,6,8,2,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,3,8] (by decide +kernel)))

theorem node_632 : Excluded a [4,6,8,2,7,0,5] :=
  source_excluded a [4,6,8,2,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_626 : Excluded a [4,6,8,2,7,0] :=
  branch_excluded a [4,6,8,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,7,0,0] (by decide +kernel))
      node_627
      (invalid_excluded a [4,6,8,2,7,0,2] (by decide +kernel))
      node_628
      (invalid_excluded a [4,6,8,2,7,0,4] (by decide +kernel))
      node_632
      (invalid_excluded a [4,6,8,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,8] (by decide +kernel)))

theorem node_633 : Excluded a [4,6,8,2,7,1] :=
  source_excluded a [4,6,8,2,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_635 : Excluded a [4,6,8,2,7,3,0] :=
  predecessor_excluded a [4,6,8,2,7,3,0] 3 0 1 6 (by decide) (by decide +kernel)

theorem node_637 : Excluded a [4,6,8,2,7,3,1,0] :=
  source_excluded a [4,6,8,2,7,3,1,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_638 : Excluded a [4,6,8,2,7,3,1,5] :=
  source_excluded a [4,6,8,2,7,3,1,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_636 : Excluded a [4,6,8,2,7,3,1] :=
  branch_excluded a [4,6,8,2,7,3,1] (by decide)
    (fin9_cases _
      node_637
      (invalid_excluded a [4,6,8,2,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,4] (by decide +kernel))
      node_638
      (invalid_excluded a [4,6,8,2,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,8] (by decide +kernel)))

theorem node_639 : Excluded a [4,6,8,2,7,3,5] :=
  source_excluded a [4,6,8,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_634 : Excluded a [4,6,8,2,7,3] :=
  branch_excluded a [4,6,8,2,7,3] (by decide)
    (fin9_cases _
      node_635
      node_636
      (invalid_excluded a [4,6,8,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,4] (by decide +kernel))
      node_639
      (invalid_excluded a [4,6,8,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,8] (by decide +kernel)))

theorem node_625 : Excluded a [4,6,8,2,7] :=
  branch_excluded a [4,6,8,2,7] (by decide)
    (fin9_cases _
      node_626
      node_633
      (invalid_excluded a [4,6,8,2,7,2] (by decide +kernel))
      node_634
      (invalid_excluded a [4,6,8,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,8] (by decide +kernel)))

theorem node_614 : Excluded a [4,6,8,2] :=
  branch_excluded a [4,6,8,2] (by decide)
    (fin9_cases _
      node_615
      node_616
      (invalid_excluded a [4,6,8,2,2] (by decide +kernel))
      node_617
      (invalid_excluded a [4,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,6] (by decide +kernel))
      node_625
      (invalid_excluded a [4,6,8,2,8] (by decide +kernel)))

theorem node_640 : Excluded a [4,6,8,5] :=
  source_excluded a [4,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_643 : Excluded a [4,6,8,7,0,1] :=
  source_excluded a [4,6,8,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_644 : Excluded a [4,6,8,7,0,2] :=
  source_excluded a [4,6,8,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_645 : Excluded a [4,6,8,7,0,3] :=
  predecessor_excluded a [4,6,8,7,0,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_642 : Excluded a [4,6,8,7,0] :=
  branch_excluded a [4,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,0,0] (by decide +kernel))
      node_643
      node_644
      node_645
      (invalid_excluded a [4,6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,8] (by decide +kernel)))

theorem node_646 : Excluded a [4,6,8,7,1] :=
  source_excluded a [4,6,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_647 : Excluded a [4,6,8,7,2] :=
  predecessor_excluded a [4,6,8,7,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_650 : Excluded a [4,6,8,7,3,0,1] :=
  predecessor_excluded a [4,6,8,7,3,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_651 : Excluded a [4,6,8,7,3,0,2] :=
  source_excluded a [4,6,8,7,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_654 : Excluded a [4,6,8,7,3,0,5,1,2] :=
  predecessor_excluded a [4,6,8,7,3,0,5,1,2] 0 2 7 8 (by decide) (by decide +kernel)

theorem node_653 : Excluded a [4,6,8,7,3,0,5,1] :=
  branch_excluded a [4,6,8,7,3,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,3,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,1] (by decide +kernel))
      node_654
      (invalid_excluded a [4,6,8,7,3,0,5,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,8] (by decide +kernel)))

theorem node_655 : Excluded a [4,6,8,7,3,0,5,2] :=
  source_excluded a [4,6,8,7,3,0,5,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_652 : Excluded a [4,6,8,7,3,0,5] :=
  branch_excluded a [4,6,8,7,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,3,0,5,0] (by decide +kernel))
      node_653
      node_655
      (invalid_excluded a [4,6,8,7,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,8] (by decide +kernel)))

theorem node_649 : Excluded a [4,6,8,7,3,0] :=
  branch_excluded a [4,6,8,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,3,0,0] (by decide +kernel))
      node_650
      node_651
      (invalid_excluded a [4,6,8,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,4] (by decide +kernel))
      node_652
      (invalid_excluded a [4,6,8,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,8] (by decide +kernel)))

theorem node_656 : Excluded a [4,6,8,7,3,1] :=
  source_excluded a [4,6,8,7,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_657 : Excluded a [4,6,8,7,3,2] :=
  source_excluded a [4,6,8,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_648 : Excluded a [4,6,8,7,3] :=
  branch_excluded a [4,6,8,7,3] (by decide)
    (fin9_cases _
      node_649
      node_656
      node_657
      (invalid_excluded a [4,6,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,8] (by decide +kernel)))

theorem node_641 : Excluded a [4,6,8,7] :=
  branch_excluded a [4,6,8,7] (by decide)
    (fin9_cases _
      node_642
      node_646
      node_647
      node_648
      (invalid_excluded a [4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,8] (by decide +kernel)))

theorem node_611 : Excluded a [4,6,8] :=
  branch_excluded a [4,6,8] (by decide)
    (fin9_cases _
      node_612
      node_613
      node_614
      (invalid_excluded a [4,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,4] (by decide +kernel))
      node_640
      (invalid_excluded a [4,6,8,6] (by decide +kernel))
      node_641
      (invalid_excluded a [4,6,8,8] (by decide +kernel)))

theorem node_571 : Excluded a [4,6] :=
  branch_excluded a [4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,0] (by decide +kernel))
      node_572
      (invalid_excluded a [4,6,2] (by decide +kernel))
      node_573
      (invalid_excluded a [4,6,4] (by decide +kernel))
      node_574
      (invalid_excluded a [4,6,6] (by decide +kernel))
      node_610
      node_611)

theorem node_659 : Excluded a [4,7,1] :=
  source_excluded a [4,7,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_660 : Excluded a [4,7,3] :=
  predecessor_excluded a [4,7,3] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_662 : Excluded a [4,7,5,0] :=
  source_excluded a [4,7,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_663 : Excluded a [4,7,5,1] :=
  source_excluded a [4,7,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_664 : Excluded a [4,7,5,2] :=
  predecessor_excluded a [4,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_666 : Excluded a [4,7,5,6,0] :=
  source_excluded a [4,7,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_667 : Excluded a [4,7,5,6,1] :=
  source_excluded a [4,7,5,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_668 : Excluded a [4,7,5,6,2] :=
  source_excluded a [4,7,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_669 : Excluded a [4,7,5,6,3] :=
  predecessor_excluded a [4,7,5,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_671 : Excluded a [4,7,5,6,8,0] :=
  source_excluded a [4,7,5,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_672 : Excluded a [4,7,5,6,8,1] :=
  predecessor_excluded a [4,7,5,6,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_674 : Excluded a [4,7,5,6,8,2,0] :=
  predecessor_excluded a [4,7,5,6,8,2,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_675 : Excluded a [4,7,5,6,8,2,1] :=
  source_excluded a [4,7,5,6,8,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_677 : Excluded a [4,7,5,6,8,2,3,0] :=
  predecessor_excluded a [4,7,5,6,8,2,3,0] 3 0 1 7 (by decide) (by decide +kernel)

theorem node_679 : Excluded a [4,7,5,6,8,2,3,1,0] :=
  predecessor_excluded a [4,7,5,6,8,2,3,1,0] 1 4 8 0 (by decide) (by decide +kernel)

theorem node_678 : Excluded a [4,7,5,6,8,2,3,1] :=
  branch_excluded a [4,7,5,6,8,2,3,1] (by decide)
    (fin9_cases _
      node_679
      (invalid_excluded a [4,7,5,6,8,2,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,1,8] (by decide +kernel)))

theorem node_676 : Excluded a [4,7,5,6,8,2,3] :=
  branch_excluded a [4,7,5,6,8,2,3] (by decide)
    (fin9_cases _
      node_677
      node_678
      (invalid_excluded a [4,7,5,6,8,2,3,2] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,3,8] (by decide +kernel)))

theorem node_673 : Excluded a [4,7,5,6,8,2] :=
  branch_excluded a [4,7,5,6,8,2] (by decide)
    (fin9_cases _
      node_674
      node_675
      (invalid_excluded a [4,7,5,6,8,2,2] (by decide +kernel))
      node_676
      (invalid_excluded a [4,7,5,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,2,8] (by decide +kernel)))

theorem node_680 : Excluded a [4,7,5,6,8,3] :=
  source_excluded a [4,7,5,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_670 : Excluded a [4,7,5,6,8] :=
  branch_excluded a [4,7,5,6,8] (by decide)
    (fin9_cases _
      node_671
      node_672
      node_673
      node_680
      (invalid_excluded a [4,7,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,8,8] (by decide +kernel)))

theorem node_665 : Excluded a [4,7,5,6] :=
  branch_excluded a [4,7,5,6] (by decide)
    (fin9_cases _
      node_666
      node_667
      node_668
      node_669
      (invalid_excluded a [4,7,5,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,6,7] (by decide +kernel))
      node_670)

theorem node_682 : Excluded a [4,7,5,8,0] :=
  source_excluded a [4,7,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_683 : Excluded a [4,7,5,8,1] :=
  source_excluded a [4,7,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_684 : Excluded a [4,7,5,8,2] :=
  source_excluded a [4,7,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_685 : Excluded a [4,7,5,8,3] :=
  predecessor_excluded a [4,7,5,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_686 : Excluded a [4,7,5,8,6] :=
  source_excluded a [4,7,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_681 : Excluded a [4,7,5,8] :=
  branch_excluded a [4,7,5,8] (by decide)
    (fin9_cases _
      node_682
      node_683
      node_684
      node_685
      (invalid_excluded a [4,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,5] (by decide +kernel))
      node_686
      (invalid_excluded a [4,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,8] (by decide +kernel)))

theorem node_661 : Excluded a [4,7,5] :=
  branch_excluded a [4,7,5] (by decide)
    (fin9_cases _
      node_662
      node_663
      node_664
      (invalid_excluded a [4,7,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,5] (by decide +kernel))
      node_665
      (invalid_excluded a [4,7,5,7] (by decide +kernel))
      node_681)

theorem node_688 : Excluded a [4,7,6,0] :=
  source_excluded a [4,7,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_689 : Excluded a [4,7,6,1] :=
  source_excluded a [4,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_691 : Excluded a [4,7,6,2,0] :=
  predecessor_excluded a [4,7,6,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_692 : Excluded a [4,7,6,2,1] :=
  source_excluded a [4,7,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_694 : Excluded a [4,7,6,2,3,0] :=
  source_excluded a [4,7,6,2,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_695 : Excluded a [4,7,6,2,3,1] :=
  predecessor_excluded a [4,7,6,2,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_697 : Excluded a [4,7,6,2,3,8,0] :=
  source_excluded a [4,7,6,2,3,8,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_698 : Excluded a [4,7,6,2,3,8,1] :=
  source_excluded a [4,7,6,2,3,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_699 : Excluded a [4,7,6,2,3,8,5] :=
  predecessor_excluded a [4,7,6,2,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_696 : Excluded a [4,7,6,2,3,8] :=
  branch_excluded a [4,7,6,2,3,8] (by decide)
    (fin9_cases _
      node_697
      node_698
      (invalid_excluded a [4,7,6,2,3,8,2] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,3,8,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,3,8,4] (by decide +kernel))
      node_699
      (invalid_excluded a [4,7,6,2,3,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,3,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,3,8,8] (by decide +kernel)))

theorem node_693 : Excluded a [4,7,6,2,3] :=
  branch_excluded a [4,7,6,2,3] (by decide)
    (fin9_cases _
      node_694
      node_695
      (invalid_excluded a [4,7,6,2,3,2] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,3,7] (by decide +kernel))
      node_696)

theorem node_701 : Excluded a [4,7,6,2,8,0] :=
  source_excluded a [4,7,6,2,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_702 : Excluded a [4,7,6,2,8,1] :=
  predecessor_excluded a [4,7,6,2,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_703 : Excluded a [4,7,6,2,8,3] :=
  predecessor_excluded a [4,7,6,2,8,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_700 : Excluded a [4,7,6,2,8] :=
  branch_excluded a [4,7,6,2,8] (by decide)
    (fin9_cases _
      node_701
      node_702
      (invalid_excluded a [4,7,6,2,8,2] (by decide +kernel))
      node_703
      (invalid_excluded a [4,7,6,2,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,8] (by decide +kernel)))

theorem node_690 : Excluded a [4,7,6,2] :=
  branch_excluded a [4,7,6,2] (by decide)
    (fin9_cases _
      node_691
      node_692
      (invalid_excluded a [4,7,6,2,2] (by decide +kernel))
      node_693
      (invalid_excluded a [4,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,7] (by decide +kernel))
      node_700)

theorem node_704 : Excluded a [4,7,6,5] :=
  source_excluded a [4,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_707 : Excluded a [4,7,6,8,0,1] :=
  predecessor_excluded a [4,7,6,8,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_708 : Excluded a [4,7,6,8,0,2] :=
  source_excluded a [4,7,6,8,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_710 : Excluded a [4,7,6,8,0,3,1] :=
  source_excluded a [4,7,6,8,0,3,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_711 : Excluded a [4,7,6,8,0,3,2] :=
  source_excluded a [4,7,6,8,0,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_714 : Excluded a [4,7,6,8,0,3,5,1,2] :=
  predecessor_excluded a [4,7,6,8,0,3,5,1,2] 0 2 7 8 (by decide) (by decide +kernel)

theorem node_713 : Excluded a [4,7,6,8,0,3,5,1] :=
  branch_excluded a [4,7,6,8,0,3,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,0,3,5,1,0] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,1,1] (by decide +kernel))
      node_714
      (invalid_excluded a [4,7,6,8,0,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,1,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,1,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,1,8] (by decide +kernel)))

theorem node_715 : Excluded a [4,7,6,8,0,3,5,2] :=
  source_excluded a [4,7,6,8,0,3,5,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_712 : Excluded a [4,7,6,8,0,3,5] :=
  branch_excluded a [4,7,6,8,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,0,3,5,0] (by decide +kernel))
      node_713
      node_715
      (invalid_excluded a [4,7,6,8,0,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,5,8] (by decide +kernel)))

theorem node_709 : Excluded a [4,7,6,8,0,3] :=
  branch_excluded a [4,7,6,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,0,3,0] (by decide +kernel))
      node_710
      node_711
      (invalid_excluded a [4,7,6,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,4] (by decide +kernel))
      node_712
      (invalid_excluded a [4,7,6,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,3,8] (by decide +kernel)))

theorem node_706 : Excluded a [4,7,6,8,0] :=
  branch_excluded a [4,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,0,0] (by decide +kernel))
      node_707
      node_708
      node_709
      (invalid_excluded a [4,7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,0,8] (by decide +kernel)))

theorem node_716 : Excluded a [4,7,6,8,1] :=
  source_excluded a [4,7,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_717 : Excluded a [4,7,6,8,2] :=
  predecessor_excluded a [4,7,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_718 : Excluded a [4,7,6,8,3] :=
  predecessor_excluded a [4,7,6,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_705 : Excluded a [4,7,6,8] :=
  branch_excluded a [4,7,6,8] (by decide)
    (fin9_cases _
      node_706
      node_716
      node_717
      node_718
      (invalid_excluded a [4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,8] (by decide +kernel)))

theorem node_687 : Excluded a [4,7,6] :=
  branch_excluded a [4,7,6] (by decide)
    (fin9_cases _
      node_688
      node_689
      node_690
      (invalid_excluded a [4,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,4] (by decide +kernel))
      node_704
      (invalid_excluded a [4,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,7] (by decide +kernel))
      node_705)

theorem node_719 : Excluded a [4,7,8] :=
  predecessor_excluded a [4,7,8] 0 8 1 2 (by decide) (by decide +kernel)

theorem node_658 : Excluded a [4,7] :=
  branch_excluded a [4,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,0] (by decide +kernel))
      node_659
      (invalid_excluded a [4,7,2] (by decide +kernel))
      node_660
      (invalid_excluded a [4,7,4] (by decide +kernel))
      node_661
      node_687
      (invalid_excluded a [4,7,7] (by decide +kernel))
      node_719)

theorem node_721 : Excluded a [4,8,1] :=
  source_excluded a [4,8,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_722 : Excluded a [4,8,3] :=
  predecessor_excluded a [4,8,3] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_724 : Excluded a [4,8,5,0] :=
  source_excluded a [4,8,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_725 : Excluded a [4,8,5,1] :=
  source_excluded a [4,8,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_726 : Excluded a [4,8,5,2] :=
  predecessor_excluded a [4,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_728 : Excluded a [4,8,5,6,0] :=
  source_excluded a [4,8,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_729 : Excluded a [4,8,5,6,1] :=
  source_excluded a [4,8,5,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_730 : Excluded a [4,8,5,6,2] :=
  source_excluded a [4,8,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_731 : Excluded a [4,8,5,6,3] :=
  predecessor_excluded a [4,8,5,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_732 : Excluded a [4,8,5,6,7] :=
  predecessor_excluded a [4,8,5,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_727 : Excluded a [4,8,5,6] :=
  branch_excluded a [4,8,5,6] (by decide)
    (fin9_cases _
      node_728
      node_729
      node_730
      node_731
      (invalid_excluded a [4,8,5,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,6,6] (by decide +kernel))
      node_732
      (invalid_excluded a [4,8,5,6,8] (by decide +kernel)))

theorem node_734 : Excluded a [4,8,5,7,0] :=
  source_excluded a [4,8,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_735 : Excluded a [4,8,5,7,1] :=
  source_excluded a [4,8,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_736 : Excluded a [4,8,5,7,2] :=
  source_excluded a [4,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_738 : Excluded a [4,8,5,7,3,0] :=
  source_excluded a [4,8,5,7,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_739 : Excluded a [4,8,5,7,3,1] :=
  predecessor_excluded a [4,8,5,7,3,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_741 : Excluded a [4,8,5,7,3,2,0] :=
  predecessor_excluded a [4,8,5,7,3,2,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_742 : Excluded a [4,8,5,7,3,2,1] :=
  predecessor_excluded a [4,8,5,7,3,2,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_740 : Excluded a [4,8,5,7,3,2] :=
  branch_excluded a [4,8,5,7,3,2] (by decide)
    (fin9_cases _
      node_741
      node_742
      (invalid_excluded a [4,8,5,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,2,8] (by decide +kernel)))

theorem node_737 : Excluded a [4,8,5,7,3] :=
  branch_excluded a [4,8,5,7,3] (by decide)
    (fin9_cases _
      node_738
      node_739
      node_740
      (invalid_excluded a [4,8,5,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,3,8] (by decide +kernel)))

theorem node_743 : Excluded a [4,8,5,7,6] :=
  source_excluded a [4,8,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_733 : Excluded a [4,8,5,7] :=
  branch_excluded a [4,8,5,7] (by decide)
    (fin9_cases _
      node_734
      node_735
      node_736
      node_737
      (invalid_excluded a [4,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,5] (by decide +kernel))
      node_743
      (invalid_excluded a [4,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,8] (by decide +kernel)))

theorem node_723 : Excluded a [4,8,5] :=
  branch_excluded a [4,8,5] (by decide)
    (fin9_cases _
      node_724
      node_725
      node_726
      (invalid_excluded a [4,8,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,5] (by decide +kernel))
      node_727
      node_733
      (invalid_excluded a [4,8,5,8] (by decide +kernel)))

theorem node_745 : Excluded a [4,8,6,0] :=
  source_excluded a [4,8,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_746 : Excluded a [4,8,6,1] :=
  source_excluded a [4,8,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_748 : Excluded a [4,8,6,2,0] :=
  predecessor_excluded a [4,8,6,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_749 : Excluded a [4,8,6,2,1] :=
  source_excluded a [4,8,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_751 : Excluded a [4,8,6,2,3,0] :=
  source_excluded a [4,8,6,2,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_753 : Excluded a [4,8,6,2,3,1,0] :=
  source_excluded a [4,8,6,2,3,1,0] 2 1 6 (by decide) (by decide +kernel)

def b_756 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 6
  | 3 => 2
  | 4 => 3
  | 5 => 1
  | 6 => 5
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_756 : LosingRegion (edgeOf a b_756) 3 :=
  losingMask a b_756 3 1210114498645845727183873
    (by decide +kernel) (by decide +kernel)

theorem node_756 : Excluded a [4,8,6,2,3,1,5,0,7] :=
  losing_excluded a [4,8,6,2,3,1,5,0,7] (by decide) b_756 (by decide +kernel) 1 3 7 cert_756 (by change 1 ≠ 3 ∧ ¬ edgeOf a b_756 1 3 ∧ 7 ≠ 1 ∧ maskRegion 1210114498645845727183873 1 7; decide +kernel)

theorem node_755 : Excluded a [4,8,6,2,3,1,5,0] :=
  branch_excluded a [4,8,6,2,3,1,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,2,3,1,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,0,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,0,2] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,0,6] (by decide +kernel))
      node_756
      (invalid_excluded a [4,8,6,2,3,1,5,0,8] (by decide +kernel)))

theorem node_754 : Excluded a [4,8,6,2,3,1,5] :=
  branch_excluded a [4,8,6,2,3,1,5] (by decide)
    (fin9_cases _
      node_755
      (invalid_excluded a [4,8,6,2,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,5,8] (by decide +kernel)))

theorem node_752 : Excluded a [4,8,6,2,3,1] :=
  branch_excluded a [4,8,6,2,3,1] (by decide)
    (fin9_cases _
      node_753
      (invalid_excluded a [4,8,6,2,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,4] (by decide +kernel))
      node_754
      (invalid_excluded a [4,8,6,2,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,1,8] (by decide +kernel)))

theorem node_757 : Excluded a [4,8,6,2,3,7] :=
  source_excluded a [4,8,6,2,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_750 : Excluded a [4,8,6,2,3] :=
  branch_excluded a [4,8,6,2,3] (by decide)
    (fin9_cases _
      node_751
      node_752
      (invalid_excluded a [4,8,6,2,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,3,6] (by decide +kernel))
      node_757
      (invalid_excluded a [4,8,6,2,3,8] (by decide +kernel)))

theorem node_759 : Excluded a [4,8,6,2,7,0] :=
  source_excluded a [4,8,6,2,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_761 : Excluded a [4,8,6,2,7,1,0] :=
  source_excluded a [4,8,6,2,7,1,0] 2 1 6 (by decide) (by decide +kernel)

def b_764 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 6
  | 3 => 2
  | 4 => 7
  | 5 => 1
  | 6 => 3
  | 7 => 0
  | 8 => 5
  | _ => 0

def cert_764 : LosingRegion (edgeOf a b_764) 0 :=
  losingMask a b_764 0 1578452153344619898215424
    (by decide +kernel) (by decide +kernel)

theorem node_764 : Excluded a [4,8,6,2,7,1,3,0,5] :=
  losing_excluded a [4,8,6,2,7,1,3,0,5] (by decide) b_764 (by decide +kernel) 1 0 2 cert_764 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_764 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1578452153344619898215424 1 2; decide +kernel)

theorem node_763 : Excluded a [4,8,6,2,7,1,3,0] :=
  branch_excluded a [4,8,6,2,7,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,2,7,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,0,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,0,2] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,0,4] (by decide +kernel))
      node_764
      (invalid_excluded a [4,8,6,2,7,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,0,8] (by decide +kernel)))

theorem node_765 : Excluded a [4,8,6,2,7,1,3,5] :=
  source_excluded a [4,8,6,2,7,1,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_762 : Excluded a [4,8,6,2,7,1,3] :=
  branch_excluded a [4,8,6,2,7,1,3] (by decide)
    (fin9_cases _
      node_763
      (invalid_excluded a [4,8,6,2,7,1,3,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,4] (by decide +kernel))
      node_765
      (invalid_excluded a [4,8,6,2,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,3,8] (by decide +kernel)))

theorem node_766 : Excluded a [4,8,6,2,7,1,5] :=
  source_excluded a [4,8,6,2,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_760 : Excluded a [4,8,6,2,7,1] :=
  branch_excluded a [4,8,6,2,7,1] (by decide)
    (fin9_cases _
      node_761
      (invalid_excluded a [4,8,6,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,2] (by decide +kernel))
      node_762
      (invalid_excluded a [4,8,6,2,7,1,4] (by decide +kernel))
      node_766
      (invalid_excluded a [4,8,6,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,8] (by decide +kernel)))

theorem node_768 : Excluded a [4,8,6,2,7,3,0] :=
  source_excluded a [4,8,6,2,7,3,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_769 : Excluded a [4,8,6,2,7,3,1] :=
  predecessor_excluded a [4,8,6,2,7,3,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_770 : Excluded a [4,8,6,2,7,3,5] :=
  source_excluded a [4,8,6,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_767 : Excluded a [4,8,6,2,7,3] :=
  branch_excluded a [4,8,6,2,7,3] (by decide)
    (fin9_cases _
      node_768
      node_769
      (invalid_excluded a [4,8,6,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,3,4] (by decide +kernel))
      node_770
      (invalid_excluded a [4,8,6,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,3,8] (by decide +kernel)))

theorem node_758 : Excluded a [4,8,6,2,7] :=
  branch_excluded a [4,8,6,2,7] (by decide)
    (fin9_cases _
      node_759
      node_760
      (invalid_excluded a [4,8,6,2,7,2] (by decide +kernel))
      node_767
      (invalid_excluded a [4,8,6,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,8] (by decide +kernel)))

theorem node_747 : Excluded a [4,8,6,2] :=
  branch_excluded a [4,8,6,2] (by decide)
    (fin9_cases _
      node_748
      node_749
      (invalid_excluded a [4,8,6,2,2] (by decide +kernel))
      node_750
      (invalid_excluded a [4,8,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,6] (by decide +kernel))
      node_758
      (invalid_excluded a [4,8,6,2,8] (by decide +kernel)))

theorem node_771 : Excluded a [4,8,6,5] :=
  source_excluded a [4,8,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_774 : Excluded a [4,8,6,7,0,1] :=
  predecessor_excluded a [4,8,6,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_775 : Excluded a [4,8,6,7,0,2] :=
  source_excluded a [4,8,6,7,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_776 : Excluded a [4,8,6,7,0,3] :=
  predecessor_excluded a [4,8,6,7,0,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_773 : Excluded a [4,8,6,7,0] :=
  branch_excluded a [4,8,6,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,7,0,0] (by decide +kernel))
      node_774
      node_775
      node_776
      (invalid_excluded a [4,8,6,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,0,8] (by decide +kernel)))

theorem node_777 : Excluded a [4,8,6,7,1] :=
  source_excluded a [4,8,6,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_778 : Excluded a [4,8,6,7,2] :=
  predecessor_excluded a [4,8,6,7,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_780 : Excluded a [4,8,6,7,3,0] :=
  source_excluded a [4,8,6,7,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_782 : Excluded a [4,8,6,7,3,1,0] :=
  source_excluded a [4,8,6,7,3,1,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_783 : Excluded a [4,8,6,7,3,1,2] :=
  predecessor_excluded a [4,8,6,7,3,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_786 : Excluded a [4,8,6,7,3,1,5,0,2] :=
  source_excluded a [4,8,6,7,3,1,5,0,2] 1 0 8 (by decide) (by decide +kernel)

theorem node_785 : Excluded a [4,8,6,7,3,1,5,0] :=
  branch_excluded a [4,8,6,7,3,1,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,7,3,1,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,0,1] (by decide +kernel))
      node_786
      (invalid_excluded a [4,8,6,7,3,1,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,0,8] (by decide +kernel)))

theorem node_787 : Excluded a [4,8,6,7,3,1,5,2] :=
  source_excluded a [4,8,6,7,3,1,5,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_784 : Excluded a [4,8,6,7,3,1,5] :=
  branch_excluded a [4,8,6,7,3,1,5] (by decide)
    (fin9_cases _
      node_785
      (invalid_excluded a [4,8,6,7,3,1,5,1] (by decide +kernel))
      node_787
      (invalid_excluded a [4,8,6,7,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,5,8] (by decide +kernel)))

theorem node_781 : Excluded a [4,8,6,7,3,1] :=
  branch_excluded a [4,8,6,7,3,1] (by decide)
    (fin9_cases _
      node_782
      (invalid_excluded a [4,8,6,7,3,1,1] (by decide +kernel))
      node_783
      (invalid_excluded a [4,8,6,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,4] (by decide +kernel))
      node_784
      (invalid_excluded a [4,8,6,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,1,8] (by decide +kernel)))

theorem node_788 : Excluded a [4,8,6,7,3,2] :=
  source_excluded a [4,8,6,7,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_779 : Excluded a [4,8,6,7,3] :=
  branch_excluded a [4,8,6,7,3] (by decide)
    (fin9_cases _
      node_780
      node_781
      node_788
      (invalid_excluded a [4,8,6,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,3,8] (by decide +kernel)))

theorem node_772 : Excluded a [4,8,6,7] :=
  branch_excluded a [4,8,6,7] (by decide)
    (fin9_cases _
      node_773
      node_777
      node_778
      node_779
      (invalid_excluded a [4,8,6,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,7,8] (by decide +kernel)))

theorem node_744 : Excluded a [4,8,6] :=
  branch_excluded a [4,8,6] (by decide)
    (fin9_cases _
      node_745
      node_746
      node_747
      (invalid_excluded a [4,8,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,4] (by decide +kernel))
      node_771
      (invalid_excluded a [4,8,6,6] (by decide +kernel))
      node_772
      (invalid_excluded a [4,8,6,8] (by decide +kernel)))

theorem node_790 : Excluded a [4,8,7,0] :=
  source_excluded a [4,8,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_791 : Excluded a [4,8,7,1] :=
  source_excluded a [4,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_793 : Excluded a [4,8,7,2,0] :=
  predecessor_excluded a [4,8,7,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_794 : Excluded a [4,8,7,2,1] :=
  source_excluded a [4,8,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_797 : Excluded a [4,8,7,2,3,0,1] :=
  predecessor_excluded a [4,8,7,2,3,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_799 : Excluded a [4,8,7,2,3,0,5,1] :=
  source_excluded a [4,8,7,2,3,0,5,1] 7 0 1 (by decide) (by decide +kernel)

theorem node_800 : Excluded a [4,8,7,2,3,0,5,6] :=
  predecessor_excluded a [4,8,7,2,3,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_798 : Excluded a [4,8,7,2,3,0,5] :=
  branch_excluded a [4,8,7,2,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,2,3,0,5,0] (by decide +kernel))
      node_799
      (invalid_excluded a [4,8,7,2,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,0,5,5] (by decide +kernel))
      node_800
      (invalid_excluded a [4,8,7,2,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,0,5,8] (by decide +kernel)))

theorem node_796 : Excluded a [4,8,7,2,3,0] :=
  branch_excluded a [4,8,7,2,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,2,3,0,0] (by decide +kernel))
      node_797
      (invalid_excluded a [4,8,7,2,3,0,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,0,4] (by decide +kernel))
      node_798
      (invalid_excluded a [4,8,7,2,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,0,8] (by decide +kernel)))

theorem node_802 : Excluded a [4,8,7,2,3,1,0] :=
  source_excluded a [4,8,7,2,3,1,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_804 : Excluded a [4,8,7,2,3,1,5,0] :=
  source_excluded a [4,8,7,2,3,1,5,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_805 : Excluded a [4,8,7,2,3,1,5,6] :=
  predecessor_excluded a [4,8,7,2,3,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_803 : Excluded a [4,8,7,2,3,1,5] :=
  branch_excluded a [4,8,7,2,3,1,5] (by decide)
    (fin9_cases _
      node_804
      (invalid_excluded a [4,8,7,2,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,5,5] (by decide +kernel))
      node_805
      (invalid_excluded a [4,8,7,2,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,5,8] (by decide +kernel)))

theorem node_801 : Excluded a [4,8,7,2,3,1] :=
  branch_excluded a [4,8,7,2,3,1] (by decide)
    (fin9_cases _
      node_802
      (invalid_excluded a [4,8,7,2,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,4] (by decide +kernel))
      node_803
      (invalid_excluded a [4,8,7,2,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,1,8] (by decide +kernel)))

theorem node_795 : Excluded a [4,8,7,2,3] :=
  branch_excluded a [4,8,7,2,3] (by decide)
    (fin9_cases _
      node_796
      node_801
      (invalid_excluded a [4,8,7,2,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,3,8] (by decide +kernel)))

theorem node_806 : Excluded a [4,8,7,2,6] :=
  source_excluded a [4,8,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_792 : Excluded a [4,8,7,2] :=
  branch_excluded a [4,8,7,2] (by decide)
    (fin9_cases _
      node_793
      node_794
      (invalid_excluded a [4,8,7,2,2] (by decide +kernel))
      node_795
      (invalid_excluded a [4,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,5] (by decide +kernel))
      node_806
      (invalid_excluded a [4,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,8] (by decide +kernel)))

theorem node_807 : Excluded a [4,8,7,5] :=
  source_excluded a [4,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_810 : Excluded a [4,8,7,6,0,1] :=
  predecessor_excluded a [4,8,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_811 : Excluded a [4,8,7,6,0,2] :=
  predecessor_excluded a [4,8,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_812 : Excluded a [4,8,7,6,0,3] :=
  source_excluded a [4,8,7,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_809 : Excluded a [4,8,7,6,0] :=
  branch_excluded a [4,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,6,0,0] (by decide +kernel))
      node_810
      node_811
      node_812
      (invalid_excluded a [4,8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,8] (by decide +kernel)))

theorem node_813 : Excluded a [4,8,7,6,1] :=
  source_excluded a [4,8,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_814 : Excluded a [4,8,7,6,2] :=
  predecessor_excluded a [4,8,7,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_815 : Excluded a [4,8,7,6,3] :=
  predecessor_excluded a [4,8,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_808 : Excluded a [4,8,7,6] :=
  branch_excluded a [4,8,7,6] (by decide)
    (fin9_cases _
      node_809
      node_813
      node_814
      node_815
      (invalid_excluded a [4,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,8] (by decide +kernel)))

theorem node_789 : Excluded a [4,8,7] :=
  branch_excluded a [4,8,7] (by decide)
    (fin9_cases _
      node_790
      node_791
      node_792
      (invalid_excluded a [4,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,4] (by decide +kernel))
      node_807
      node_808
      (invalid_excluded a [4,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,8] (by decide +kernel)))

theorem node_720 : Excluded a [4,8] :=
  branch_excluded a [4,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,0] (by decide +kernel))
      node_721
      (invalid_excluded a [4,8,2] (by decide +kernel))
      node_722
      (invalid_excluded a [4,8,4] (by decide +kernel))
      node_723
      node_744
      node_789
      (invalid_excluded a [4,8,8] (by decide +kernel)))

theorem node_431 : Excluded a [4] :=
  branch_excluded a [4] (by decide)
    (fin9_cases _
      node_432
      (invalid_excluded a [4,1] (by decide +kernel))
      (invalid_excluded a [4,2] (by decide +kernel))
      node_433
      (invalid_excluded a [4,4] (by decide +kernel))
      node_570
      node_571
      node_658
      node_720)

theorem node_817 : Excluded a [5,0] :=
  source_excluded a [5,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_819 : Excluded a [5,3,1] :=
  source_excluded a [5,3,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_820 : Excluded a [5,3,4] :=
  predecessor_excluded a [5,3,4] 1 5 2 0 (by decide) (by decide +kernel)

theorem node_822 : Excluded a [5,3,6,0] :=
  predecessor_excluded a [5,3,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_824 : Excluded a [5,3,6,1,0] :=
  source_excluded a [5,3,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_825 : Excluded a [5,3,6,1,2] :=
  predecessor_excluded a [5,3,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_827 : Excluded a [5,3,6,1,7,0] :=
  source_excluded a [5,3,6,1,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_828 : Excluded a [5,3,6,1,7,2] :=
  source_excluded a [5,3,6,1,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_829 : Excluded a [5,3,6,1,7,4] :=
  predecessor_excluded a [5,3,6,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_830 : Excluded a [5,3,6,1,7,8] :=
  predecessor_excluded a [5,3,6,1,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_826 : Excluded a [5,3,6,1,7] :=
  branch_excluded a [5,3,6,1,7] (by decide)
    (fin9_cases _
      node_827
      (invalid_excluded a [5,3,6,1,7,1] (by decide +kernel))
      node_828
      (invalid_excluded a [5,3,6,1,7,3] (by decide +kernel))
      node_829
      (invalid_excluded a [5,3,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,7,7] (by decide +kernel))
      node_830)

theorem node_832 : Excluded a [5,3,6,1,8,0] :=
  source_excluded a [5,3,6,1,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_833 : Excluded a [5,3,6,1,8,2] :=
  source_excluded a [5,3,6,1,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_835 : Excluded a [5,3,6,1,8,4,0] :=
  source_excluded a [5,3,6,1,8,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_837 : Excluded a [5,3,6,1,8,4,2,0] :=
  predecessor_excluded a [5,3,6,1,8,4,2,0] 1 0 6 7 (by decide) (by decide +kernel)

theorem node_836 : Excluded a [5,3,6,1,8,4,2] :=
  branch_excluded a [5,3,6,1,8,4,2] (by decide)
    (fin9_cases _
      node_837
      (invalid_excluded a [5,3,6,1,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,2,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,2,8] (by decide +kernel)))

theorem node_834 : Excluded a [5,3,6,1,8,4] :=
  branch_excluded a [5,3,6,1,8,4] (by decide)
    (fin9_cases _
      node_835
      (invalid_excluded a [5,3,6,1,8,4,1] (by decide +kernel))
      node_836
      (invalid_excluded a [5,3,6,1,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,4,8] (by decide +kernel)))

theorem node_838 : Excluded a [5,3,6,1,8,7] :=
  source_excluded a [5,3,6,1,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_831 : Excluded a [5,3,6,1,8] :=
  branch_excluded a [5,3,6,1,8] (by decide)
    (fin9_cases _
      node_832
      (invalid_excluded a [5,3,6,1,8,1] (by decide +kernel))
      node_833
      (invalid_excluded a [5,3,6,1,8,3] (by decide +kernel))
      node_834
      (invalid_excluded a [5,3,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,8,6] (by decide +kernel))
      node_838
      (invalid_excluded a [5,3,6,1,8,8] (by decide +kernel)))

theorem node_823 : Excluded a [5,3,6,1] :=
  branch_excluded a [5,3,6,1] (by decide)
    (fin9_cases _
      node_824
      (invalid_excluded a [5,3,6,1,1] (by decide +kernel))
      node_825
      (invalid_excluded a [5,3,6,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,1,6] (by decide +kernel))
      node_826
      node_831)

theorem node_839 : Excluded a [5,3,6,2] :=
  source_excluded a [5,3,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_841 : Excluded a [5,3,6,7,0] :=
  source_excluded a [5,3,6,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_842 : Excluded a [5,3,6,7,1] :=
  source_excluded a [5,3,6,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_843 : Excluded a [5,3,6,7,2] :=
  predecessor_excluded a [5,3,6,7,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_844 : Excluded a [5,3,6,7,8] :=
  predecessor_excluded a [5,3,6,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_840 : Excluded a [5,3,6,7] :=
  branch_excluded a [5,3,6,7] (by decide)
    (fin9_cases _
      node_841
      node_842
      node_843
      (invalid_excluded a [5,3,6,7,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,7,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,7,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,7,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,7,7] (by decide +kernel))
      node_844)

theorem node_846 : Excluded a [5,3,6,8,0] :=
  source_excluded a [5,3,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_847 : Excluded a [5,3,6,8,1] :=
  source_excluded a [5,3,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_848 : Excluded a [5,3,6,8,2] :=
  predecessor_excluded a [5,3,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_850 : Excluded a [5,3,6,8,7,0] :=
  source_excluded a [5,3,6,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_851 : Excluded a [5,3,6,8,7,1] :=
  source_excluded a [5,3,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_852 : Excluded a [5,3,6,8,7,2] :=
  source_excluded a [5,3,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_853 : Excluded a [5,3,6,8,7,4] :=
  predecessor_excluded a [5,3,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_849 : Excluded a [5,3,6,8,7] :=
  branch_excluded a [5,3,6,8,7] (by decide)
    (fin9_cases _
      node_850
      node_851
      node_852
      (invalid_excluded a [5,3,6,8,7,3] (by decide +kernel))
      node_853
      (invalid_excluded a [5,3,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,7,8] (by decide +kernel)))

theorem node_845 : Excluded a [5,3,6,8] :=
  branch_excluded a [5,3,6,8] (by decide)
    (fin9_cases _
      node_846
      node_847
      node_848
      (invalid_excluded a [5,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,6] (by decide +kernel))
      node_849
      (invalid_excluded a [5,3,6,8,8] (by decide +kernel)))

theorem node_821 : Excluded a [5,3,6] :=
  branch_excluded a [5,3,6] (by decide)
    (fin9_cases _
      node_822
      node_823
      node_839
      (invalid_excluded a [5,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,6] (by decide +kernel))
      node_840
      node_845)

theorem node_855 : Excluded a [5,3,7,0] :=
  predecessor_excluded a [5,3,7,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_857 : Excluded a [5,3,7,1,0] :=
  source_excluded a [5,3,7,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_858 : Excluded a [5,3,7,1,2] :=
  predecessor_excluded a [5,3,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_859 : Excluded a [5,3,7,1,6] :=
  source_excluded a [5,3,7,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_862 : Excluded a [5,3,7,1,8,0,2] :=
  source_excluded a [5,3,7,1,8,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_863 : Excluded a [5,3,7,1,8,0,4] :=
  predecessor_excluded a [5,3,7,1,8,0,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_861 : Excluded a [5,3,7,1,8,0] :=
  branch_excluded a [5,3,7,1,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,7,1,8,0,0] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,0,1] (by decide +kernel))
      node_862
      (invalid_excluded a [5,3,7,1,8,0,3] (by decide +kernel))
      node_863
      (invalid_excluded a [5,3,7,1,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,0,8] (by decide +kernel)))

theorem node_864 : Excluded a [5,3,7,1,8,2] :=
  predecessor_excluded a [5,3,7,1,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_866 : Excluded a [5,3,7,1,8,4,0] :=
  source_excluded a [5,3,7,1,8,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_867 : Excluded a [5,3,7,1,8,4,2] :=
  source_excluded a [5,3,7,1,8,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_865 : Excluded a [5,3,7,1,8,4] :=
  branch_excluded a [5,3,7,1,8,4] (by decide)
    (fin9_cases _
      node_866
      (invalid_excluded a [5,3,7,1,8,4,1] (by decide +kernel))
      node_867
      (invalid_excluded a [5,3,7,1,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,4,8] (by decide +kernel)))

theorem node_860 : Excluded a [5,3,7,1,8] :=
  branch_excluded a [5,3,7,1,8] (by decide)
    (fin9_cases _
      node_861
      (invalid_excluded a [5,3,7,1,8,1] (by decide +kernel))
      node_864
      (invalid_excluded a [5,3,7,1,8,3] (by decide +kernel))
      node_865
      (invalid_excluded a [5,3,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,8,8] (by decide +kernel)))

theorem node_856 : Excluded a [5,3,7,1] :=
  branch_excluded a [5,3,7,1] (by decide)
    (fin9_cases _
      node_857
      (invalid_excluded a [5,3,7,1,1] (by decide +kernel))
      node_858
      (invalid_excluded a [5,3,7,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,1,5] (by decide +kernel))
      node_859
      (invalid_excluded a [5,3,7,1,7] (by decide +kernel))
      node_860)

theorem node_868 : Excluded a [5,3,7,2] :=
  source_excluded a [5,3,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_870 : Excluded a [5,3,7,6,0] :=
  source_excluded a [5,3,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_871 : Excluded a [5,3,7,6,1] :=
  source_excluded a [5,3,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_873 : Excluded a [5,3,7,6,2,0] :=
  predecessor_excluded a [5,3,7,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_874 : Excluded a [5,3,7,6,2,1] :=
  source_excluded a [5,3,7,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_875 : Excluded a [5,3,7,6,2,4] :=
  source_excluded a [5,3,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_877 : Excluded a [5,3,7,6,2,8,0] :=
  source_excluded a [5,3,7,6,2,8,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_879 : Excluded a [5,3,7,6,2,8,1,0] :=
  source_excluded a [5,3,7,6,2,8,1,0] 2 1 7 (by decide) (by decide +kernel)

def b_881 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 7
  | 3 => 6
  | 4 => 2
  | 5 => 8
  | 6 => 1
  | 7 => 4
  | 8 => 0
  | _ => 0

def cert_881 : LosingRegion (edgeOf a b_881) 0 :=
  losingMask a b_881 0 1210109947688349575687168
    (by decide +kernel) (by decide +kernel)

theorem node_881 : Excluded a [5,3,7,6,2,8,1,4,0] :=
  losing_excluded a [5,3,7,6,2,8,1,4,0] (by decide) b_881 (by decide +kernel) 1 0 2 cert_881 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_881 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1210109947688349575687168 1 2; decide +kernel)

theorem node_880 : Excluded a [5,3,7,6,2,8,1,4] :=
  branch_excluded a [5,3,7,6,2,8,1,4] (by decide)
    (fin9_cases _
      node_881
      (invalid_excluded a [5,3,7,6,2,8,1,4,1] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,4,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,4,8] (by decide +kernel)))

theorem node_878 : Excluded a [5,3,7,6,2,8,1] :=
  branch_excluded a [5,3,7,6,2,8,1] (by decide)
    (fin9_cases _
      node_879
      (invalid_excluded a [5,3,7,6,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,3] (by decide +kernel))
      node_880
      (invalid_excluded a [5,3,7,6,2,8,1,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,8] (by decide +kernel)))

theorem node_882 : Excluded a [5,3,7,6,2,8,4] :=
  source_excluded a [5,3,7,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_876 : Excluded a [5,3,7,6,2,8] :=
  branch_excluded a [5,3,7,6,2,8] (by decide)
    (fin9_cases _
      node_877
      node_878
      (invalid_excluded a [5,3,7,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,3] (by decide +kernel))
      node_882
      (invalid_excluded a [5,3,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,8] (by decide +kernel)))

theorem node_872 : Excluded a [5,3,7,6,2] :=
  branch_excluded a [5,3,7,6,2] (by decide)
    (fin9_cases _
      node_873
      node_874
      (invalid_excluded a [5,3,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,3] (by decide +kernel))
      node_875
      (invalid_excluded a [5,3,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,7] (by decide +kernel))
      node_876)

theorem node_885 : Excluded a [5,3,7,6,8,0,1] :=
  predecessor_excluded a [5,3,7,6,8,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_886 : Excluded a [5,3,7,6,8,0,2] :=
  source_excluded a [5,3,7,6,8,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_887 : Excluded a [5,3,7,6,8,0,4] :=
  source_excluded a [5,3,7,6,8,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_884 : Excluded a [5,3,7,6,8,0] :=
  branch_excluded a [5,3,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,7,6,8,0,0] (by decide +kernel))
      node_885
      node_886
      (invalid_excluded a [5,3,7,6,8,0,3] (by decide +kernel))
      node_887
      (invalid_excluded a [5,3,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,0,8] (by decide +kernel)))

theorem node_888 : Excluded a [5,3,7,6,8,1] :=
  source_excluded a [5,3,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_889 : Excluded a [5,3,7,6,8,2] :=
  predecessor_excluded a [5,3,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_890 : Excluded a [5,3,7,6,8,4] :=
  source_excluded a [5,3,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_883 : Excluded a [5,3,7,6,8] :=
  branch_excluded a [5,3,7,6,8] (by decide)
    (fin9_cases _
      node_884
      node_888
      node_889
      (invalid_excluded a [5,3,7,6,8,3] (by decide +kernel))
      node_890
      (invalid_excluded a [5,3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,8] (by decide +kernel)))

theorem node_869 : Excluded a [5,3,7,6] :=
  branch_excluded a [5,3,7,6] (by decide)
    (fin9_cases _
      node_870
      node_871
      node_872
      (invalid_excluded a [5,3,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,7] (by decide +kernel))
      node_883)

theorem node_892 : Excluded a [5,3,7,8,0] :=
  source_excluded a [5,3,7,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_893 : Excluded a [5,3,7,8,1] :=
  source_excluded a [5,3,7,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_895 : Excluded a [5,3,7,8,2,0] :=
  predecessor_excluded a [5,3,7,8,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_896 : Excluded a [5,3,7,8,2,1] :=
  source_excluded a [5,3,7,8,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_898 : Excluded a [5,3,7,8,2,4,0] :=
  source_excluded a [5,3,7,8,2,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_900 : Excluded a [5,3,7,8,2,4,1,0] :=
  source_excluded a [5,3,7,8,2,4,1,0] 2 1 7 (by decide) (by decide +kernel)

def b_902 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 7
  | 3 => 8
  | 4 => 2
  | 5 => 4
  | 6 => 1
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_902 : LosingRegion (edgeOf a b_902) 3 :=
  losingMask a b_902 3 1210107572054918144459841
    (by decide +kernel) (by decide +kernel)

theorem node_902 : Excluded a [5,3,7,8,2,4,1,6,0] :=
  losing_excluded a [5,3,7,8,2,4,1,6,0] (by decide) b_902 (by decide +kernel) 0 3 6 cert_902 (by change 0 ≠ 3 ∧ ¬ edgeOf a b_902 0 3 ∧ 6 ≠ 0 ∧ maskRegion 1210107572054918144459841 0 6; decide +kernel)

theorem node_901 : Excluded a [5,3,7,8,2,4,1,6] :=
  branch_excluded a [5,3,7,8,2,4,1,6] (by decide)
    (fin9_cases _
      node_902
      (invalid_excluded a [5,3,7,8,2,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,6,8] (by decide +kernel)))

theorem node_899 : Excluded a [5,3,7,8,2,4,1] :=
  branch_excluded a [5,3,7,8,2,4,1] (by decide)
    (fin9_cases _
      node_900
      (invalid_excluded a [5,3,7,8,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,5] (by decide +kernel))
      node_901
      (invalid_excluded a [5,3,7,8,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,1,8] (by decide +kernel)))

theorem node_897 : Excluded a [5,3,7,8,2,4] :=
  branch_excluded a [5,3,7,8,2,4] (by decide)
    (fin9_cases _
      node_898
      node_899
      (invalid_excluded a [5,3,7,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,4,8] (by decide +kernel)))

theorem node_894 : Excluded a [5,3,7,8,2] :=
  branch_excluded a [5,3,7,8,2] (by decide)
    (fin9_cases _
      node_895
      node_896
      (invalid_excluded a [5,3,7,8,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,3] (by decide +kernel))
      node_897
      (invalid_excluded a [5,3,7,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,2,8] (by decide +kernel)))

theorem node_903 : Excluded a [5,3,7,8,6] :=
  source_excluded a [5,3,7,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_891 : Excluded a [5,3,7,8] :=
  branch_excluded a [5,3,7,8] (by decide)
    (fin9_cases _
      node_892
      node_893
      node_894
      (invalid_excluded a [5,3,7,8,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,5] (by decide +kernel))
      node_903
      (invalid_excluded a [5,3,7,8,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,8,8] (by decide +kernel)))

theorem node_854 : Excluded a [5,3,7] :=
  branch_excluded a [5,3,7] (by decide)
    (fin9_cases _
      node_855
      node_856
      node_868
      (invalid_excluded a [5,3,7,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,5] (by decide +kernel))
      node_869
      (invalid_excluded a [5,3,7,7] (by decide +kernel))
      node_891)

theorem node_905 : Excluded a [5,3,8,0] :=
  predecessor_excluded a [5,3,8,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_907 : Excluded a [5,3,8,1,0] :=
  source_excluded a [5,3,8,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_908 : Excluded a [5,3,8,1,2] :=
  predecessor_excluded a [5,3,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_909 : Excluded a [5,3,8,1,6] :=
  source_excluded a [5,3,8,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_912 : Excluded a [5,3,8,1,7,0,2] :=
  predecessor_excluded a [5,3,8,1,7,0,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_913 : Excluded a [5,3,8,1,7,0,4] :=
  source_excluded a [5,3,8,1,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_911 : Excluded a [5,3,8,1,7,0] :=
  branch_excluded a [5,3,8,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [5,3,8,1,7,0,1] (by decide +kernel))
      node_912
      (invalid_excluded a [5,3,8,1,7,0,3] (by decide +kernel))
      node_913
      (invalid_excluded a [5,3,8,1,7,0,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,1,7,0,8] (by decide +kernel)))

theorem node_914 : Excluded a [5,3,8,1,7,2] :=
  predecessor_excluded a [5,3,8,1,7,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_915 : Excluded a [5,3,8,1,7,4] :=
  predecessor_excluded a [5,3,8,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_910 : Excluded a [5,3,8,1,7] :=
  branch_excluded a [5,3,8,1,7] (by decide)
    (fin9_cases _
      node_911
      (invalid_excluded a [5,3,8,1,7,1] (by decide +kernel))
      node_914
      (invalid_excluded a [5,3,8,1,7,3] (by decide +kernel))
      node_915
      (invalid_excluded a [5,3,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,1,7,8] (by decide +kernel)))

theorem node_906 : Excluded a [5,3,8,1] :=
  branch_excluded a [5,3,8,1] (by decide)
    (fin9_cases _
      node_907
      (invalid_excluded a [5,3,8,1,1] (by decide +kernel))
      node_908
      (invalid_excluded a [5,3,8,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,1,5] (by decide +kernel))
      node_909
      node_910
      (invalid_excluded a [5,3,8,1,8] (by decide +kernel)))

theorem node_916 : Excluded a [5,3,8,2] :=
  source_excluded a [5,3,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_918 : Excluded a [5,3,8,6,0] :=
  source_excluded a [5,3,8,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_919 : Excluded a [5,3,8,6,1] :=
  source_excluded a [5,3,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_921 : Excluded a [5,3,8,6,2,0] :=
  predecessor_excluded a [5,3,8,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_922 : Excluded a [5,3,8,6,2,1] :=
  source_excluded a [5,3,8,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_923 : Excluded a [5,3,8,6,2,4] :=
  source_excluded a [5,3,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_924 : Excluded a [5,3,8,6,2,7] :=
  source_excluded a [5,3,8,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_920 : Excluded a [5,3,8,6,2] :=
  branch_excluded a [5,3,8,6,2] (by decide)
    (fin9_cases _
      node_921
      node_922
      (invalid_excluded a [5,3,8,6,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,2,3] (by decide +kernel))
      node_923
      (invalid_excluded a [5,3,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,2,6] (by decide +kernel))
      node_924
      (invalid_excluded a [5,3,8,6,2,8] (by decide +kernel)))

theorem node_925 : Excluded a [5,3,8,6,7] :=
  predecessor_excluded a [5,3,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_917 : Excluded a [5,3,8,6] :=
  branch_excluded a [5,3,8,6] (by decide)
    (fin9_cases _
      node_918
      node_919
      node_920
      (invalid_excluded a [5,3,8,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,6] (by decide +kernel))
      node_925
      (invalid_excluded a [5,3,8,6,8] (by decide +kernel)))

theorem node_927 : Excluded a [5,3,8,7,0] :=
  source_excluded a [5,3,8,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_928 : Excluded a [5,3,8,7,1] :=
  source_excluded a [5,3,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_930 : Excluded a [5,3,8,7,2,0] :=
  predecessor_excluded a [5,3,8,7,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_931 : Excluded a [5,3,8,7,2,1] :=
  source_excluded a [5,3,8,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_934 : Excluded a [5,3,8,7,2,4,0,1] :=
  predecessor_excluded a [5,3,8,7,2,4,0,1] 0 3 7 1 (by decide) (by decide +kernel)

theorem node_936 : Excluded a [5,3,8,7,2,4,0,6,1] :=
  source_excluded a [5,3,8,7,2,4,0,6,1] 8 0 1 (by decide) (by decide +kernel)

theorem node_935 : Excluded a [5,3,8,7,2,4,0,6] :=
  branch_excluded a [5,3,8,7,2,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,2,4,0,6,0] (by decide +kernel))
      node_936
      (invalid_excluded a [5,3,8,7,2,4,0,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,8] (by decide +kernel)))

theorem node_933 : Excluded a [5,3,8,7,2,4,0] :=
  branch_excluded a [5,3,8,7,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,2,4,0,0] (by decide +kernel))
      node_934
      (invalid_excluded a [5,3,8,7,2,4,0,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,5] (by decide +kernel))
      node_935
      (invalid_excluded a [5,3,8,7,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,8] (by decide +kernel)))

theorem node_938 : Excluded a [5,3,8,7,2,4,1,0] :=
  source_excluded a [5,3,8,7,2,4,1,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_940 : Excluded a [5,3,8,7,2,4,1,6,0] :=
  source_excluded a [5,3,8,7,2,4,1,6,0] 2 1 8 (by decide) (by decide +kernel)

theorem node_939 : Excluded a [5,3,8,7,2,4,1,6] :=
  branch_excluded a [5,3,8,7,2,4,1,6] (by decide)
    (fin9_cases _
      node_940
      (invalid_excluded a [5,3,8,7,2,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,8] (by decide +kernel)))

theorem node_937 : Excluded a [5,3,8,7,2,4,1] :=
  branch_excluded a [5,3,8,7,2,4,1] (by decide)
    (fin9_cases _
      node_938
      (invalid_excluded a [5,3,8,7,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,5] (by decide +kernel))
      node_939
      (invalid_excluded a [5,3,8,7,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,8] (by decide +kernel)))

theorem node_932 : Excluded a [5,3,8,7,2,4] :=
  branch_excluded a [5,3,8,7,2,4] (by decide)
    (fin9_cases _
      node_933
      node_937
      (invalid_excluded a [5,3,8,7,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,8] (by decide +kernel)))

theorem node_929 : Excluded a [5,3,8,7,2] :=
  branch_excluded a [5,3,8,7,2] (by decide)
    (fin9_cases _
      node_930
      node_931
      (invalid_excluded a [5,3,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,3] (by decide +kernel))
      node_932
      (invalid_excluded a [5,3,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,8] (by decide +kernel)))

theorem node_941 : Excluded a [5,3,8,7,6] :=
  source_excluded a [5,3,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_926 : Excluded a [5,3,8,7] :=
  branch_excluded a [5,3,8,7] (by decide)
    (fin9_cases _
      node_927
      node_928
      node_929
      (invalid_excluded a [5,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,5] (by decide +kernel))
      node_941
      (invalid_excluded a [5,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,8] (by decide +kernel)))

theorem node_904 : Excluded a [5,3,8] :=
  branch_excluded a [5,3,8] (by decide)
    (fin9_cases _
      node_905
      node_906
      node_916
      (invalid_excluded a [5,3,8,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,5] (by decide +kernel))
      node_917
      node_926
      (invalid_excluded a [5,3,8,8] (by decide +kernel)))

theorem node_818 : Excluded a [5,3] :=
  branch_excluded a [5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,0] (by decide +kernel))
      node_819
      (invalid_excluded a [5,3,2] (by decide +kernel))
      (invalid_excluded a [5,3,3] (by decide +kernel))
      node_820
      (invalid_excluded a [5,3,5] (by decide +kernel))
      node_821
      node_854
      node_904)

theorem node_943 : Excluded a [5,4,1] :=
  source_excluded a [5,4,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_945 : Excluded a [5,4,3,0] :=
  source_excluded a [5,4,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_946 : Excluded a [5,4,3,1] :=
  source_excluded a [5,4,3,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_947 : Excluded a [5,4,3,2] :=
  source_excluded a [5,4,3,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_949 : Excluded a [5,4,3,6,0] :=
  source_excluded a [5,4,3,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_950 : Excluded a [5,4,3,6,1] :=
  source_excluded a [5,4,3,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_951 : Excluded a [5,4,3,6,2] :=
  source_excluded a [5,4,3,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_952 : Excluded a [5,4,3,6,7] :=
  predecessor_excluded a [5,4,3,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_955 : Excluded a [5,4,3,6,8,0,1] :=
  predecessor_excluded a [5,4,3,6,8,0,1] 2 1 5 6 (by decide) (by decide +kernel)

def b_958 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 6
  | 4 => 8
  | 5 => 0
  | 6 => 2
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_958 : LosingRegion (edgeOf a b_958) 0 :=
  losingMask a b_958 0 2339408122192977615391744
    (by decide +kernel) (by decide +kernel)

theorem node_958 : Excluded a [5,4,3,6,8,0,2,1,7] :=
  losing_excluded a [5,4,3,6,8,0,2,1,7] (by decide) b_958 (by decide +kernel) 1 0 2 cert_958 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_958 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2339408122192977615391744 1 2; decide +kernel)

theorem node_957 : Excluded a [5,4,3,6,8,0,2,1] :=
  branch_excluded a [5,4,3,6,8,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,6,8,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,1,6] (by decide +kernel))
      node_958
      (invalid_excluded a [5,4,3,6,8,0,2,1,8] (by decide +kernel)))

theorem node_956 : Excluded a [5,4,3,6,8,0,2] :=
  branch_excluded a [5,4,3,6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,6,8,0,2,0] (by decide +kernel))
      node_957
      (invalid_excluded a [5,4,3,6,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,2,8] (by decide +kernel)))

theorem node_954 : Excluded a [5,4,3,6,8,0] :=
  branch_excluded a [5,4,3,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,6,8,0,0] (by decide +kernel))
      node_955
      node_956
      (invalid_excluded a [5,4,3,6,8,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,0,8] (by decide +kernel)))

theorem node_959 : Excluded a [5,4,3,6,8,1] :=
  source_excluded a [5,4,3,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_960 : Excluded a [5,4,3,6,8,2] :=
  predecessor_excluded a [5,4,3,6,8,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_961 : Excluded a [5,4,3,6,8,7] :=
  source_excluded a [5,4,3,6,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_953 : Excluded a [5,4,3,6,8] :=
  branch_excluded a [5,4,3,6,8] (by decide)
    (fin9_cases _
      node_954
      node_959
      node_960
      (invalid_excluded a [5,4,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,8,6] (by decide +kernel))
      node_961
      (invalid_excluded a [5,4,3,6,8,8] (by decide +kernel)))

theorem node_948 : Excluded a [5,4,3,6] :=
  branch_excluded a [5,4,3,6] (by decide)
    (fin9_cases _
      node_949
      node_950
      node_951
      (invalid_excluded a [5,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,6,6] (by decide +kernel))
      node_952
      node_953)

theorem node_963 : Excluded a [5,4,3,7,0] :=
  source_excluded a [5,4,3,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_964 : Excluded a [5,4,3,7,1] :=
  source_excluded a [5,4,3,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_965 : Excluded a [5,4,3,7,2] :=
  source_excluded a [5,4,3,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_966 : Excluded a [5,4,3,7,6] :=
  source_excluded a [5,4,3,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_967 : Excluded a [5,4,3,7,8] :=
  predecessor_excluded a [5,4,3,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_962 : Excluded a [5,4,3,7] :=
  branch_excluded a [5,4,3,7] (by decide)
    (fin9_cases _
      node_963
      node_964
      node_965
      (invalid_excluded a [5,4,3,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,7,5] (by decide +kernel))
      node_966
      (invalid_excluded a [5,4,3,7,7] (by decide +kernel))
      node_967)

theorem node_969 : Excluded a [5,4,3,8,0] :=
  source_excluded a [5,4,3,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_970 : Excluded a [5,4,3,8,1] :=
  source_excluded a [5,4,3,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_971 : Excluded a [5,4,3,8,2] :=
  source_excluded a [5,4,3,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_972 : Excluded a [5,4,3,8,6] :=
  source_excluded a [5,4,3,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_975 : Excluded a [5,4,3,8,7,0,1] :=
  predecessor_excluded a [5,4,3,8,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

def b_978 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 8
  | 4 => 7
  | 5 => 0
  | 6 => 2
  | 7 => 1
  | 8 => 6
  | _ => 0

def cert_978 : LosingRegion (edgeOf a b_978) 0 :=
  losingMask a b_978 0 2301629190330022601165824
    (by decide +kernel) (by decide +kernel)

theorem node_978 : Excluded a [5,4,3,8,7,0,2,1,6] :=
  losing_excluded a [5,4,3,8,7,0,2,1,6] (by decide) b_978 (by decide +kernel) 1 0 2 cert_978 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_978 1 0 ∧ 2 ≠ 1 ∧ maskRegion 2301629190330022601165824 1 2; decide +kernel)

theorem node_977 : Excluded a [5,4,3,8,7,0,2,1] :=
  branch_excluded a [5,4,3,8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,1,5] (by decide +kernel))
      node_978
      (invalid_excluded a [5,4,3,8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,1,8] (by decide +kernel)))

theorem node_979 : Excluded a [5,4,3,8,7,0,2,6] :=
  predecessor_excluded a [5,4,3,8,7,0,2,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_976 : Excluded a [5,4,3,8,7,0,2] :=
  branch_excluded a [5,4,3,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,8,7,0,2,0] (by decide +kernel))
      node_977
      (invalid_excluded a [5,4,3,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,5] (by decide +kernel))
      node_979
      (invalid_excluded a [5,4,3,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,2,8] (by decide +kernel)))

theorem node_974 : Excluded a [5,4,3,8,7,0] :=
  branch_excluded a [5,4,3,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,3,8,7,0,0] (by decide +kernel))
      node_975
      node_976
      (invalid_excluded a [5,4,3,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,0,8] (by decide +kernel)))

theorem node_980 : Excluded a [5,4,3,8,7,1] :=
  source_excluded a [5,4,3,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_981 : Excluded a [5,4,3,8,7,2] :=
  predecessor_excluded a [5,4,3,8,7,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_973 : Excluded a [5,4,3,8,7] :=
  branch_excluded a [5,4,3,8,7] (by decide)
    (fin9_cases _
      node_974
      node_980
      node_981
      (invalid_excluded a [5,4,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,7,8] (by decide +kernel)))

theorem node_968 : Excluded a [5,4,3,8] :=
  branch_excluded a [5,4,3,8] (by decide)
    (fin9_cases _
      node_969
      node_970
      node_971
      (invalid_excluded a [5,4,3,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,8,5] (by decide +kernel))
      node_972
      node_973
      (invalid_excluded a [5,4,3,8,8] (by decide +kernel)))

theorem node_944 : Excluded a [5,4,3] :=
  branch_excluded a [5,4,3] (by decide)
    (fin9_cases _
      node_945
      node_946
      node_947
      (invalid_excluded a [5,4,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,3,5] (by decide +kernel))
      node_948
      node_962
      node_968)

theorem node_983 : Excluded a [5,4,6,0] :=
  predecessor_excluded a [5,4,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_984 : Excluded a [5,4,6,1] :=
  source_excluded a [5,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_985 : Excluded a [5,4,6,2] :=
  source_excluded a [5,4,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_987 : Excluded a [5,4,6,7,0] :=
  source_excluded a [5,4,6,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_988 : Excluded a [5,4,6,7,1] :=
  source_excluded a [5,4,6,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_989 : Excluded a [5,4,6,7,2] :=
  source_excluded a [5,4,6,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_991 : Excluded a [5,4,6,7,3,0] :=
  source_excluded a [5,4,6,7,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_992 : Excluded a [5,4,6,7,3,1] :=
  source_excluded a [5,4,6,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_993 : Excluded a [5,4,6,7,3,2] :=
  source_excluded a [5,4,6,7,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_995 : Excluded a [5,4,6,7,3,8,0] :=
  source_excluded a [5,4,6,7,3,8,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_996 : Excluded a [5,4,6,7,3,8,1] :=
  predecessor_excluded a [5,4,6,7,3,8,1] 3 1 2 6 (by decide) (by decide +kernel)

theorem node_998 : Excluded a [5,4,6,7,3,8,2,0] :=
  predecessor_excluded a [5,4,6,7,3,8,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_1000 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 6
  | 3 => 7
  | 4 => 3
  | 5 => 8
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_1000 : LosingRegion (edgeOf a b_1000) 1 :=
  losingMask a b_1000 1 1228997033614748106620929
    (by decide +kernel) (by decide +kernel)

theorem node_1000 : Excluded a [5,4,6,7,3,8,2,1,0] :=
  losing_excluded a [5,4,6,7,3,8,2,1,0] (by decide) b_1000 (by decide +kernel) 3 1 6 cert_1000 (by change 3 ≠ 1 ∧ ¬ edgeOf a b_1000 3 1 ∧ 6 ≠ 3 ∧ maskRegion 1228997033614748106620929 3 6; decide +kernel)

theorem node_999 : Excluded a [5,4,6,7,3,8,2,1] :=
  branch_excluded a [5,4,6,7,3,8,2,1] (by decide)
    (fin9_cases _
      node_1000
      (invalid_excluded a [5,4,6,7,3,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,1,8] (by decide +kernel)))

theorem node_997 : Excluded a [5,4,6,7,3,8,2] :=
  branch_excluded a [5,4,6,7,3,8,2] (by decide)
    (fin9_cases _
      node_998
      node_999
      (invalid_excluded a [5,4,6,7,3,8,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,2,8] (by decide +kernel)))

theorem node_994 : Excluded a [5,4,6,7,3,8] :=
  branch_excluded a [5,4,6,7,3,8] (by decide)
    (fin9_cases _
      node_995
      node_996
      node_997
      (invalid_excluded a [5,4,6,7,3,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,8,8] (by decide +kernel)))

theorem node_990 : Excluded a [5,4,6,7,3] :=
  branch_excluded a [5,4,6,7,3] (by decide)
    (fin9_cases _
      node_991
      node_992
      node_993
      (invalid_excluded a [5,4,6,7,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,3,7] (by decide +kernel))
      node_994)

theorem node_1001 : Excluded a [5,4,6,7,8] :=
  predecessor_excluded a [5,4,6,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_986 : Excluded a [5,4,6,7] :=
  branch_excluded a [5,4,6,7] (by decide)
    (fin9_cases _
      node_987
      node_988
      node_989
      node_990
      (invalid_excluded a [5,4,6,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,7,7] (by decide +kernel))
      node_1001)

theorem node_1003 : Excluded a [5,4,6,8,0] :=
  source_excluded a [5,4,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1004 : Excluded a [5,4,6,8,1] :=
  source_excluded a [5,4,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1005 : Excluded a [5,4,6,8,2] :=
  source_excluded a [5,4,6,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1006 : Excluded a [5,4,6,8,3] :=
  predecessor_excluded a [5,4,6,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1008 : Excluded a [5,4,6,8,7,0] :=
  source_excluded a [5,4,6,8,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1009 : Excluded a [5,4,6,8,7,1] :=
  source_excluded a [5,4,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1010 : Excluded a [5,4,6,8,7,2] :=
  source_excluded a [5,4,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1012 : Excluded a [5,4,6,8,7,3,0] :=
  source_excluded a [5,4,6,8,7,3,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1013 : Excluded a [5,4,6,8,7,3,1] :=
  predecessor_excluded a [5,4,6,8,7,3,1] 3 1 2 6 (by decide) (by decide +kernel)

theorem node_1015 : Excluded a [5,4,6,8,7,3,2,0] :=
  predecessor_excluded a [5,4,6,8,7,3,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_1017 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 6
  | 3 => 8
  | 4 => 7
  | 5 => 3
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_1017 : LosingRegion (edgeOf a b_1017) 1 :=
  losingMask a b_1017 1 1233719400095144655978497
    (by decide +kernel) (by decide +kernel)

theorem node_1017 : Excluded a [5,4,6,8,7,3,2,1,0] :=
  losing_excluded a [5,4,6,8,7,3,2,1,0] (by decide) b_1017 (by decide +kernel) 3 1 1 cert_1017 (by change 3 ≠ 1 ∧ ¬ edgeOf a b_1017 3 1 ∧ 1 ≠ 3 ∧ maskRegion 1233719400095144655978497 3 1; decide +kernel)

theorem node_1016 : Excluded a [5,4,6,8,7,3,2,1] :=
  branch_excluded a [5,4,6,8,7,3,2,1] (by decide)
    (fin9_cases _
      node_1017
      (invalid_excluded a [5,4,6,8,7,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,1,8] (by decide +kernel)))

theorem node_1014 : Excluded a [5,4,6,8,7,3,2] :=
  branch_excluded a [5,4,6,8,7,3,2] (by decide)
    (fin9_cases _
      node_1015
      node_1016
      (invalid_excluded a [5,4,6,8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,2,8] (by decide +kernel)))

theorem node_1011 : Excluded a [5,4,6,8,7,3] :=
  branch_excluded a [5,4,6,8,7,3] (by decide)
    (fin9_cases _
      node_1012
      node_1013
      node_1014
      (invalid_excluded a [5,4,6,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,3,8] (by decide +kernel)))

theorem node_1007 : Excluded a [5,4,6,8,7] :=
  branch_excluded a [5,4,6,8,7] (by decide)
    (fin9_cases _
      node_1008
      node_1009
      node_1010
      node_1011
      (invalid_excluded a [5,4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,8] (by decide +kernel)))

theorem node_1002 : Excluded a [5,4,6,8] :=
  branch_excluded a [5,4,6,8] (by decide)
    (fin9_cases _
      node_1003
      node_1004
      node_1005
      node_1006
      (invalid_excluded a [5,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,6] (by decide +kernel))
      node_1007
      (invalid_excluded a [5,4,6,8,8] (by decide +kernel)))

theorem node_982 : Excluded a [5,4,6] :=
  branch_excluded a [5,4,6] (by decide)
    (fin9_cases _
      node_983
      node_984
      node_985
      (invalid_excluded a [5,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,6] (by decide +kernel))
      node_986
      node_1002)

theorem node_1019 : Excluded a [5,4,7,0] :=
  predecessor_excluded a [5,4,7,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1020 : Excluded a [5,4,7,1] :=
  source_excluded a [5,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1021 : Excluded a [5,4,7,2] :=
  source_excluded a [5,4,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1023 : Excluded a [5,4,7,6,0] :=
  source_excluded a [5,4,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1024 : Excluded a [5,4,7,6,1] :=
  source_excluded a [5,4,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1025 : Excluded a [5,4,7,6,2] :=
  source_excluded a [5,4,7,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1026 : Excluded a [5,4,7,6,3] :=
  predecessor_excluded a [5,4,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1029 : Excluded a [5,4,7,6,8,0,1] :=
  predecessor_excluded a [5,4,7,6,8,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_1030 : Excluded a [5,4,7,6,8,0,2] :=
  source_excluded a [5,4,7,6,8,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1032 : Excluded a [5,4,7,6,8,0,3,1] :=
  predecessor_excluded a [5,4,7,6,8,0,3,1] 3 1 2 7 (by decide) (by decide +kernel)

theorem node_1034 : Excluded a [5,4,7,6,8,0,3,2,1] :=
  predecessor_excluded a [5,4,7,6,8,0,3,2,1] 0 4 8 1 (by decide) (by decide +kernel)

theorem node_1033 : Excluded a [5,4,7,6,8,0,3,2] :=
  branch_excluded a [5,4,7,6,8,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,7,6,8,0,3,2,0] (by decide +kernel))
      node_1034
      (invalid_excluded a [5,4,7,6,8,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,2,8] (by decide +kernel)))

theorem node_1031 : Excluded a [5,4,7,6,8,0,3] :=
  branch_excluded a [5,4,7,6,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,7,6,8,0,3,0] (by decide +kernel))
      node_1032
      node_1033
      (invalid_excluded a [5,4,7,6,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,3,8] (by decide +kernel)))

theorem node_1028 : Excluded a [5,4,7,6,8,0] :=
  branch_excluded a [5,4,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,7,6,8,0,0] (by decide +kernel))
      node_1029
      node_1030
      node_1031
      (invalid_excluded a [5,4,7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,0,8] (by decide +kernel)))

theorem node_1035 : Excluded a [5,4,7,6,8,1] :=
  source_excluded a [5,4,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1036 : Excluded a [5,4,7,6,8,2] :=
  predecessor_excluded a [5,4,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1037 : Excluded a [5,4,7,6,8,3] :=
  source_excluded a [5,4,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1027 : Excluded a [5,4,7,6,8] :=
  branch_excluded a [5,4,7,6,8] (by decide)
    (fin9_cases _
      node_1028
      node_1035
      node_1036
      node_1037
      (invalid_excluded a [5,4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,8] (by decide +kernel)))

theorem node_1022 : Excluded a [5,4,7,6] :=
  branch_excluded a [5,4,7,6] (by decide)
    (fin9_cases _
      node_1023
      node_1024
      node_1025
      node_1026
      (invalid_excluded a [5,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,7] (by decide +kernel))
      node_1027)

theorem node_1039 : Excluded a [5,4,7,8,0] :=
  source_excluded a [5,4,7,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1040 : Excluded a [5,4,7,8,1] :=
  source_excluded a [5,4,7,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1041 : Excluded a [5,4,7,8,2] :=
  source_excluded a [5,4,7,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1042 : Excluded a [5,4,7,8,3] :=
  predecessor_excluded a [5,4,7,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1043 : Excluded a [5,4,7,8,6] :=
  source_excluded a [5,4,7,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1038 : Excluded a [5,4,7,8] :=
  branch_excluded a [5,4,7,8] (by decide)
    (fin9_cases _
      node_1039
      node_1040
      node_1041
      node_1042
      (invalid_excluded a [5,4,7,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,8,5] (by decide +kernel))
      node_1043
      (invalid_excluded a [5,4,7,8,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,8,8] (by decide +kernel)))

theorem node_1018 : Excluded a [5,4,7] :=
  branch_excluded a [5,4,7] (by decide)
    (fin9_cases _
      node_1019
      node_1020
      node_1021
      (invalid_excluded a [5,4,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,5] (by decide +kernel))
      node_1022
      (invalid_excluded a [5,4,7,7] (by decide +kernel))
      node_1038)

theorem node_1045 : Excluded a [5,4,8,0] :=
  predecessor_excluded a [5,4,8,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1046 : Excluded a [5,4,8,1] :=
  source_excluded a [5,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1047 : Excluded a [5,4,8,2] :=
  source_excluded a [5,4,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1049 : Excluded a [5,4,8,6,0] :=
  source_excluded a [5,4,8,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1050 : Excluded a [5,4,8,6,1] :=
  source_excluded a [5,4,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1051 : Excluded a [5,4,8,6,2] :=
  source_excluded a [5,4,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1052 : Excluded a [5,4,8,6,3] :=
  predecessor_excluded a [5,4,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1053 : Excluded a [5,4,8,6,7] :=
  predecessor_excluded a [5,4,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1048 : Excluded a [5,4,8,6] :=
  branch_excluded a [5,4,8,6] (by decide)
    (fin9_cases _
      node_1049
      node_1050
      node_1051
      node_1052
      (invalid_excluded a [5,4,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,6,6] (by decide +kernel))
      node_1053
      (invalid_excluded a [5,4,8,6,8] (by decide +kernel)))

theorem node_1055 : Excluded a [5,4,8,7,0] :=
  source_excluded a [5,4,8,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1056 : Excluded a [5,4,8,7,1] :=
  source_excluded a [5,4,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1057 : Excluded a [5,4,8,7,2] :=
  source_excluded a [5,4,8,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1060 : Excluded a [5,4,8,7,3,0,1] :=
  predecessor_excluded a [5,4,8,7,3,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_1061 : Excluded a [5,4,8,7,3,0,2] :=
  predecessor_excluded a [5,4,8,7,3,0,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1059 : Excluded a [5,4,8,7,3,0] :=
  branch_excluded a [5,4,8,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,8,7,3,0,0] (by decide +kernel))
      node_1060
      node_1061
      (invalid_excluded a [5,4,8,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,0,8] (by decide +kernel)))

theorem node_1062 : Excluded a [5,4,8,7,3,1] :=
  source_excluded a [5,4,8,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1063 : Excluded a [5,4,8,7,3,2] :=
  predecessor_excluded a [5,4,8,7,3,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_1058 : Excluded a [5,4,8,7,3] :=
  branch_excluded a [5,4,8,7,3] (by decide)
    (fin9_cases _
      node_1059
      node_1062
      node_1063
      (invalid_excluded a [5,4,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,3,8] (by decide +kernel)))

theorem node_1064 : Excluded a [5,4,8,7,6] :=
  source_excluded a [5,4,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1054 : Excluded a [5,4,8,7] :=
  branch_excluded a [5,4,8,7] (by decide)
    (fin9_cases _
      node_1055
      node_1056
      node_1057
      node_1058
      (invalid_excluded a [5,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,5] (by decide +kernel))
      node_1064
      (invalid_excluded a [5,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,8] (by decide +kernel)))

theorem node_1044 : Excluded a [5,4,8] :=
  branch_excluded a [5,4,8] (by decide)
    (fin9_cases _
      node_1045
      node_1046
      node_1047
      (invalid_excluded a [5,4,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,5] (by decide +kernel))
      node_1048
      node_1054
      (invalid_excluded a [5,4,8,8] (by decide +kernel)))

theorem node_942 : Excluded a [5,4] :=
  branch_excluded a [5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0] (by decide +kernel))
      node_943
      (invalid_excluded a [5,4,2] (by decide +kernel))
      node_944
      (invalid_excluded a [5,4,4] (by decide +kernel))
      (invalid_excluded a [5,4,5] (by decide +kernel))
      node_982
      node_1018
      node_1044)

theorem node_1065 : Excluded a [5,6] :=
  predecessor_excluded a [5,6] 2 6 0 1 (by decide) (by decide +kernel)

theorem node_1067 : Excluded a [5,7,1] :=
  source_excluded a [5,7,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1069 : Excluded a [5,7,3,0] :=
  source_excluded a [5,7,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1070 : Excluded a [5,7,3,1] :=
  predecessor_excluded a [5,7,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_1072 : Excluded a [5,7,3,2,0] :=
  source_excluded a [5,7,3,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1073 : Excluded a [5,7,3,2,1] :=
  source_excluded a [5,7,3,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1074 : Excluded a [5,7,3,2,6] :=
  source_excluded a [5,7,3,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1077 : Excluded a [5,7,3,2,8,0,1] :=
  source_excluded a [5,7,3,2,8,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1078 : Excluded a [5,7,3,2,8,0,4] :=
  predecessor_excluded a [5,7,3,2,8,0,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1076 : Excluded a [5,7,3,2,8,0] :=
  branch_excluded a [5,7,3,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,3,2,8,0,0] (by decide +kernel))
      node_1077
      (invalid_excluded a [5,7,3,2,8,0,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,0,3] (by decide +kernel))
      node_1078
      (invalid_excluded a [5,7,3,2,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,0,8] (by decide +kernel)))

theorem node_1079 : Excluded a [5,7,3,2,8,1] :=
  source_excluded a [5,7,3,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1082 : Excluded a [5,7,3,2,8,4,0,1] :=
  predecessor_excluded a [5,7,3,2,8,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_1084 : Excluded a [5,7,3,2,8,4,0,6,1] :=
  predecessor_excluded a [5,7,3,2,8,4,0,6,1] 0 2 8 3 (by decide) (by decide +kernel)

theorem node_1083 : Excluded a [5,7,3,2,8,4,0,6] :=
  branch_excluded a [5,7,3,2,8,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,3,2,8,4,0,6,0] (by decide +kernel))
      node_1084
      (invalid_excluded a [5,7,3,2,8,4,0,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,6,8] (by decide +kernel)))

theorem node_1081 : Excluded a [5,7,3,2,8,4,0] :=
  branch_excluded a [5,7,3,2,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,3,2,8,4,0,0] (by decide +kernel))
      node_1082
      (invalid_excluded a [5,7,3,2,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,5] (by decide +kernel))
      node_1083
      (invalid_excluded a [5,7,3,2,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,0,8] (by decide +kernel)))

theorem node_1085 : Excluded a [5,7,3,2,8,4,1] :=
  source_excluded a [5,7,3,2,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1080 : Excluded a [5,7,3,2,8,4] :=
  branch_excluded a [5,7,3,2,8,4] (by decide)
    (fin9_cases _
      node_1081
      node_1085
      (invalid_excluded a [5,7,3,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,4,8] (by decide +kernel)))

theorem node_1075 : Excluded a [5,7,3,2,8] :=
  branch_excluded a [5,7,3,2,8] (by decide)
    (fin9_cases _
      node_1076
      node_1079
      (invalid_excluded a [5,7,3,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,3] (by decide +kernel))
      node_1080
      (invalid_excluded a [5,7,3,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,8,8] (by decide +kernel)))

theorem node_1071 : Excluded a [5,7,3,2] :=
  branch_excluded a [5,7,3,2] (by decide)
    (fin9_cases _
      node_1072
      node_1073
      (invalid_excluded a [5,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,2,5] (by decide +kernel))
      node_1074
      (invalid_excluded a [5,7,3,2,7] (by decide +kernel))
      node_1075)

theorem node_1087 : Excluded a [5,7,3,6,0] :=
  source_excluded a [5,7,3,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1088 : Excluded a [5,7,3,6,1] :=
  source_excluded a [5,7,3,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1090 : Excluded a [5,7,3,6,2,0] :=
  predecessor_excluded a [5,7,3,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1091 : Excluded a [5,7,3,6,2,1] :=
  source_excluded a [5,7,3,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1092 : Excluded a [5,7,3,6,2,4] :=
  source_excluded a [5,7,3,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1095 : Excluded a [5,7,3,6,2,8,0,1] :=
  predecessor_excluded a [5,7,3,6,2,8,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_1097 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 7
  | 2 => 3
  | 3 => 6
  | 4 => 2
  | 5 => 8
  | 6 => 0
  | 7 => 4
  | 8 => 1
  | _ => 0

def cert_1097 : LosingRegion (edgeOf a b_1097) 0 :=
  losingMask a b_1097 0 1267052664521142926584832
    (by decide +kernel) (by decide +kernel)

theorem node_1097 : Excluded a [5,7,3,6,2,8,0,4,1] :=
  losing_excluded a [5,7,3,6,2,8,0,4,1] (by decide) b_1097 (by decide +kernel) 1 0 2 cert_1097 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1097 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1267052664521142926584832 1 2; decide +kernel)

theorem node_1096 : Excluded a [5,7,3,6,2,8,0,4] :=
  branch_excluded a [5,7,3,6,2,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,3,6,2,8,0,4,0] (by decide +kernel))
      node_1097
      (invalid_excluded a [5,7,3,6,2,8,0,4,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,4,8] (by decide +kernel)))

theorem node_1094 : Excluded a [5,7,3,6,2,8,0] :=
  branch_excluded a [5,7,3,6,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,3,6,2,8,0,0] (by decide +kernel))
      node_1095
      (invalid_excluded a [5,7,3,6,2,8,0,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,3] (by decide +kernel))
      node_1096
      (invalid_excluded a [5,7,3,6,2,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,0,8] (by decide +kernel)))

theorem node_1098 : Excluded a [5,7,3,6,2,8,1] :=
  source_excluded a [5,7,3,6,2,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1099 : Excluded a [5,7,3,6,2,8,4] :=
  source_excluded a [5,7,3,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1093 : Excluded a [5,7,3,6,2,8] :=
  branch_excluded a [5,7,3,6,2,8] (by decide)
    (fin9_cases _
      node_1094
      node_1098
      (invalid_excluded a [5,7,3,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,3] (by decide +kernel))
      node_1099
      (invalid_excluded a [5,7,3,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,8,8] (by decide +kernel)))

theorem node_1089 : Excluded a [5,7,3,6,2] :=
  branch_excluded a [5,7,3,6,2] (by decide)
    (fin9_cases _
      node_1090
      node_1091
      (invalid_excluded a [5,7,3,6,2,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,3] (by decide +kernel))
      node_1092
      (invalid_excluded a [5,7,3,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,2,7] (by decide +kernel))
      node_1093)

theorem node_1102 : Excluded a [5,7,3,6,8,0,1] :=
  source_excluded a [5,7,3,6,8,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1103 : Excluded a [5,7,3,6,8,0,2] :=
  source_excluded a [5,7,3,6,8,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_1104 : Excluded a [5,7,3,6,8,0,4] :=
  source_excluded a [5,7,3,6,8,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1101 : Excluded a [5,7,3,6,8,0] :=
  branch_excluded a [5,7,3,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,3,6,8,0,0] (by decide +kernel))
      node_1102
      node_1103
      (invalid_excluded a [5,7,3,6,8,0,3] (by decide +kernel))
      node_1104
      (invalid_excluded a [5,7,3,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,8,0,8] (by decide +kernel)))

theorem node_1105 : Excluded a [5,7,3,6,8,1] :=
  source_excluded a [5,7,3,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1106 : Excluded a [5,7,3,6,8,2] :=
  predecessor_excluded a [5,7,3,6,8,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_1107 : Excluded a [5,7,3,6,8,4] :=
  source_excluded a [5,7,3,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1100 : Excluded a [5,7,3,6,8] :=
  branch_excluded a [5,7,3,6,8] (by decide)
    (fin9_cases _
      node_1101
      node_1105
      node_1106
      (invalid_excluded a [5,7,3,6,8,3] (by decide +kernel))
      node_1107
      (invalid_excluded a [5,7,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,8,8] (by decide +kernel)))

theorem node_1086 : Excluded a [5,7,3,6] :=
  branch_excluded a [5,7,3,6] (by decide)
    (fin9_cases _
      node_1087
      node_1088
      node_1089
      (invalid_excluded a [5,7,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,6,7] (by decide +kernel))
      node_1100)

theorem node_1109 : Excluded a [5,7,3,8,0] :=
  source_excluded a [5,7,3,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1110 : Excluded a [5,7,3,8,1] :=
  source_excluded a [5,7,3,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1112 : Excluded a [5,7,3,8,2,0] :=
  predecessor_excluded a [5,7,3,8,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1113 : Excluded a [5,7,3,8,2,1] :=
  source_excluded a [5,7,3,8,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1116 : Excluded a [5,7,3,8,2,4,0,1] :=
  predecessor_excluded a [5,7,3,8,2,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_1118 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 7
  | 2 => 3
  | 3 => 8
  | 4 => 2
  | 5 => 4
  | 6 => 0
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_1118 : LosingRegion (edgeOf a b_1118) 0 :=
  losingMask a b_1118 0 1480167898522965964235776
    (by decide +kernel) (by decide +kernel)

theorem node_1118 : Excluded a [5,7,3,8,2,4,0,6,1] :=
  losing_excluded a [5,7,3,8,2,4,0,6,1] (by decide) b_1118 (by decide +kernel) 1 0 4 cert_1118 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1118 1 0 ∧ 4 ≠ 1 ∧ maskRegion 1480167898522965964235776 1 4; decide +kernel)

theorem node_1117 : Excluded a [5,7,3,8,2,4,0,6] :=
  branch_excluded a [5,7,3,8,2,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,3,8,2,4,0,6,0] (by decide +kernel))
      node_1118
      (invalid_excluded a [5,7,3,8,2,4,0,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,6,8] (by decide +kernel)))

theorem node_1115 : Excluded a [5,7,3,8,2,4,0] :=
  branch_excluded a [5,7,3,8,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,3,8,2,4,0,0] (by decide +kernel))
      node_1116
      (invalid_excluded a [5,7,3,8,2,4,0,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,5] (by decide +kernel))
      node_1117
      (invalid_excluded a [5,7,3,8,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,0,8] (by decide +kernel)))

theorem node_1119 : Excluded a [5,7,3,8,2,4,1] :=
  source_excluded a [5,7,3,8,2,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1114 : Excluded a [5,7,3,8,2,4] :=
  branch_excluded a [5,7,3,8,2,4] (by decide)
    (fin9_cases _
      node_1115
      node_1119
      (invalid_excluded a [5,7,3,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,4,8] (by decide +kernel)))

theorem node_1111 : Excluded a [5,7,3,8,2] :=
  branch_excluded a [5,7,3,8,2] (by decide)
    (fin9_cases _
      node_1112
      node_1113
      (invalid_excluded a [5,7,3,8,2,2] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,3] (by decide +kernel))
      node_1114
      (invalid_excluded a [5,7,3,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,2,8] (by decide +kernel)))

theorem node_1120 : Excluded a [5,7,3,8,6] :=
  source_excluded a [5,7,3,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1108 : Excluded a [5,7,3,8] :=
  branch_excluded a [5,7,3,8] (by decide)
    (fin9_cases _
      node_1109
      node_1110
      node_1111
      (invalid_excluded a [5,7,3,8,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,5] (by decide +kernel))
      node_1120
      (invalid_excluded a [5,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,3,8,8] (by decide +kernel)))

theorem node_1068 : Excluded a [5,7,3] :=
  branch_excluded a [5,7,3] (by decide)
    (fin9_cases _
      node_1069
      node_1070
      node_1071
      (invalid_excluded a [5,7,3,3] (by decide +kernel))
      (invalid_excluded a [5,7,3,4] (by decide +kernel))
      (invalid_excluded a [5,7,3,5] (by decide +kernel))
      node_1086
      (invalid_excluded a [5,7,3,7] (by decide +kernel))
      node_1108)

theorem node_1121 : Excluded a [5,7,4] :=
  predecessor_excluded a [5,7,4] 1 5 2 0 (by decide) (by decide +kernel)

theorem node_1123 : Excluded a [5,7,6,0] :=
  predecessor_excluded a [5,7,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1125 : Excluded a [5,7,6,1,0] :=
  source_excluded a [5,7,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1126 : Excluded a [5,7,6,1,2] :=
  predecessor_excluded a [5,7,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1128 : Excluded a [5,7,6,1,3,0] :=
  source_excluded a [5,7,6,1,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1129 : Excluded a [5,7,6,1,3,2] :=
  source_excluded a [5,7,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1130 : Excluded a [5,7,6,1,3,4] :=
  predecessor_excluded a [5,7,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1132 : Excluded a [5,7,6,1,3,8,0] :=
  source_excluded a [5,7,6,1,3,8,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1133 : Excluded a [5,7,6,1,3,8,2] :=
  source_excluded a [5,7,6,1,3,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_1135 : Excluded a [5,7,6,1,3,8,4,0] :=
  predecessor_excluded a [5,7,6,1,3,8,4,0] 3 0 1 7 (by decide) (by decide +kernel)

theorem node_1136 : Excluded a [5,7,6,1,3,8,4,2] :=
  source_excluded a [5,7,6,1,3,8,4,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_1134 : Excluded a [5,7,6,1,3,8,4] :=
  branch_excluded a [5,7,6,1,3,8,4] (by decide)
    (fin9_cases _
      node_1135
      (invalid_excluded a [5,7,6,1,3,8,4,1] (by decide +kernel))
      node_1136
      (invalid_excluded a [5,7,6,1,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,4,8] (by decide +kernel)))

theorem node_1131 : Excluded a [5,7,6,1,3,8] :=
  branch_excluded a [5,7,6,1,3,8] (by decide)
    (fin9_cases _
      node_1132
      (invalid_excluded a [5,7,6,1,3,8,1] (by decide +kernel))
      node_1133
      (invalid_excluded a [5,7,6,1,3,8,3] (by decide +kernel))
      node_1134
      (invalid_excluded a [5,7,6,1,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,8] (by decide +kernel)))

theorem node_1127 : Excluded a [5,7,6,1,3] :=
  branch_excluded a [5,7,6,1,3] (by decide)
    (fin9_cases _
      node_1128
      (invalid_excluded a [5,7,6,1,3,1] (by decide +kernel))
      node_1129
      (invalid_excluded a [5,7,6,1,3,3] (by decide +kernel))
      node_1130
      (invalid_excluded a [5,7,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,7] (by decide +kernel))
      node_1131)

theorem node_1138 : Excluded a [5,7,6,1,8,0] :=
  source_excluded a [5,7,6,1,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1139 : Excluded a [5,7,6,1,8,2] :=
  source_excluded a [5,7,6,1,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1140 : Excluded a [5,7,6,1,8,3] :=
  predecessor_excluded a [5,7,6,1,8,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1142 : Excluded a [5,7,6,1,8,4,0] :=
  source_excluded a [5,7,6,1,8,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1143 : Excluded a [5,7,6,1,8,4,2] :=
  source_excluded a [5,7,6,1,8,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_1145 : Excluded a [5,7,6,1,8,4,3,0] :=
  predecessor_excluded a [5,7,6,1,8,4,3,0] 3 0 1 7 (by decide) (by decide +kernel)

theorem node_1146 : Excluded a [5,7,6,1,8,4,3,2] :=
  source_excluded a [5,7,6,1,8,4,3,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_1144 : Excluded a [5,7,6,1,8,4,3] :=
  branch_excluded a [5,7,6,1,8,4,3] (by decide)
    (fin9_cases _
      node_1145
      (invalid_excluded a [5,7,6,1,8,4,3,1] (by decide +kernel))
      node_1146
      (invalid_excluded a [5,7,6,1,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,3,8] (by decide +kernel)))

theorem node_1141 : Excluded a [5,7,6,1,8,4] :=
  branch_excluded a [5,7,6,1,8,4] (by decide)
    (fin9_cases _
      node_1142
      (invalid_excluded a [5,7,6,1,8,4,1] (by decide +kernel))
      node_1143
      node_1144
      (invalid_excluded a [5,7,6,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,8] (by decide +kernel)))

theorem node_1137 : Excluded a [5,7,6,1,8] :=
  branch_excluded a [5,7,6,1,8] (by decide)
    (fin9_cases _
      node_1138
      (invalid_excluded a [5,7,6,1,8,1] (by decide +kernel))
      node_1139
      node_1140
      node_1141
      (invalid_excluded a [5,7,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,8] (by decide +kernel)))

theorem node_1124 : Excluded a [5,7,6,1] :=
  branch_excluded a [5,7,6,1] (by decide)
    (fin9_cases _
      node_1125
      (invalid_excluded a [5,7,6,1,1] (by decide +kernel))
      node_1126
      node_1127
      (invalid_excluded a [5,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,7] (by decide +kernel))
      node_1137)

theorem node_1148 : Excluded a [5,7,6,2,0] :=
  source_excluded a [5,7,6,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1149 : Excluded a [5,7,6,2,1] :=
  source_excluded a [5,7,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1151 : Excluded a [5,7,6,2,3,0] :=
  source_excluded a [5,7,6,2,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1152 : Excluded a [5,7,6,2,3,1] :=
  source_excluded a [5,7,6,2,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1153 : Excluded a [5,7,6,2,3,4] :=
  predecessor_excluded a [5,7,6,2,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1155 : Excluded a [5,7,6,2,3,8,0] :=
  source_excluded a [5,7,6,2,3,8,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1156 : Excluded a [5,7,6,2,3,8,1] :=
  source_excluded a [5,7,6,2,3,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1158 : Excluded a [5,7,6,2,3,8,4,0] :=
  predecessor_excluded a [5,7,6,2,3,8,4,0] 3 0 1 7 (by decide) (by decide +kernel)

def b_1160 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 7
  | 2 => 6
  | 3 => 2
  | 4 => 3
  | 5 => 8
  | 6 => 4
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_1160 : LosingRegion (edgeOf a b_1160) 0 :=
  losingMask a b_1160 0 1210109911668260602905600
    (by decide +kernel) (by decide +kernel)

theorem node_1160 : Excluded a [5,7,6,2,3,8,4,1,0] :=
  losing_excluded a [5,7,6,2,3,8,4,1,0] (by decide) b_1160 (by decide +kernel) 3 0 1 cert_1160 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1160 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1210109911668260602905600 3 1; decide +kernel)

theorem node_1159 : Excluded a [5,7,6,2,3,8,4,1] :=
  branch_excluded a [5,7,6,2,3,8,4,1] (by decide)
    (fin9_cases _
      node_1160
      (invalid_excluded a [5,7,6,2,3,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,1,8] (by decide +kernel)))

theorem node_1157 : Excluded a [5,7,6,2,3,8,4] :=
  branch_excluded a [5,7,6,2,3,8,4] (by decide)
    (fin9_cases _
      node_1158
      node_1159
      (invalid_excluded a [5,7,6,2,3,8,4,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,4,8] (by decide +kernel)))

theorem node_1154 : Excluded a [5,7,6,2,3,8] :=
  branch_excluded a [5,7,6,2,3,8] (by decide)
    (fin9_cases _
      node_1155
      node_1156
      (invalid_excluded a [5,7,6,2,3,8,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,3] (by decide +kernel))
      node_1157
      (invalid_excluded a [5,7,6,2,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,8,8] (by decide +kernel)))

theorem node_1150 : Excluded a [5,7,6,2,3] :=
  branch_excluded a [5,7,6,2,3] (by decide)
    (fin9_cases _
      node_1151
      node_1152
      (invalid_excluded a [5,7,6,2,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,3] (by decide +kernel))
      node_1153
      (invalid_excluded a [5,7,6,2,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,3,7] (by decide +kernel))
      node_1154)

theorem node_1162 : Excluded a [5,7,6,2,8,0] :=
  source_excluded a [5,7,6,2,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1163 : Excluded a [5,7,6,2,8,1] :=
  source_excluded a [5,7,6,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1164 : Excluded a [5,7,6,2,8,3] :=
  predecessor_excluded a [5,7,6,2,8,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1166 : Excluded a [5,7,6,2,8,4,0] :=
  source_excluded a [5,7,6,2,8,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1167 : Excluded a [5,7,6,2,8,4,1] :=
  source_excluded a [5,7,6,2,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1169 : Excluded a [5,7,6,2,8,4,3,0] :=
  predecessor_excluded a [5,7,6,2,8,4,3,0] 3 0 1 7 (by decide) (by decide +kernel)

def b_1171 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 7
  | 2 => 6
  | 3 => 2
  | 4 => 8
  | 5 => 4
  | 6 => 3
  | 7 => 1
  | 8 => 0
  | _ => 0

def cert_1171 : LosingRegion (edgeOf a b_1171) 0 :=
  losingMask a b_1171 0 1210109913990222465467392
    (by decide +kernel) (by decide +kernel)

theorem node_1171 : Excluded a [5,7,6,2,8,4,3,1,0] :=
  losing_excluded a [5,7,6,2,8,4,3,1,0] (by decide) b_1171 (by decide +kernel) 3 0 1 cert_1171 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1171 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1210109913990222465467392 3 1; decide +kernel)

theorem node_1170 : Excluded a [5,7,6,2,8,4,3,1] :=
  branch_excluded a [5,7,6,2,8,4,3,1] (by decide)
    (fin9_cases _
      node_1171
      (invalid_excluded a [5,7,6,2,8,4,3,1,1] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,1,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,1,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,1,8] (by decide +kernel)))

theorem node_1168 : Excluded a [5,7,6,2,8,4,3] :=
  branch_excluded a [5,7,6,2,8,4,3] (by decide)
    (fin9_cases _
      node_1169
      node_1170
      (invalid_excluded a [5,7,6,2,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,3,8] (by decide +kernel)))

theorem node_1165 : Excluded a [5,7,6,2,8,4] :=
  branch_excluded a [5,7,6,2,8,4] (by decide)
    (fin9_cases _
      node_1166
      node_1167
      (invalid_excluded a [5,7,6,2,8,4,2] (by decide +kernel))
      node_1168
      (invalid_excluded a [5,7,6,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,8] (by decide +kernel)))

theorem node_1161 : Excluded a [5,7,6,2,8] :=
  branch_excluded a [5,7,6,2,8] (by decide)
    (fin9_cases _
      node_1162
      node_1163
      (invalid_excluded a [5,7,6,2,8,2] (by decide +kernel))
      node_1164
      node_1165
      (invalid_excluded a [5,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,8] (by decide +kernel)))

theorem node_1147 : Excluded a [5,7,6,2] :=
  branch_excluded a [5,7,6,2] (by decide)
    (fin9_cases _
      node_1148
      node_1149
      (invalid_excluded a [5,7,6,2,2] (by decide +kernel))
      node_1150
      (invalid_excluded a [5,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,7] (by decide +kernel))
      node_1161)

theorem node_1173 : Excluded a [5,7,6,8,0] :=
  source_excluded a [5,7,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1174 : Excluded a [5,7,6,8,1] :=
  source_excluded a [5,7,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1175 : Excluded a [5,7,6,8,2] :=
  predecessor_excluded a [5,7,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1176 : Excluded a [5,7,6,8,3] :=
  predecessor_excluded a [5,7,6,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1172 : Excluded a [5,7,6,8] :=
  branch_excluded a [5,7,6,8] (by decide)
    (fin9_cases _
      node_1173
      node_1174
      node_1175
      node_1176
      (invalid_excluded a [5,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,8] (by decide +kernel)))

theorem node_1122 : Excluded a [5,7,6] :=
  branch_excluded a [5,7,6] (by decide)
    (fin9_cases _
      node_1123
      node_1124
      node_1147
      (invalid_excluded a [5,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,7] (by decide +kernel))
      node_1172)

theorem node_1177 : Excluded a [5,7,8] :=
  predecessor_excluded a [5,7,8] 0 8 1 2 (by decide) (by decide +kernel)

theorem node_1066 : Excluded a [5,7] :=
  branch_excluded a [5,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0] (by decide +kernel))
      node_1067
      (invalid_excluded a [5,7,2] (by decide +kernel))
      node_1068
      node_1121
      (invalid_excluded a [5,7,5] (by decide +kernel))
      node_1122
      (invalid_excluded a [5,7,7] (by decide +kernel))
      node_1177)

theorem node_1179 : Excluded a [5,8,1] :=
  source_excluded a [5,8,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1180 : Excluded a [5,8,3] :=
  predecessor_excluded a [5,8,3] 0 3 1 2 (by decide) (by decide +kernel)

theorem node_1181 : Excluded a [5,8,4] :=
  predecessor_excluded a [5,8,4] 1 5 2 0 (by decide) (by decide +kernel)

theorem node_1183 : Excluded a [5,8,6,0] :=
  predecessor_excluded a [5,8,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1185 : Excluded a [5,8,6,1,0] :=
  source_excluded a [5,8,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1186 : Excluded a [5,8,6,1,2] :=
  predecessor_excluded a [5,8,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1188 : Excluded a [5,8,6,1,3,0] :=
  source_excluded a [5,8,6,1,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1189 : Excluded a [5,8,6,1,3,2] :=
  source_excluded a [5,8,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1190 : Excluded a [5,8,6,1,3,4] :=
  predecessor_excluded a [5,8,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1191 : Excluded a [5,8,6,1,3,7] :=
  source_excluded a [5,8,6,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1187 : Excluded a [5,8,6,1,3] :=
  branch_excluded a [5,8,6,1,3] (by decide)
    (fin9_cases _
      node_1188
      (invalid_excluded a [5,8,6,1,3,1] (by decide +kernel))
      node_1189
      (invalid_excluded a [5,8,6,1,3,3] (by decide +kernel))
      node_1190
      (invalid_excluded a [5,8,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,6] (by decide +kernel))
      node_1191
      (invalid_excluded a [5,8,6,1,3,8] (by decide +kernel)))

theorem node_1193 : Excluded a [5,8,6,1,7,0] :=
  source_excluded a [5,8,6,1,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1194 : Excluded a [5,8,6,1,7,2] :=
  source_excluded a [5,8,6,1,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1196 : Excluded a [5,8,6,1,7,3,0] :=
  source_excluded a [5,8,6,1,7,3,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1198 : Excluded a [5,8,6,1,7,3,2,0] :=
  predecessor_excluded a [5,8,6,1,7,3,2,0] 1 0 6 7 (by decide) (by decide +kernel)

theorem node_1200 : Excluded a [5,8,6,1,7,3,2,4,0] :=
  predecessor_excluded a [5,8,6,1,7,3,2,4,0] 2 1 8 3 (by decide) (by decide +kernel)

theorem node_1199 : Excluded a [5,8,6,1,7,3,2,4] :=
  branch_excluded a [5,8,6,1,7,3,2,4] (by decide)
    (fin9_cases _
      node_1200
      (invalid_excluded a [5,8,6,1,7,3,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,4,8] (by decide +kernel)))

theorem node_1197 : Excluded a [5,8,6,1,7,3,2] :=
  branch_excluded a [5,8,6,1,7,3,2] (by decide)
    (fin9_cases _
      node_1198
      (invalid_excluded a [5,8,6,1,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,3] (by decide +kernel))
      node_1199
      (invalid_excluded a [5,8,6,1,7,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,2,8] (by decide +kernel)))

theorem node_1201 : Excluded a [5,8,6,1,7,3,4] :=
  source_excluded a [5,8,6,1,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1195 : Excluded a [5,8,6,1,7,3] :=
  branch_excluded a [5,8,6,1,7,3] (by decide)
    (fin9_cases _
      node_1196
      (invalid_excluded a [5,8,6,1,7,3,1] (by decide +kernel))
      node_1197
      (invalid_excluded a [5,8,6,1,7,3,3] (by decide +kernel))
      node_1201
      (invalid_excluded a [5,8,6,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,3,8] (by decide +kernel)))

theorem node_1202 : Excluded a [5,8,6,1,7,4] :=
  predecessor_excluded a [5,8,6,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1192 : Excluded a [5,8,6,1,7] :=
  branch_excluded a [5,8,6,1,7] (by decide)
    (fin9_cases _
      node_1193
      (invalid_excluded a [5,8,6,1,7,1] (by decide +kernel))
      node_1194
      node_1195
      node_1202
      (invalid_excluded a [5,8,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,8] (by decide +kernel)))

theorem node_1184 : Excluded a [5,8,6,1] :=
  branch_excluded a [5,8,6,1] (by decide)
    (fin9_cases _
      node_1185
      (invalid_excluded a [5,8,6,1,1] (by decide +kernel))
      node_1186
      node_1187
      (invalid_excluded a [5,8,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,6] (by decide +kernel))
      node_1192
      (invalid_excluded a [5,8,6,1,8] (by decide +kernel)))

theorem node_1204 : Excluded a [5,8,6,2,0] :=
  source_excluded a [5,8,6,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1205 : Excluded a [5,8,6,2,1] :=
  source_excluded a [5,8,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1207 : Excluded a [5,8,6,2,3,0] :=
  source_excluded a [5,8,6,2,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1208 : Excluded a [5,8,6,2,3,1] :=
  source_excluded a [5,8,6,2,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1209 : Excluded a [5,8,6,2,3,4] :=
  predecessor_excluded a [5,8,6,2,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1210 : Excluded a [5,8,6,2,3,7] :=
  source_excluded a [5,8,6,2,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1206 : Excluded a [5,8,6,2,3] :=
  branch_excluded a [5,8,6,2,3] (by decide)
    (fin9_cases _
      node_1207
      node_1208
      (invalid_excluded a [5,8,6,2,3,2] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,3,3] (by decide +kernel))
      node_1209
      (invalid_excluded a [5,8,6,2,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,3,6] (by decide +kernel))
      node_1210
      (invalid_excluded a [5,8,6,2,3,8] (by decide +kernel)))

theorem node_1212 : Excluded a [5,8,6,2,7,0] :=
  source_excluded a [5,8,6,2,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1213 : Excluded a [5,8,6,2,7,1] :=
  source_excluded a [5,8,6,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1215 : Excluded a [5,8,6,2,7,3,0] :=
  source_excluded a [5,8,6,2,7,3,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1216 : Excluded a [5,8,6,2,7,3,1] :=
  predecessor_excluded a [5,8,6,2,7,3,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1217 : Excluded a [5,8,6,2,7,3,4] :=
  source_excluded a [5,8,6,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1214 : Excluded a [5,8,6,2,7,3] :=
  branch_excluded a [5,8,6,2,7,3] (by decide)
    (fin9_cases _
      node_1215
      node_1216
      (invalid_excluded a [5,8,6,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,3,3] (by decide +kernel))
      node_1217
      (invalid_excluded a [5,8,6,2,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,3,8] (by decide +kernel)))

theorem node_1218 : Excluded a [5,8,6,2,7,4] :=
  predecessor_excluded a [5,8,6,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1211 : Excluded a [5,8,6,2,7] :=
  branch_excluded a [5,8,6,2,7] (by decide)
    (fin9_cases _
      node_1212
      node_1213
      (invalid_excluded a [5,8,6,2,7,2] (by decide +kernel))
      node_1214
      node_1218
      (invalid_excluded a [5,8,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,8] (by decide +kernel)))

theorem node_1203 : Excluded a [5,8,6,2] :=
  branch_excluded a [5,8,6,2] (by decide)
    (fin9_cases _
      node_1204
      node_1205
      (invalid_excluded a [5,8,6,2,2] (by decide +kernel))
      node_1206
      (invalid_excluded a [5,8,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,6] (by decide +kernel))
      node_1211
      (invalid_excluded a [5,8,6,2,8] (by decide +kernel)))

theorem node_1220 : Excluded a [5,8,6,7,0] :=
  source_excluded a [5,8,6,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1221 : Excluded a [5,8,6,7,1] :=
  source_excluded a [5,8,6,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1222 : Excluded a [5,8,6,7,2] :=
  predecessor_excluded a [5,8,6,7,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1224 : Excluded a [5,8,6,7,3,0] :=
  source_excluded a [5,8,6,7,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1225 : Excluded a [5,8,6,7,3,1] :=
  source_excluded a [5,8,6,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1226 : Excluded a [5,8,6,7,3,2] :=
  source_excluded a [5,8,6,7,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1227 : Excluded a [5,8,6,7,3,4] :=
  predecessor_excluded a [5,8,6,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1223 : Excluded a [5,8,6,7,3] :=
  branch_excluded a [5,8,6,7,3] (by decide)
    (fin9_cases _
      node_1224
      node_1225
      node_1226
      (invalid_excluded a [5,8,6,7,3,3] (by decide +kernel))
      node_1227
      (invalid_excluded a [5,8,6,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,7,3,8] (by decide +kernel)))

theorem node_1219 : Excluded a [5,8,6,7] :=
  branch_excluded a [5,8,6,7] (by decide)
    (fin9_cases _
      node_1220
      node_1221
      node_1222
      node_1223
      (invalid_excluded a [5,8,6,7,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,7,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,7,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,7,8] (by decide +kernel)))

theorem node_1182 : Excluded a [5,8,6] :=
  branch_excluded a [5,8,6] (by decide)
    (fin9_cases _
      node_1183
      node_1184
      node_1203
      (invalid_excluded a [5,8,6,3] (by decide +kernel))
      (invalid_excluded a [5,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,6] (by decide +kernel))
      node_1219
      (invalid_excluded a [5,8,6,8] (by decide +kernel)))

theorem node_1229 : Excluded a [5,8,7,0] :=
  predecessor_excluded a [5,8,7,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1231 : Excluded a [5,8,7,1,0] :=
  source_excluded a [5,8,7,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1232 : Excluded a [5,8,7,1,2] :=
  predecessor_excluded a [5,8,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1235 : Excluded a [5,8,7,1,3,0,2] :=
  source_excluded a [5,8,7,1,3,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1237 : Excluded a [5,8,7,1,3,0,4,2] :=
  source_excluded a [5,8,7,1,3,0,4,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_1239 : Excluded a [5,8,7,1,3,0,4,6,2] :=
  source_excluded a [5,8,7,1,3,0,4,6,2] 1 0 8 (by decide) (by decide +kernel)

theorem node_1238 : Excluded a [5,8,7,1,3,0,4,6] :=
  branch_excluded a [5,8,7,1,3,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,1,3,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,1] (by decide +kernel))
      node_1239
      (invalid_excluded a [5,8,7,1,3,0,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,8] (by decide +kernel)))

theorem node_1236 : Excluded a [5,8,7,1,3,0,4] :=
  branch_excluded a [5,8,7,1,3,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,1,3,0,4,0] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,1] (by decide +kernel))
      node_1237
      (invalid_excluded a [5,8,7,1,3,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,5] (by decide +kernel))
      node_1238
      (invalid_excluded a [5,8,7,1,3,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,8] (by decide +kernel)))

theorem node_1234 : Excluded a [5,8,7,1,3,0] :=
  branch_excluded a [5,8,7,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,1] (by decide +kernel))
      node_1235
      (invalid_excluded a [5,8,7,1,3,0,3] (by decide +kernel))
      node_1236
      (invalid_excluded a [5,8,7,1,3,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,8] (by decide +kernel)))

theorem node_1240 : Excluded a [5,8,7,1,3,2] :=
  predecessor_excluded a [5,8,7,1,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1241 : Excluded a [5,8,7,1,3,4] :=
  predecessor_excluded a [5,8,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1233 : Excluded a [5,8,7,1,3] :=
  branch_excluded a [5,8,7,1,3] (by decide)
    (fin9_cases _
      node_1234
      (invalid_excluded a [5,8,7,1,3,1] (by decide +kernel))
      node_1240
      (invalid_excluded a [5,8,7,1,3,3] (by decide +kernel))
      node_1241
      (invalid_excluded a [5,8,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,8] (by decide +kernel)))

theorem node_1242 : Excluded a [5,8,7,1,6] :=
  source_excluded a [5,8,7,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1230 : Excluded a [5,8,7,1] :=
  branch_excluded a [5,8,7,1] (by decide)
    (fin9_cases _
      node_1231
      (invalid_excluded a [5,8,7,1,1] (by decide +kernel))
      node_1232
      node_1233
      (invalid_excluded a [5,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,5] (by decide +kernel))
      node_1242
      (invalid_excluded a [5,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,8] (by decide +kernel)))

theorem node_1244 : Excluded a [5,8,7,2,0] :=
  source_excluded a [5,8,7,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1245 : Excluded a [5,8,7,2,1] :=
  source_excluded a [5,8,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1248 : Excluded a [5,8,7,2,3,0,1] :=
  predecessor_excluded a [5,8,7,2,3,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1250 : Excluded a [5,8,7,2,3,0,4,1] :=
  source_excluded a [5,8,7,2,3,0,4,1] 7 0 1 (by decide) (by decide +kernel)

theorem node_1252 : Excluded a [5,8,7,2,3,0,4,6,1] :=
  predecessor_excluded a [5,8,7,2,3,0,4,6,1] 0 2 8 3 (by decide) (by decide +kernel)

theorem node_1251 : Excluded a [5,8,7,2,3,0,4,6] :=
  branch_excluded a [5,8,7,2,3,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,2,3,0,4,6,0] (by decide +kernel))
      node_1252
      (invalid_excluded a [5,8,7,2,3,0,4,6,2] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,6,8] (by decide +kernel)))

theorem node_1249 : Excluded a [5,8,7,2,3,0,4] :=
  branch_excluded a [5,8,7,2,3,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,2,3,0,4,0] (by decide +kernel))
      node_1250
      (invalid_excluded a [5,8,7,2,3,0,4,2] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,5] (by decide +kernel))
      node_1251
      (invalid_excluded a [5,8,7,2,3,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,4,8] (by decide +kernel)))

theorem node_1247 : Excluded a [5,8,7,2,3,0] :=
  branch_excluded a [5,8,7,2,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,2,3,0,0] (by decide +kernel))
      node_1248
      (invalid_excluded a [5,8,7,2,3,0,2] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,3] (by decide +kernel))
      node_1249
      (invalid_excluded a [5,8,7,2,3,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,0,8] (by decide +kernel)))

theorem node_1253 : Excluded a [5,8,7,2,3,1] :=
  source_excluded a [5,8,7,2,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1254 : Excluded a [5,8,7,2,3,4] :=
  predecessor_excluded a [5,8,7,2,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1246 : Excluded a [5,8,7,2,3] :=
  branch_excluded a [5,8,7,2,3] (by decide)
    (fin9_cases _
      node_1247
      node_1253
      (invalid_excluded a [5,8,7,2,3,2] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,3] (by decide +kernel))
      node_1254
      (invalid_excluded a [5,8,7,2,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,3,8] (by decide +kernel)))

theorem node_1255 : Excluded a [5,8,7,2,6] :=
  source_excluded a [5,8,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1243 : Excluded a [5,8,7,2] :=
  branch_excluded a [5,8,7,2] (by decide)
    (fin9_cases _
      node_1244
      node_1245
      (invalid_excluded a [5,8,7,2,2] (by decide +kernel))
      node_1246
      (invalid_excluded a [5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,5] (by decide +kernel))
      node_1255
      (invalid_excluded a [5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,8] (by decide +kernel)))

theorem node_1257 : Excluded a [5,8,7,6,0] :=
  source_excluded a [5,8,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1258 : Excluded a [5,8,7,6,1] :=
  source_excluded a [5,8,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1260 : Excluded a [5,8,7,6,2,0] :=
  predecessor_excluded a [5,8,7,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1261 : Excluded a [5,8,7,6,2,1] :=
  source_excluded a [5,8,7,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1262 : Excluded a [5,8,7,6,2,3] :=
  source_excluded a [5,8,7,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1263 : Excluded a [5,8,7,6,2,4] :=
  source_excluded a [5,8,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1259 : Excluded a [5,8,7,6,2] :=
  branch_excluded a [5,8,7,6,2] (by decide)
    (fin9_cases _
      node_1260
      node_1261
      (invalid_excluded a [5,8,7,6,2,2] (by decide +kernel))
      node_1262
      node_1263
      (invalid_excluded a [5,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,8] (by decide +kernel)))

theorem node_1264 : Excluded a [5,8,7,6,3] :=
  predecessor_excluded a [5,8,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1256 : Excluded a [5,8,7,6] :=
  branch_excluded a [5,8,7,6] (by decide)
    (fin9_cases _
      node_1257
      node_1258
      node_1259
      node_1264
      (invalid_excluded a [5,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,8] (by decide +kernel)))

theorem node_1228 : Excluded a [5,8,7] :=
  branch_excluded a [5,8,7] (by decide)
    (fin9_cases _
      node_1229
      node_1230
      node_1243
      (invalid_excluded a [5,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,5] (by decide +kernel))
      node_1256
      (invalid_excluded a [5,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,8] (by decide +kernel)))

theorem node_1178 : Excluded a [5,8] :=
  branch_excluded a [5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0] (by decide +kernel))
      node_1179
      (invalid_excluded a [5,8,2] (by decide +kernel))
      node_1180
      node_1181
      (invalid_excluded a [5,8,5] (by decide +kernel))
      node_1182
      node_1228
      (invalid_excluded a [5,8,8] (by decide +kernel)))

theorem node_816 : Excluded a [5] :=
  branch_excluded a [5] (by decide)
    (fin9_cases _
      node_817
      (invalid_excluded a [5,1] (by decide +kernel))
      (invalid_excluded a [5,2] (by decide +kernel))
      node_818
      node_942
      (invalid_excluded a [5,5] (by decide +kernel))
      node_1065
      node_1066
      node_1178)

theorem node_1266 : Excluded a [6,0] :=
  source_excluded a [6,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_1268 : Excluded a [6,3,1] :=
  source_excluded a [6,3,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1269 : Excluded a [6,3,4] :=
  predecessor_excluded a [6,3,4] 0 4 1 2 (by decide) (by decide +kernel)

theorem node_1270 : Excluded a [6,3,5] :=
  predecessor_excluded a [6,3,5] 1 6 2 0 (by decide) (by decide +kernel)

theorem node_1272 : Excluded a [6,3,7,0] :=
  predecessor_excluded a [6,3,7,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1274 : Excluded a [6,3,7,1,0] :=
  predecessor_excluded a [6,3,7,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1275 : Excluded a [6,3,7,1,2] :=
  predecessor_excluded a [6,3,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1277 : Excluded a [6,3,7,1,8,0] :=
  source_excluded a [6,3,7,1,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1278 : Excluded a [6,3,7,1,8,2] :=
  predecessor_excluded a [6,3,7,1,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1280 : Excluded a [6,3,7,1,8,4,0] :=
  source_excluded a [6,3,7,1,8,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1281 : Excluded a [6,3,7,1,8,4,2] :=
  source_excluded a [6,3,7,1,8,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1282 : Excluded a [6,3,7,1,8,4,5] :=
  predecessor_excluded a [6,3,7,1,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1279 : Excluded a [6,3,7,1,8,4] :=
  branch_excluded a [6,3,7,1,8,4] (by decide)
    (fin9_cases _
      node_1280
      (invalid_excluded a [6,3,7,1,8,4,1] (by decide +kernel))
      node_1281
      (invalid_excluded a [6,3,7,1,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,8,4,4] (by decide +kernel))
      node_1282
      (invalid_excluded a [6,3,7,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,8,4,8] (by decide +kernel)))

theorem node_1276 : Excluded a [6,3,7,1,8] :=
  branch_excluded a [6,3,7,1,8] (by decide)
    (fin9_cases _
      node_1277
      (invalid_excluded a [6,3,7,1,8,1] (by decide +kernel))
      node_1278
      (invalid_excluded a [6,3,7,1,8,3] (by decide +kernel))
      node_1279
      (invalid_excluded a [6,3,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,8,8] (by decide +kernel)))

theorem node_1273 : Excluded a [6,3,7,1] :=
  branch_excluded a [6,3,7,1] (by decide)
    (fin9_cases _
      node_1274
      (invalid_excluded a [6,3,7,1,1] (by decide +kernel))
      node_1275
      (invalid_excluded a [6,3,7,1,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,1,7] (by decide +kernel))
      node_1276)

theorem node_1283 : Excluded a [6,3,7,2] :=
  source_excluded a [6,3,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1284 : Excluded a [6,3,7,5] :=
  source_excluded a [6,3,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1286 : Excluded a [6,3,7,8,0] :=
  predecessor_excluded a [6,3,7,8,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1288 : Excluded a [6,3,7,8,1,0] :=
  source_excluded a [6,3,7,8,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1289 : Excluded a [6,3,7,8,1,2] :=
  predecessor_excluded a [6,3,7,8,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1291 : Excluded a [6,3,7,8,1,4,0] :=
  source_excluded a [6,3,7,8,1,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1292 : Excluded a [6,3,7,8,1,4,2] :=
  source_excluded a [6,3,7,8,1,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1293 : Excluded a [6,3,7,8,1,4,5] :=
  predecessor_excluded a [6,3,7,8,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1290 : Excluded a [6,3,7,8,1,4] :=
  branch_excluded a [6,3,7,8,1,4] (by decide)
    (fin9_cases _
      node_1291
      (invalid_excluded a [6,3,7,8,1,4,1] (by decide +kernel))
      node_1292
      (invalid_excluded a [6,3,7,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,1,4,4] (by decide +kernel))
      node_1293
      (invalid_excluded a [6,3,7,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,1,4,8] (by decide +kernel)))

theorem node_1287 : Excluded a [6,3,7,8,1] :=
  branch_excluded a [6,3,7,8,1] (by decide)
    (fin9_cases _
      node_1288
      (invalid_excluded a [6,3,7,8,1,1] (by decide +kernel))
      node_1289
      (invalid_excluded a [6,3,7,8,1,3] (by decide +kernel))
      node_1290
      (invalid_excluded a [6,3,7,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,1,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,1,8] (by decide +kernel)))

theorem node_1295 : Excluded a [6,3,7,8,2,0] :=
  source_excluded a [6,3,7,8,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1296 : Excluded a [6,3,7,8,2,1] :=
  source_excluded a [6,3,7,8,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1298 : Excluded a [6,3,7,8,2,4,0] :=
  source_excluded a [6,3,7,8,2,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1299 : Excluded a [6,3,7,8,2,4,1] :=
  source_excluded a [6,3,7,8,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1300 : Excluded a [6,3,7,8,2,4,5] :=
  predecessor_excluded a [6,3,7,8,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1297 : Excluded a [6,3,7,8,2,4] :=
  branch_excluded a [6,3,7,8,2,4] (by decide)
    (fin9_cases _
      node_1298
      node_1299
      (invalid_excluded a [6,3,7,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,4,4] (by decide +kernel))
      node_1300
      (invalid_excluded a [6,3,7,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,4,8] (by decide +kernel)))

theorem node_1294 : Excluded a [6,3,7,8,2] :=
  branch_excluded a [6,3,7,8,2] (by decide)
    (fin9_cases _
      node_1295
      node_1296
      (invalid_excluded a [6,3,7,8,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,3] (by decide +kernel))
      node_1297
      (invalid_excluded a [6,3,7,8,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,2,8] (by decide +kernel)))

theorem node_1285 : Excluded a [6,3,7,8] :=
  branch_excluded a [6,3,7,8] (by decide)
    (fin9_cases _
      node_1286
      node_1287
      node_1294
      (invalid_excluded a [6,3,7,8,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,4] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,8,8] (by decide +kernel)))

theorem node_1271 : Excluded a [6,3,7] :=
  branch_excluded a [6,3,7] (by decide)
    (fin9_cases _
      node_1272
      node_1273
      node_1283
      (invalid_excluded a [6,3,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,4] (by decide +kernel))
      node_1284
      (invalid_excluded a [6,3,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,7] (by decide +kernel))
      node_1285)

theorem node_1302 : Excluded a [6,3,8,0] :=
  predecessor_excluded a [6,3,8,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1304 : Excluded a [6,3,8,1,0] :=
  predecessor_excluded a [6,3,8,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1305 : Excluded a [6,3,8,1,2] :=
  predecessor_excluded a [6,3,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1307 : Excluded a [6,3,8,1,7,0] :=
  source_excluded a [6,3,8,1,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1309 : Excluded a [6,3,8,1,7,2,0] :=
  predecessor_excluded a [6,3,8,1,7,2,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_1310 : Excluded a [6,3,8,1,7,2,4] :=
  source_excluded a [6,3,8,1,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1311 : Excluded a [6,3,8,1,7,2,5] :=
  source_excluded a [6,3,8,1,7,2,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1308 : Excluded a [6,3,8,1,7,2] :=
  branch_excluded a [6,3,8,1,7,2] (by decide)
    (fin9_cases _
      node_1309
      (invalid_excluded a [6,3,8,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,7,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,7,2,3] (by decide +kernel))
      node_1310
      node_1311
      (invalid_excluded a [6,3,8,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,7,2,8] (by decide +kernel)))

theorem node_1312 : Excluded a [6,3,8,1,7,4] :=
  predecessor_excluded a [6,3,8,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1306 : Excluded a [6,3,8,1,7] :=
  branch_excluded a [6,3,8,1,7] (by decide)
    (fin9_cases _
      node_1307
      (invalid_excluded a [6,3,8,1,7,1] (by decide +kernel))
      node_1308
      (invalid_excluded a [6,3,8,1,7,3] (by decide +kernel))
      node_1312
      (invalid_excluded a [6,3,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,7,8] (by decide +kernel)))

theorem node_1303 : Excluded a [6,3,8,1] :=
  branch_excluded a [6,3,8,1] (by decide)
    (fin9_cases _
      node_1304
      (invalid_excluded a [6,3,8,1,1] (by decide +kernel))
      node_1305
      (invalid_excluded a [6,3,8,1,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,4] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,1,6] (by decide +kernel))
      node_1306
      (invalid_excluded a [6,3,8,1,8] (by decide +kernel)))

theorem node_1313 : Excluded a [6,3,8,2] :=
  source_excluded a [6,3,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1314 : Excluded a [6,3,8,5] :=
  source_excluded a [6,3,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1316 : Excluded a [6,3,8,7,0] :=
  predecessor_excluded a [6,3,8,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1318 : Excluded a [6,3,8,7,1,0] :=
  source_excluded a [6,3,8,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1319 : Excluded a [6,3,8,7,1,2] :=
  predecessor_excluded a [6,3,8,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1322 : Excluded a [6,3,8,7,1,4,0,2] :=
  source_excluded a [6,3,8,7,1,4,0,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_1323 : Excluded a [6,3,8,7,1,4,0,5] :=
  predecessor_excluded a [6,3,8,7,1,4,0,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_1321 : Excluded a [6,3,8,7,1,4,0] :=
  branch_excluded a [6,3,8,7,1,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,1,4,0,0] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,0,1] (by decide +kernel))
      node_1322
      (invalid_excluded a [6,3,8,7,1,4,0,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,0,4] (by decide +kernel))
      node_1323
      (invalid_excluded a [6,3,8,7,1,4,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,0,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,0,8] (by decide +kernel)))

theorem node_1324 : Excluded a [6,3,8,7,1,4,2] :=
  predecessor_excluded a [6,3,8,7,1,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1325 : Excluded a [6,3,8,7,1,4,5] :=
  predecessor_excluded a [6,3,8,7,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1320 : Excluded a [6,3,8,7,1,4] :=
  branch_excluded a [6,3,8,7,1,4] (by decide)
    (fin9_cases _
      node_1321
      (invalid_excluded a [6,3,8,7,1,4,1] (by decide +kernel))
      node_1324
      (invalid_excluded a [6,3,8,7,1,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,4] (by decide +kernel))
      node_1325
      (invalid_excluded a [6,3,8,7,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,8] (by decide +kernel)))

theorem node_1317 : Excluded a [6,3,8,7,1] :=
  branch_excluded a [6,3,8,7,1] (by decide)
    (fin9_cases _
      node_1318
      (invalid_excluded a [6,3,8,7,1,1] (by decide +kernel))
      node_1319
      (invalid_excluded a [6,3,8,7,1,3] (by decide +kernel))
      node_1320
      (invalid_excluded a [6,3,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,8] (by decide +kernel)))

theorem node_1327 : Excluded a [6,3,8,7,2,0] :=
  source_excluded a [6,3,8,7,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1328 : Excluded a [6,3,8,7,2,1] :=
  source_excluded a [6,3,8,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1331 : Excluded a [6,3,8,7,2,4,0,1] :=
  predecessor_excluded a [6,3,8,7,2,4,0,1] 0 3 7 1 (by decide) (by decide +kernel)

theorem node_1332 : Excluded a [6,3,8,7,2,4,0,5] :=
  predecessor_excluded a [6,3,8,7,2,4,0,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_1330 : Excluded a [6,3,8,7,2,4,0] :=
  branch_excluded a [6,3,8,7,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,2,4,0,0] (by decide +kernel))
      node_1331
      (invalid_excluded a [6,3,8,7,2,4,0,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,0,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,0,4] (by decide +kernel))
      node_1332
      (invalid_excluded a [6,3,8,7,2,4,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,0,8] (by decide +kernel)))

theorem node_1333 : Excluded a [6,3,8,7,2,4,1] :=
  source_excluded a [6,3,8,7,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1334 : Excluded a [6,3,8,7,2,4,5] :=
  predecessor_excluded a [6,3,8,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1329 : Excluded a [6,3,8,7,2,4] :=
  branch_excluded a [6,3,8,7,2,4] (by decide)
    (fin9_cases _
      node_1330
      node_1333
      (invalid_excluded a [6,3,8,7,2,4,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,4] (by decide +kernel))
      node_1334
      (invalid_excluded a [6,3,8,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,8] (by decide +kernel)))

theorem node_1326 : Excluded a [6,3,8,7,2] :=
  branch_excluded a [6,3,8,7,2] (by decide)
    (fin9_cases _
      node_1327
      node_1328
      (invalid_excluded a [6,3,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,3] (by decide +kernel))
      node_1329
      (invalid_excluded a [6,3,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,8] (by decide +kernel)))

theorem node_1315 : Excluded a [6,3,8,7] :=
  branch_excluded a [6,3,8,7] (by decide)
    (fin9_cases _
      node_1316
      node_1317
      node_1326
      (invalid_excluded a [6,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,8] (by decide +kernel)))

theorem node_1301 : Excluded a [6,3,8] :=
  branch_excluded a [6,3,8] (by decide)
    (fin9_cases _
      node_1302
      node_1303
      node_1313
      (invalid_excluded a [6,3,8,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,4] (by decide +kernel))
      node_1314
      (invalid_excluded a [6,3,8,6] (by decide +kernel))
      node_1315
      (invalid_excluded a [6,3,8,8] (by decide +kernel)))

theorem node_1267 : Excluded a [6,3] :=
  branch_excluded a [6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,0] (by decide +kernel))
      node_1268
      (invalid_excluded a [6,3,2] (by decide +kernel))
      (invalid_excluded a [6,3,3] (by decide +kernel))
      node_1269
      node_1270
      (invalid_excluded a [6,3,6] (by decide +kernel))
      node_1271
      node_1301)

theorem node_1336 : Excluded a [6,4,1] :=
  source_excluded a [6,4,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1338 : Excluded a [6,4,3,0] :=
  source_excluded a [6,4,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1339 : Excluded a [6,4,3,1] :=
  source_excluded a [6,4,3,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1340 : Excluded a [6,4,3,2] :=
  source_excluded a [6,4,3,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1341 : Excluded a [6,4,3,5] :=
  source_excluded a [6,4,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1343 : Excluded a [6,4,3,7,0] :=
  predecessor_excluded a [6,4,3,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1345 : Excluded a [6,4,3,7,1,0] :=
  source_excluded a [6,4,3,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1346 : Excluded a [6,4,3,7,1,2] :=
  predecessor_excluded a [6,4,3,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1349 : Excluded a [6,4,3,7,1,8,0,2] :=
  predecessor_excluded a [6,4,3,7,1,8,0,2] 0 3 7 2 (by decide) (by decide +kernel)

theorem node_1350 : Excluded a [6,4,3,7,1,8,0,5] :=
  source_excluded a [6,4,3,7,1,8,0,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_1348 : Excluded a [6,4,3,7,1,8,0] :=
  branch_excluded a [6,4,3,7,1,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,3,7,1,8,0,0] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,1] (by decide +kernel))
      node_1349
      (invalid_excluded a [6,4,3,7,1,8,0,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,4] (by decide +kernel))
      node_1350
      (invalid_excluded a [6,4,3,7,1,8,0,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,7] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,0,8] (by decide +kernel)))

theorem node_1351 : Excluded a [6,4,3,7,1,8,2] :=
  predecessor_excluded a [6,4,3,7,1,8,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1352 : Excluded a [6,4,3,7,1,8,5] :=
  predecessor_excluded a [6,4,3,7,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1347 : Excluded a [6,4,3,7,1,8] :=
  branch_excluded a [6,4,3,7,1,8] (by decide)
    (fin9_cases _
      node_1348
      (invalid_excluded a [6,4,3,7,1,8,1] (by decide +kernel))
      node_1351
      (invalid_excluded a [6,4,3,7,1,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,4] (by decide +kernel))
      node_1352
      (invalid_excluded a [6,4,3,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,8,8] (by decide +kernel)))

theorem node_1344 : Excluded a [6,4,3,7,1] :=
  branch_excluded a [6,4,3,7,1] (by decide)
    (fin9_cases _
      node_1345
      (invalid_excluded a [6,4,3,7,1,1] (by decide +kernel))
      node_1346
      (invalid_excluded a [6,4,3,7,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,1,7] (by decide +kernel))
      node_1347)

theorem node_1353 : Excluded a [6,4,3,7,2] :=
  source_excluded a [6,4,3,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1354 : Excluded a [6,4,3,7,8] :=
  predecessor_excluded a [6,4,3,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1342 : Excluded a [6,4,3,7] :=
  branch_excluded a [6,4,3,7] (by decide)
    (fin9_cases _
      node_1343
      node_1344
      node_1353
      (invalid_excluded a [6,4,3,7,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,7,7] (by decide +kernel))
      node_1354)

theorem node_1356 : Excluded a [6,4,3,8,0] :=
  predecessor_excluded a [6,4,3,8,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1358 : Excluded a [6,4,3,8,1,0] :=
  source_excluded a [6,4,3,8,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1359 : Excluded a [6,4,3,8,1,2] :=
  predecessor_excluded a [6,4,3,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1360 : Excluded a [6,4,3,8,1,7] :=
  source_excluded a [6,4,3,8,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1357 : Excluded a [6,4,3,8,1] :=
  branch_excluded a [6,4,3,8,1] (by decide)
    (fin9_cases _
      node_1358
      (invalid_excluded a [6,4,3,8,1,1] (by decide +kernel))
      node_1359
      (invalid_excluded a [6,4,3,8,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,1,6] (by decide +kernel))
      node_1360
      (invalid_excluded a [6,4,3,8,1,8] (by decide +kernel)))

theorem node_1361 : Excluded a [6,4,3,8,2] :=
  source_excluded a [6,4,3,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1363 : Excluded a [6,4,3,8,7,0] :=
  source_excluded a [6,4,3,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1364 : Excluded a [6,4,3,8,7,1] :=
  source_excluded a [6,4,3,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1366 : Excluded a [6,4,3,8,7,2,0] :=
  predecessor_excluded a [6,4,3,8,7,2,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_1367 : Excluded a [6,4,3,8,7,2,1] :=
  source_excluded a [6,4,3,8,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1368 : Excluded a [6,4,3,8,7,2,5] :=
  source_excluded a [6,4,3,8,7,2,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1365 : Excluded a [6,4,3,8,7,2] :=
  branch_excluded a [6,4,3,8,7,2] (by decide)
    (fin9_cases _
      node_1366
      node_1367
      (invalid_excluded a [6,4,3,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,2,4] (by decide +kernel))
      node_1368
      (invalid_excluded a [6,4,3,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,2,8] (by decide +kernel)))

theorem node_1362 : Excluded a [6,4,3,8,7] :=
  branch_excluded a [6,4,3,8,7] (by decide)
    (fin9_cases _
      node_1363
      node_1364
      node_1365
      (invalid_excluded a [6,4,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,7,8] (by decide +kernel)))

theorem node_1355 : Excluded a [6,4,3,8] :=
  branch_excluded a [6,4,3,8] (by decide)
    (fin9_cases _
      node_1356
      node_1357
      node_1361
      (invalid_excluded a [6,4,3,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,3,8,6] (by decide +kernel))
      node_1362
      (invalid_excluded a [6,4,3,8,8] (by decide +kernel)))

theorem node_1337 : Excluded a [6,4,3] :=
  branch_excluded a [6,4,3] (by decide)
    (fin9_cases _
      node_1338
      node_1339
      node_1340
      (invalid_excluded a [6,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,3,4] (by decide +kernel))
      node_1341
      (invalid_excluded a [6,4,3,6] (by decide +kernel))
      node_1342
      node_1355)

theorem node_1369 : Excluded a [6,4,5] :=
  predecessor_excluded a [6,4,5] 1 6 2 0 (by decide) (by decide +kernel)

theorem node_1372 : Excluded a [6,4,7,0,1] :=
  predecessor_excluded a [6,4,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1373 : Excluded a [6,4,7,0,2] :=
  source_excluded a [6,4,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1375 : Excluded a [6,4,7,0,3,1] :=
  source_excluded a [6,4,7,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1376 : Excluded a [6,4,7,0,3,2] :=
  predecessor_excluded a [6,4,7,0,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1378 : Excluded a [6,4,7,0,3,8,1] :=
  source_excluded a [6,4,7,0,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1379 : Excluded a [6,4,7,0,3,8,2] :=
  source_excluded a [6,4,7,0,3,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1380 : Excluded a [6,4,7,0,3,8,5] :=
  predecessor_excluded a [6,4,7,0,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1377 : Excluded a [6,4,7,0,3,8] :=
  branch_excluded a [6,4,7,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,3,8,0] (by decide +kernel))
      node_1378
      node_1379
      (invalid_excluded a [6,4,7,0,3,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,3,8,4] (by decide +kernel))
      node_1380
      (invalid_excluded a [6,4,7,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,3,8,8] (by decide +kernel)))

theorem node_1374 : Excluded a [6,4,7,0,3] :=
  branch_excluded a [6,4,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,3,0] (by decide +kernel))
      node_1375
      node_1376
      (invalid_excluded a [6,4,7,0,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,3,7] (by decide +kernel))
      node_1377)

theorem node_1382 : Excluded a [6,4,7,0,8,1] :=
  source_excluded a [6,4,7,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1383 : Excluded a [6,4,7,0,8,2] :=
  predecessor_excluded a [6,4,7,0,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1384 : Excluded a [6,4,7,0,8,3] :=
  predecessor_excluded a [6,4,7,0,8,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1381 : Excluded a [6,4,7,0,8] :=
  branch_excluded a [6,4,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,8,0] (by decide +kernel))
      node_1382
      node_1383
      node_1384
      (invalid_excluded a [6,4,7,0,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,8] (by decide +kernel)))

theorem node_1371 : Excluded a [6,4,7,0] :=
  branch_excluded a [6,4,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,0] (by decide +kernel))
      node_1372
      node_1373
      node_1374
      (invalid_excluded a [6,4,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,7] (by decide +kernel))
      node_1381)

theorem node_1385 : Excluded a [6,4,7,1] :=
  source_excluded a [6,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1386 : Excluded a [6,4,7,2] :=
  source_excluded a [6,4,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1387 : Excluded a [6,4,7,5] :=
  source_excluded a [6,4,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1389 : Excluded a [6,4,7,8,0] :=
  predecessor_excluded a [6,4,7,8,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1391 : Excluded a [6,4,7,8,1,0] :=
  source_excluded a [6,4,7,8,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1392 : Excluded a [6,4,7,8,1,2] :=
  predecessor_excluded a [6,4,7,8,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1394 : Excluded a [6,4,7,8,1,3,0] :=
  source_excluded a [6,4,7,8,1,3,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1395 : Excluded a [6,4,7,8,1,3,2] :=
  source_excluded a [6,4,7,8,1,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1397 : Excluded a [6,4,7,8,1,3,5,0] :=
  source_excluded a [6,4,7,8,1,3,5,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_1399 : Excluded a [6,4,7,8,1,3,5,2,0] :=
  predecessor_excluded a [6,4,7,8,1,3,5,2,0] 1 0 7 8 (by decide) (by decide +kernel)

theorem node_1398 : Excluded a [6,4,7,8,1,3,5,2] :=
  branch_excluded a [6,4,7,8,1,3,5,2] (by decide)
    (fin9_cases _
      node_1399
      (invalid_excluded a [6,4,7,8,1,3,5,2,1] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,2,8] (by decide +kernel)))

theorem node_1396 : Excluded a [6,4,7,8,1,3,5] :=
  branch_excluded a [6,4,7,8,1,3,5] (by decide)
    (fin9_cases _
      node_1397
      (invalid_excluded a [6,4,7,8,1,3,5,1] (by decide +kernel))
      node_1398
      (invalid_excluded a [6,4,7,8,1,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,5,8] (by decide +kernel)))

theorem node_1393 : Excluded a [6,4,7,8,1,3] :=
  branch_excluded a [6,4,7,8,1,3] (by decide)
    (fin9_cases _
      node_1394
      (invalid_excluded a [6,4,7,8,1,3,1] (by decide +kernel))
      node_1395
      (invalid_excluded a [6,4,7,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,4] (by decide +kernel))
      node_1396
      (invalid_excluded a [6,4,7,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,3,8] (by decide +kernel)))

theorem node_1390 : Excluded a [6,4,7,8,1] :=
  branch_excluded a [6,4,7,8,1] (by decide)
    (fin9_cases _
      node_1391
      (invalid_excluded a [6,4,7,8,1,1] (by decide +kernel))
      node_1392
      node_1393
      (invalid_excluded a [6,4,7,8,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,1,8] (by decide +kernel)))

theorem node_1400 : Excluded a [6,4,7,8,2] :=
  source_excluded a [6,4,7,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1401 : Excluded a [6,4,7,8,3] :=
  predecessor_excluded a [6,4,7,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1388 : Excluded a [6,4,7,8] :=
  branch_excluded a [6,4,7,8] (by decide)
    (fin9_cases _
      node_1389
      node_1390
      node_1400
      node_1401
      (invalid_excluded a [6,4,7,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,8,8] (by decide +kernel)))

theorem node_1370 : Excluded a [6,4,7] :=
  branch_excluded a [6,4,7] (by decide)
    (fin9_cases _
      node_1371
      node_1385
      node_1386
      (invalid_excluded a [6,4,7,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,4] (by decide +kernel))
      node_1387
      (invalid_excluded a [6,4,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,7] (by decide +kernel))
      node_1388)

theorem node_1404 : Excluded a [6,4,8,0,1] :=
  predecessor_excluded a [6,4,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1405 : Excluded a [6,4,8,0,2] :=
  source_excluded a [6,4,8,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1407 : Excluded a [6,4,8,0,3,1] :=
  source_excluded a [6,4,8,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1409 : Excluded a [6,4,8,0,3,2,1] :=
  source_excluded a [6,4,8,0,3,2,1] 0 2 6 (by decide) (by decide +kernel)

def b_1412 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 8
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 5
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_1412 : LosingRegion (edgeOf a b_1412) 3 :=
  losingMask a b_1412 3 1210114498716214538273921
    (by decide +kernel) (by decide +kernel)

theorem node_1412 : Excluded a [6,4,8,0,3,2,5,1,7] :=
  losing_excluded a [6,4,8,0,3,2,5,1,7] (by decide) b_1412 (by decide +kernel) 0 3 7 cert_1412 (by change 0 ≠ 3 ∧ ¬ edgeOf a b_1412 0 3 ∧ 7 ≠ 0 ∧ maskRegion 1210114498716214538273921 0 7; decide +kernel)

theorem node_1411 : Excluded a [6,4,8,0,3,2,5,1] :=
  branch_excluded a [6,4,8,0,3,2,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,3,2,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,1,6] (by decide +kernel))
      node_1412
      (invalid_excluded a [6,4,8,0,3,2,5,1,8] (by decide +kernel)))

theorem node_1410 : Excluded a [6,4,8,0,3,2,5] :=
  branch_excluded a [6,4,8,0,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,3,2,5,0] (by decide +kernel))
      node_1411
      (invalid_excluded a [6,4,8,0,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,5,8] (by decide +kernel)))

theorem node_1408 : Excluded a [6,4,8,0,3,2] :=
  branch_excluded a [6,4,8,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,3,2,0] (by decide +kernel))
      node_1409
      (invalid_excluded a [6,4,8,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,4] (by decide +kernel))
      node_1410
      (invalid_excluded a [6,4,8,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,2,8] (by decide +kernel)))

theorem node_1413 : Excluded a [6,4,8,0,3,7] :=
  source_excluded a [6,4,8,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1406 : Excluded a [6,4,8,0,3] :=
  branch_excluded a [6,4,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,3,0] (by decide +kernel))
      node_1407
      node_1408
      (invalid_excluded a [6,4,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,3,6] (by decide +kernel))
      node_1413
      (invalid_excluded a [6,4,8,0,3,8] (by decide +kernel)))

theorem node_1415 : Excluded a [6,4,8,0,7,1] :=
  source_excluded a [6,4,8,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1417 : Excluded a [6,4,8,0,7,2,1] :=
  source_excluded a [6,4,8,0,7,2,1] 0 2 6 (by decide) (by decide +kernel)

def b_1420 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 8
  | 3 => 0
  | 4 => 7
  | 5 => 2
  | 6 => 3
  | 7 => 1
  | 8 => 5
  | _ => 0

def cert_1420 : LosingRegion (edgeOf a b_1420) 0 :=
  losingMask a b_1420 0 1212510253860393369750528
    (by decide +kernel) (by decide +kernel)

theorem node_1420 : Excluded a [6,4,8,0,7,2,3,1,5] :=
  losing_excluded a [6,4,8,0,7,2,3,1,5] (by decide) b_1420 (by decide +kernel) 1 0 2 cert_1420 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1420 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212510253860393369750528 1 2; decide +kernel)

theorem node_1419 : Excluded a [6,4,8,0,7,2,3,1] :=
  branch_excluded a [6,4,8,0,7,2,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,7,2,3,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,1,4] (by decide +kernel))
      node_1420
      (invalid_excluded a [6,4,8,0,7,2,3,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,1,8] (by decide +kernel)))

theorem node_1421 : Excluded a [6,4,8,0,7,2,3,5] :=
  source_excluded a [6,4,8,0,7,2,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1418 : Excluded a [6,4,8,0,7,2,3] :=
  branch_excluded a [6,4,8,0,7,2,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,7,2,3,0] (by decide +kernel))
      node_1419
      (invalid_excluded a [6,4,8,0,7,2,3,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,4] (by decide +kernel))
      node_1421
      (invalid_excluded a [6,4,8,0,7,2,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,3,8] (by decide +kernel)))

theorem node_1422 : Excluded a [6,4,8,0,7,2,5] :=
  source_excluded a [6,4,8,0,7,2,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1416 : Excluded a [6,4,8,0,7,2] :=
  branch_excluded a [6,4,8,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,7,2,0] (by decide +kernel))
      node_1417
      (invalid_excluded a [6,4,8,0,7,2,2] (by decide +kernel))
      node_1418
      (invalid_excluded a [6,4,8,0,7,2,4] (by decide +kernel))
      node_1422
      (invalid_excluded a [6,4,8,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,2,8] (by decide +kernel)))

theorem node_1424 : Excluded a [6,4,8,0,7,3,1] :=
  source_excluded a [6,4,8,0,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1425 : Excluded a [6,4,8,0,7,3,2] :=
  predecessor_excluded a [6,4,8,0,7,3,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1426 : Excluded a [6,4,8,0,7,3,5] :=
  source_excluded a [6,4,8,0,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1423 : Excluded a [6,4,8,0,7,3] :=
  branch_excluded a [6,4,8,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,7,3,0] (by decide +kernel))
      node_1424
      node_1425
      (invalid_excluded a [6,4,8,0,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,3,4] (by decide +kernel))
      node_1426
      (invalid_excluded a [6,4,8,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,3,8] (by decide +kernel)))

theorem node_1414 : Excluded a [6,4,8,0,7] :=
  branch_excluded a [6,4,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,7,0] (by decide +kernel))
      node_1415
      node_1416
      node_1423
      (invalid_excluded a [6,4,8,0,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,7,8] (by decide +kernel)))

theorem node_1403 : Excluded a [6,4,8,0] :=
  branch_excluded a [6,4,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,0,0] (by decide +kernel))
      node_1404
      node_1405
      node_1406
      (invalid_excluded a [6,4,8,0,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,0,6] (by decide +kernel))
      node_1414
      (invalid_excluded a [6,4,8,0,8] (by decide +kernel)))

theorem node_1427 : Excluded a [6,4,8,1] :=
  source_excluded a [6,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1428 : Excluded a [6,4,8,2] :=
  source_excluded a [6,4,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1429 : Excluded a [6,4,8,5] :=
  source_excluded a [6,4,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1431 : Excluded a [6,4,8,7,0] :=
  predecessor_excluded a [6,4,8,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1433 : Excluded a [6,4,8,7,1,0] :=
  source_excluded a [6,4,8,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1434 : Excluded a [6,4,8,7,1,2] :=
  predecessor_excluded a [6,4,8,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1435 : Excluded a [6,4,8,7,1,3] :=
  predecessor_excluded a [6,4,8,7,1,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1432 : Excluded a [6,4,8,7,1] :=
  branch_excluded a [6,4,8,7,1] (by decide)
    (fin9_cases _
      node_1433
      (invalid_excluded a [6,4,8,7,1,1] (by decide +kernel))
      node_1434
      node_1435
      (invalid_excluded a [6,4,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,1,8] (by decide +kernel)))

theorem node_1436 : Excluded a [6,4,8,7,2] :=
  source_excluded a [6,4,8,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1438 : Excluded a [6,4,8,7,3,0] :=
  source_excluded a [6,4,8,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1439 : Excluded a [6,4,8,7,3,1] :=
  source_excluded a [6,4,8,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1441 : Excluded a [6,4,8,7,3,2,0] :=
  predecessor_excluded a [6,4,8,7,3,2,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_1442 : Excluded a [6,4,8,7,3,2,1] :=
  source_excluded a [6,4,8,7,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1444 : Excluded a [6,4,8,7,3,2,5,0] :=
  source_excluded a [6,4,8,7,3,2,5,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_1446 : Excluded a [6,4,8,7,3,2,5,1,0] :=
  source_excluded a [6,4,8,7,3,2,5,1,0] 2 1 8 (by decide) (by decide +kernel)

theorem node_1445 : Excluded a [6,4,8,7,3,2,5,1] :=
  branch_excluded a [6,4,8,7,3,2,5,1] (by decide)
    (fin9_cases _
      node_1446
      (invalid_excluded a [6,4,8,7,3,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,8] (by decide +kernel)))

theorem node_1443 : Excluded a [6,4,8,7,3,2,5] :=
  branch_excluded a [6,4,8,7,3,2,5] (by decide)
    (fin9_cases _
      node_1444
      node_1445
      (invalid_excluded a [6,4,8,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,8] (by decide +kernel)))

theorem node_1440 : Excluded a [6,4,8,7,3,2] :=
  branch_excluded a [6,4,8,7,3,2] (by decide)
    (fin9_cases _
      node_1441
      node_1442
      (invalid_excluded a [6,4,8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,4] (by decide +kernel))
      node_1443
      (invalid_excluded a [6,4,8,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,8] (by decide +kernel)))

theorem node_1437 : Excluded a [6,4,8,7,3] :=
  branch_excluded a [6,4,8,7,3] (by decide)
    (fin9_cases _
      node_1438
      node_1439
      node_1440
      (invalid_excluded a [6,4,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,8] (by decide +kernel)))

theorem node_1430 : Excluded a [6,4,8,7] :=
  branch_excluded a [6,4,8,7] (by decide)
    (fin9_cases _
      node_1431
      node_1432
      node_1436
      node_1437
      (invalid_excluded a [6,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,8] (by decide +kernel)))

theorem node_1402 : Excluded a [6,4,8] :=
  branch_excluded a [6,4,8] (by decide)
    (fin9_cases _
      node_1403
      node_1427
      node_1428
      (invalid_excluded a [6,4,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,4] (by decide +kernel))
      node_1429
      (invalid_excluded a [6,4,8,6] (by decide +kernel))
      node_1430
      (invalid_excluded a [6,4,8,8] (by decide +kernel)))

theorem node_1335 : Excluded a [6,4] :=
  branch_excluded a [6,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0] (by decide +kernel))
      node_1336
      (invalid_excluded a [6,4,2] (by decide +kernel))
      node_1337
      (invalid_excluded a [6,4,4] (by decide +kernel))
      node_1369
      (invalid_excluded a [6,4,6] (by decide +kernel))
      node_1370
      node_1402)

theorem node_1448 : Excluded a [6,5,1] :=
  source_excluded a [6,5,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1450 : Excluded a [6,5,3,0] :=
  source_excluded a [6,5,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1451 : Excluded a [6,5,3,1] :=
  predecessor_excluded a [6,5,3,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1453 : Excluded a [6,5,3,2,0] :=
  predecessor_excluded a [6,5,3,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1454 : Excluded a [6,5,3,2,1] :=
  source_excluded a [6,5,3,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1456 : Excluded a [6,5,3,2,7,0] :=
  source_excluded a [6,5,3,2,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1457 : Excluded a [6,5,3,2,7,1] :=
  source_excluded a [6,5,3,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1458 : Excluded a [6,5,3,2,7,4] :=
  predecessor_excluded a [6,5,3,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1459 : Excluded a [6,5,3,2,7,8] :=
  predecessor_excluded a [6,5,3,2,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1455 : Excluded a [6,5,3,2,7] :=
  branch_excluded a [6,5,3,2,7] (by decide)
    (fin9_cases _
      node_1456
      node_1457
      (invalid_excluded a [6,5,3,2,7,2] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,7,3] (by decide +kernel))
      node_1458
      (invalid_excluded a [6,5,3,2,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,7,7] (by decide +kernel))
      node_1459)

theorem node_1461 : Excluded a [6,5,3,2,8,0] :=
  source_excluded a [6,5,3,2,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1462 : Excluded a [6,5,3,2,8,1] :=
  source_excluded a [6,5,3,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1465 : Excluded a [6,5,3,2,8,4,0,1] :=
  predecessor_excluded a [6,5,3,2,8,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_1464 : Excluded a [6,5,3,2,8,4,0] :=
  branch_excluded a [6,5,3,2,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,3,2,8,4,0,0] (by decide +kernel))
      node_1465
      (invalid_excluded a [6,5,3,2,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,0,8] (by decide +kernel)))

theorem node_1466 : Excluded a [6,5,3,2,8,4,1] :=
  source_excluded a [6,5,3,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1463 : Excluded a [6,5,3,2,8,4] :=
  branch_excluded a [6,5,3,2,8,4] (by decide)
    (fin9_cases _
      node_1464
      node_1466
      (invalid_excluded a [6,5,3,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,4,8] (by decide +kernel)))

theorem node_1467 : Excluded a [6,5,3,2,8,7] :=
  source_excluded a [6,5,3,2,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1460 : Excluded a [6,5,3,2,8] :=
  branch_excluded a [6,5,3,2,8] (by decide)
    (fin9_cases _
      node_1461
      node_1462
      (invalid_excluded a [6,5,3,2,8,2] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,3] (by decide +kernel))
      node_1463
      (invalid_excluded a [6,5,3,2,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,8,6] (by decide +kernel))
      node_1467
      (invalid_excluded a [6,5,3,2,8,8] (by decide +kernel)))

theorem node_1452 : Excluded a [6,5,3,2] :=
  branch_excluded a [6,5,3,2] (by decide)
    (fin9_cases _
      node_1453
      node_1454
      (invalid_excluded a [6,5,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,3,2,6] (by decide +kernel))
      node_1455
      node_1460)

theorem node_1469 : Excluded a [6,5,3,7,0] :=
  predecessor_excluded a [6,5,3,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1470 : Excluded a [6,5,3,7,1] :=
  source_excluded a [6,5,3,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1471 : Excluded a [6,5,3,7,2] :=
  source_excluded a [6,5,3,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1472 : Excluded a [6,5,3,7,8] :=
  predecessor_excluded a [6,5,3,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1468 : Excluded a [6,5,3,7] :=
  branch_excluded a [6,5,3,7] (by decide)
    (fin9_cases _
      node_1469
      node_1470
      node_1471
      (invalid_excluded a [6,5,3,7,3] (by decide +kernel))
      (invalid_excluded a [6,5,3,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,3,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,3,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,3,7,7] (by decide +kernel))
      node_1472)

theorem node_1474 : Excluded a [6,5,3,8,0] :=
  predecessor_excluded a [6,5,3,8,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1475 : Excluded a [6,5,3,8,1] :=
  source_excluded a [6,5,3,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1476 : Excluded a [6,5,3,8,2] :=
  source_excluded a [6,5,3,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1478 : Excluded a [6,5,3,8,7,0] :=
  source_excluded a [6,5,3,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1479 : Excluded a [6,5,3,8,7,1] :=
  source_excluded a [6,5,3,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1480 : Excluded a [6,5,3,8,7,2] :=
  source_excluded a [6,5,3,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1481 : Excluded a [6,5,3,8,7,4] :=
  predecessor_excluded a [6,5,3,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1477 : Excluded a [6,5,3,8,7] :=
  branch_excluded a [6,5,3,8,7] (by decide)
    (fin9_cases _
      node_1478
      node_1479
      node_1480
      (invalid_excluded a [6,5,3,8,7,3] (by decide +kernel))
      node_1481
      (invalid_excluded a [6,5,3,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,3,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,3,8,7,8] (by decide +kernel)))

theorem node_1473 : Excluded a [6,5,3,8] :=
  branch_excluded a [6,5,3,8] (by decide)
    (fin9_cases _
      node_1474
      node_1475
      node_1476
      (invalid_excluded a [6,5,3,8,3] (by decide +kernel))
      (invalid_excluded a [6,5,3,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,3,8,6] (by decide +kernel))
      node_1477
      (invalid_excluded a [6,5,3,8,8] (by decide +kernel)))

theorem node_1449 : Excluded a [6,5,3] :=
  branch_excluded a [6,5,3] (by decide)
    (fin9_cases _
      node_1450
      node_1451
      node_1452
      (invalid_excluded a [6,5,3,3] (by decide +kernel))
      (invalid_excluded a [6,5,3,4] (by decide +kernel))
      (invalid_excluded a [6,5,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,3,6] (by decide +kernel))
      node_1468
      node_1473)

theorem node_1483 : Excluded a [6,5,4,0] :=
  source_excluded a [6,5,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1484 : Excluded a [6,5,4,1] :=
  predecessor_excluded a [6,5,4,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1485 : Excluded a [6,5,4,2] :=
  source_excluded a [6,5,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_1487 : Excluded a [6,5,4,7,0] :=
  source_excluded a [6,5,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1488 : Excluded a [6,5,4,7,1] :=
  source_excluded a [6,5,4,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1489 : Excluded a [6,5,4,7,2] :=
  source_excluded a [6,5,4,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1491 : Excluded a [6,5,4,7,3,0] :=
  source_excluded a [6,5,4,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1492 : Excluded a [6,5,4,7,3,1] :=
  source_excluded a [6,5,4,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1493 : Excluded a [6,5,4,7,3,2] :=
  source_excluded a [6,5,4,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1496 : Excluded a [6,5,4,7,3,8,0,1] :=
  predecessor_excluded a [6,5,4,7,3,8,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_1498 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 5
  | 2 => 4
  | 3 => 7
  | 4 => 3
  | 5 => 8
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_1498 : LosingRegion (edgeOf a b_1498) 0 :=
  losingMask a b_1498 0 1847682382997598279568384
    (by decide +kernel) (by decide +kernel)

theorem node_1498 : Excluded a [6,5,4,7,3,8,0,2,1] :=
  losing_excluded a [6,5,4,7,3,8,0,2,1] (by decide) b_1498 (by decide +kernel) 1 0 2 cert_1498 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1498 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1847682382997598279568384 1 2; decide +kernel)

theorem node_1497 : Excluded a [6,5,4,7,3,8,0,2] :=
  branch_excluded a [6,5,4,7,3,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,4,7,3,8,0,2,0] (by decide +kernel))
      node_1498
      (invalid_excluded a [6,5,4,7,3,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,2,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,2,8] (by decide +kernel)))

theorem node_1495 : Excluded a [6,5,4,7,3,8,0] :=
  branch_excluded a [6,5,4,7,3,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,4,7,3,8,0,0] (by decide +kernel))
      node_1496
      node_1497
      (invalid_excluded a [6,5,4,7,3,8,0,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,0,8] (by decide +kernel)))

theorem node_1499 : Excluded a [6,5,4,7,3,8,1] :=
  source_excluded a [6,5,4,7,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1500 : Excluded a [6,5,4,7,3,8,2] :=
  predecessor_excluded a [6,5,4,7,3,8,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1494 : Excluded a [6,5,4,7,3,8] :=
  branch_excluded a [6,5,4,7,3,8] (by decide)
    (fin9_cases _
      node_1495
      node_1499
      node_1500
      (invalid_excluded a [6,5,4,7,3,8,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,8,8] (by decide +kernel)))

theorem node_1490 : Excluded a [6,5,4,7,3] :=
  branch_excluded a [6,5,4,7,3] (by decide)
    (fin9_cases _
      node_1491
      node_1492
      node_1493
      (invalid_excluded a [6,5,4,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,3,7] (by decide +kernel))
      node_1494)

theorem node_1501 : Excluded a [6,5,4,7,8] :=
  predecessor_excluded a [6,5,4,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1486 : Excluded a [6,5,4,7] :=
  branch_excluded a [6,5,4,7] (by decide)
    (fin9_cases _
      node_1487
      node_1488
      node_1489
      node_1490
      (invalid_excluded a [6,5,4,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,7,7] (by decide +kernel))
      node_1501)

theorem node_1503 : Excluded a [6,5,4,8,0] :=
  source_excluded a [6,5,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1504 : Excluded a [6,5,4,8,1] :=
  source_excluded a [6,5,4,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1505 : Excluded a [6,5,4,8,2] :=
  source_excluded a [6,5,4,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1506 : Excluded a [6,5,4,8,3] :=
  predecessor_excluded a [6,5,4,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1508 : Excluded a [6,5,4,8,7,0] :=
  source_excluded a [6,5,4,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1509 : Excluded a [6,5,4,8,7,1] :=
  source_excluded a [6,5,4,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1510 : Excluded a [6,5,4,8,7,2] :=
  source_excluded a [6,5,4,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1513 : Excluded a [6,5,4,8,7,3,0,1] :=
  predecessor_excluded a [6,5,4,8,7,3,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_1515 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 5
  | 2 => 4
  | 3 => 8
  | 4 => 7
  | 5 => 3
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_1515 : LosingRegion (edgeOf a b_1515) 0 :=
  losingMask a b_1515 0 1847682382995401403796480
    (by decide +kernel) (by decide +kernel)

theorem node_1515 : Excluded a [6,5,4,8,7,3,0,2,1] :=
  losing_excluded a [6,5,4,8,7,3,0,2,1] (by decide) b_1515 (by decide +kernel) 1 0 2 cert_1515 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1515 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1847682382995401403796480 1 2; decide +kernel)

theorem node_1514 : Excluded a [6,5,4,8,7,3,0,2] :=
  branch_excluded a [6,5,4,8,7,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,4,8,7,3,0,2,0] (by decide +kernel))
      node_1515
      (invalid_excluded a [6,5,4,8,7,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,2,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,2,8] (by decide +kernel)))

theorem node_1512 : Excluded a [6,5,4,8,7,3,0] :=
  branch_excluded a [6,5,4,8,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,4,8,7,3,0,0] (by decide +kernel))
      node_1513
      node_1514
      (invalid_excluded a [6,5,4,8,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,0,8] (by decide +kernel)))

theorem node_1516 : Excluded a [6,5,4,8,7,3,1] :=
  source_excluded a [6,5,4,8,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1517 : Excluded a [6,5,4,8,7,3,2] :=
  predecessor_excluded a [6,5,4,8,7,3,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1511 : Excluded a [6,5,4,8,7,3] :=
  branch_excluded a [6,5,4,8,7,3] (by decide)
    (fin9_cases _
      node_1512
      node_1516
      node_1517
      (invalid_excluded a [6,5,4,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,3,8] (by decide +kernel)))

theorem node_1507 : Excluded a [6,5,4,8,7] :=
  branch_excluded a [6,5,4,8,7] (by decide)
    (fin9_cases _
      node_1508
      node_1509
      node_1510
      node_1511
      (invalid_excluded a [6,5,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,7,8] (by decide +kernel)))

theorem node_1502 : Excluded a [6,5,4,8] :=
  branch_excluded a [6,5,4,8] (by decide)
    (fin9_cases _
      node_1503
      node_1504
      node_1505
      node_1506
      (invalid_excluded a [6,5,4,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,8,6] (by decide +kernel))
      node_1507
      (invalid_excluded a [6,5,4,8,8] (by decide +kernel)))

theorem node_1482 : Excluded a [6,5,4] :=
  branch_excluded a [6,5,4] (by decide)
    (fin9_cases _
      node_1483
      node_1484
      node_1485
      (invalid_excluded a [6,5,4,3] (by decide +kernel))
      (invalid_excluded a [6,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,4,6] (by decide +kernel))
      node_1486
      node_1502)

theorem node_1520 : Excluded a [6,5,7,0,1] :=
  source_excluded a [6,5,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1521 : Excluded a [6,5,7,0,2] :=
  source_excluded a [6,5,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1523 : Excluded a [6,5,7,0,3,1] :=
  source_excluded a [6,5,7,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1524 : Excluded a [6,5,7,0,3,2] :=
  source_excluded a [6,5,7,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1525 : Excluded a [6,5,7,0,3,4] :=
  predecessor_excluded a [6,5,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1527 : Excluded a [6,5,7,0,3,8,1] :=
  source_excluded a [6,5,7,0,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1528 : Excluded a [6,5,7,0,3,8,2] :=
  source_excluded a [6,5,7,0,3,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1530 : Excluded a [6,5,7,0,3,8,4,1] :=
  predecessor_excluded a [6,5,7,0,3,8,4,1] 3 1 2 7 (by decide) (by decide +kernel)

def b_1532 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 5
  | 2 => 7
  | 3 => 0
  | 4 => 3
  | 5 => 8
  | 6 => 4
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_1532 : LosingRegion (edgeOf a b_1532) 1 :=
  losingMask a b_1532 1 1210109947697263646081025
    (by decide +kernel) (by decide +kernel)

theorem node_1532 : Excluded a [6,5,7,0,3,8,4,2,1] :=
  losing_excluded a [6,5,7,0,3,8,4,2,1] (by decide) b_1532 (by decide +kernel) 3 1 0 cert_1532 (by change 3 ≠ 1 ∧ ¬ edgeOf a b_1532 3 1 ∧ 0 ≠ 3 ∧ maskRegion 1210109947697263646081025 3 0; decide +kernel)

theorem node_1531 : Excluded a [6,5,7,0,3,8,4,2] :=
  branch_excluded a [6,5,7,0,3,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,3,8,4,2,0] (by decide +kernel))
      node_1532
      (invalid_excluded a [6,5,7,0,3,8,4,2,2] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,8] (by decide +kernel)))

theorem node_1529 : Excluded a [6,5,7,0,3,8,4] :=
  branch_excluded a [6,5,7,0,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,3,8,4,0] (by decide +kernel))
      node_1530
      node_1531
      (invalid_excluded a [6,5,7,0,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,8] (by decide +kernel)))

theorem node_1526 : Excluded a [6,5,7,0,3,8] :=
  branch_excluded a [6,5,7,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,3,8,0] (by decide +kernel))
      node_1527
      node_1528
      (invalid_excluded a [6,5,7,0,3,8,3] (by decide +kernel))
      node_1529
      (invalid_excluded a [6,5,7,0,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,8] (by decide +kernel)))

theorem node_1522 : Excluded a [6,5,7,0,3] :=
  branch_excluded a [6,5,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,3,0] (by decide +kernel))
      node_1523
      node_1524
      (invalid_excluded a [6,5,7,0,3,3] (by decide +kernel))
      node_1525
      (invalid_excluded a [6,5,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,7] (by decide +kernel))
      node_1526)

theorem node_1534 : Excluded a [6,5,7,0,8,1] :=
  source_excluded a [6,5,7,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1535 : Excluded a [6,5,7,0,8,2] :=
  source_excluded a [6,5,7,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1536 : Excluded a [6,5,7,0,8,3] :=
  predecessor_excluded a [6,5,7,0,8,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1538 : Excluded a [6,5,7,0,8,4,1] :=
  source_excluded a [6,5,7,0,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1539 : Excluded a [6,5,7,0,8,4,2] :=
  source_excluded a [6,5,7,0,8,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1541 : Excluded a [6,5,7,0,8,4,3,1] :=
  predecessor_excluded a [6,5,7,0,8,4,3,1] 3 1 2 7 (by decide) (by decide +kernel)

def b_1543 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 5
  | 2 => 7
  | 3 => 0
  | 4 => 8
  | 5 => 4
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_1543 : LosingRegion (edgeOf a b_1543) 1 :=
  losingMask a b_1543 1 1210109950089388497043457
    (by decide +kernel) (by decide +kernel)

theorem node_1543 : Excluded a [6,5,7,0,8,4,3,2,1] :=
  losing_excluded a [6,5,7,0,8,4,3,2,1] (by decide) b_1543 (by decide +kernel) 3 1 2 cert_1543 (by change 3 ≠ 1 ∧ ¬ edgeOf a b_1543 3 1 ∧ 2 ≠ 3 ∧ maskRegion 1210109950089388497043457 3 2; decide +kernel)

theorem node_1542 : Excluded a [6,5,7,0,8,4,3,2] :=
  branch_excluded a [6,5,7,0,8,4,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,4,3,2,0] (by decide +kernel))
      node_1543
      (invalid_excluded a [6,5,7,0,8,4,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,2,8] (by decide +kernel)))

theorem node_1540 : Excluded a [6,5,7,0,8,4,3] :=
  branch_excluded a [6,5,7,0,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,4,3,0] (by decide +kernel))
      node_1541
      node_1542
      (invalid_excluded a [6,5,7,0,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,3,8] (by decide +kernel)))

theorem node_1537 : Excluded a [6,5,7,0,8,4] :=
  branch_excluded a [6,5,7,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,4,0] (by decide +kernel))
      node_1538
      node_1539
      node_1540
      (invalid_excluded a [6,5,7,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,8] (by decide +kernel)))

theorem node_1533 : Excluded a [6,5,7,0,8] :=
  branch_excluded a [6,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,0] (by decide +kernel))
      node_1534
      node_1535
      node_1536
      node_1537
      (invalid_excluded a [6,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,8] (by decide +kernel)))

theorem node_1519 : Excluded a [6,5,7,0] :=
  branch_excluded a [6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,0] (by decide +kernel))
      node_1520
      node_1521
      node_1522
      (invalid_excluded a [6,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,7] (by decide +kernel))
      node_1533)

theorem node_1544 : Excluded a [6,5,7,1] :=
  predecessor_excluded a [6,5,7,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1546 : Excluded a [6,5,7,2,0] :=
  predecessor_excluded a [6,5,7,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1547 : Excluded a [6,5,7,2,1] :=
  source_excluded a [6,5,7,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1549 : Excluded a [6,5,7,2,3,0] :=
  source_excluded a [6,5,7,2,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1550 : Excluded a [6,5,7,2,3,1] :=
  source_excluded a [6,5,7,2,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1551 : Excluded a [6,5,7,2,3,4] :=
  predecessor_excluded a [6,5,7,2,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1553 : Excluded a [6,5,7,2,3,8,0] :=
  source_excluded a [6,5,7,2,3,8,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1554 : Excluded a [6,5,7,2,3,8,1] :=
  source_excluded a [6,5,7,2,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1556 : Excluded a [6,5,7,2,3,8,4,0] :=
  source_excluded a [6,5,7,2,3,8,4,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_1557 : Excluded a [6,5,7,2,3,8,4,1] :=
  predecessor_excluded a [6,5,7,2,3,8,4,1] 3 1 2 7 (by decide) (by decide +kernel)

theorem node_1555 : Excluded a [6,5,7,2,3,8,4] :=
  branch_excluded a [6,5,7,2,3,8,4] (by decide)
    (fin9_cases _
      node_1556
      node_1557
      (invalid_excluded a [6,5,7,2,3,8,4,2] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,4,8] (by decide +kernel)))

theorem node_1552 : Excluded a [6,5,7,2,3,8] :=
  branch_excluded a [6,5,7,2,3,8] (by decide)
    (fin9_cases _
      node_1553
      node_1554
      (invalid_excluded a [6,5,7,2,3,8,2] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,3] (by decide +kernel))
      node_1555
      (invalid_excluded a [6,5,7,2,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,8,8] (by decide +kernel)))

theorem node_1548 : Excluded a [6,5,7,2,3] :=
  branch_excluded a [6,5,7,2,3] (by decide)
    (fin9_cases _
      node_1549
      node_1550
      (invalid_excluded a [6,5,7,2,3,2] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,3] (by decide +kernel))
      node_1551
      (invalid_excluded a [6,5,7,2,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,3,7] (by decide +kernel))
      node_1552)

theorem node_1559 : Excluded a [6,5,7,2,8,0] :=
  source_excluded a [6,5,7,2,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1560 : Excluded a [6,5,7,2,8,1] :=
  source_excluded a [6,5,7,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1561 : Excluded a [6,5,7,2,8,3] :=
  predecessor_excluded a [6,5,7,2,8,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1563 : Excluded a [6,5,7,2,8,4,0] :=
  source_excluded a [6,5,7,2,8,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1564 : Excluded a [6,5,7,2,8,4,1] :=
  source_excluded a [6,5,7,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1566 : Excluded a [6,5,7,2,8,4,3,0] :=
  source_excluded a [6,5,7,2,8,4,3,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_1567 : Excluded a [6,5,7,2,8,4,3,1] :=
  predecessor_excluded a [6,5,7,2,8,4,3,1] 3 1 2 7 (by decide) (by decide +kernel)

theorem node_1565 : Excluded a [6,5,7,2,8,4,3] :=
  branch_excluded a [6,5,7,2,8,4,3] (by decide)
    (fin9_cases _
      node_1566
      node_1567
      (invalid_excluded a [6,5,7,2,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,3,8] (by decide +kernel)))

theorem node_1562 : Excluded a [6,5,7,2,8,4] :=
  branch_excluded a [6,5,7,2,8,4] (by decide)
    (fin9_cases _
      node_1563
      node_1564
      (invalid_excluded a [6,5,7,2,8,4,2] (by decide +kernel))
      node_1565
      (invalid_excluded a [6,5,7,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,8] (by decide +kernel)))

theorem node_1558 : Excluded a [6,5,7,2,8] :=
  branch_excluded a [6,5,7,2,8] (by decide)
    (fin9_cases _
      node_1559
      node_1560
      (invalid_excluded a [6,5,7,2,8,2] (by decide +kernel))
      node_1561
      node_1562
      (invalid_excluded a [6,5,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,8] (by decide +kernel)))

theorem node_1545 : Excluded a [6,5,7,2] :=
  branch_excluded a [6,5,7,2] (by decide)
    (fin9_cases _
      node_1546
      node_1547
      (invalid_excluded a [6,5,7,2,2] (by decide +kernel))
      node_1548
      (invalid_excluded a [6,5,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,7] (by decide +kernel))
      node_1558)

theorem node_1569 : Excluded a [6,5,7,8,0] :=
  predecessor_excluded a [6,5,7,8,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1570 : Excluded a [6,5,7,8,1] :=
  source_excluded a [6,5,7,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1571 : Excluded a [6,5,7,8,2] :=
  source_excluded a [6,5,7,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1572 : Excluded a [6,5,7,8,3] :=
  predecessor_excluded a [6,5,7,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1568 : Excluded a [6,5,7,8] :=
  branch_excluded a [6,5,7,8] (by decide)
    (fin9_cases _
      node_1569
      node_1570
      node_1571
      node_1572
      (invalid_excluded a [6,5,7,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,8,8] (by decide +kernel)))

theorem node_1518 : Excluded a [6,5,7] :=
  branch_excluded a [6,5,7] (by decide)
    (fin9_cases _
      node_1519
      node_1544
      node_1545
      (invalid_excluded a [6,5,7,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,7] (by decide +kernel))
      node_1568)

theorem node_1575 : Excluded a [6,5,8,0,1] :=
  source_excluded a [6,5,8,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1576 : Excluded a [6,5,8,0,2] :=
  source_excluded a [6,5,8,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1578 : Excluded a [6,5,8,0,3,1] :=
  source_excluded a [6,5,8,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1579 : Excluded a [6,5,8,0,3,2] :=
  source_excluded a [6,5,8,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1580 : Excluded a [6,5,8,0,3,4] :=
  predecessor_excluded a [6,5,8,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1581 : Excluded a [6,5,8,0,3,7] :=
  source_excluded a [6,5,8,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1577 : Excluded a [6,5,8,0,3] :=
  branch_excluded a [6,5,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,8,0,3,0] (by decide +kernel))
      node_1578
      node_1579
      (invalid_excluded a [6,5,8,0,3,3] (by decide +kernel))
      node_1580
      (invalid_excluded a [6,5,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,0,3,6] (by decide +kernel))
      node_1581
      (invalid_excluded a [6,5,8,0,3,8] (by decide +kernel)))

theorem node_1583 : Excluded a [6,5,8,0,7,1] :=
  source_excluded a [6,5,8,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1584 : Excluded a [6,5,8,0,7,2] :=
  source_excluded a [6,5,8,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1586 : Excluded a [6,5,8,0,7,3,1] :=
  source_excluded a [6,5,8,0,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1587 : Excluded a [6,5,8,0,7,3,2] :=
  predecessor_excluded a [6,5,8,0,7,3,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1588 : Excluded a [6,5,8,0,7,3,4] :=
  source_excluded a [6,5,8,0,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1585 : Excluded a [6,5,8,0,7,3] :=
  branch_excluded a [6,5,8,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,8,0,7,3,0] (by decide +kernel))
      node_1586
      node_1587
      (invalid_excluded a [6,5,8,0,7,3,3] (by decide +kernel))
      node_1588
      (invalid_excluded a [6,5,8,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,0,7,3,8] (by decide +kernel)))

theorem node_1589 : Excluded a [6,5,8,0,7,4] :=
  predecessor_excluded a [6,5,8,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1582 : Excluded a [6,5,8,0,7] :=
  branch_excluded a [6,5,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,8,0,7,0] (by decide +kernel))
      node_1583
      node_1584
      node_1585
      node_1589
      (invalid_excluded a [6,5,8,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,0,7,8] (by decide +kernel)))

theorem node_1574 : Excluded a [6,5,8,0] :=
  branch_excluded a [6,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,8,0,0] (by decide +kernel))
      node_1575
      node_1576
      node_1577
      (invalid_excluded a [6,5,8,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,0,6] (by decide +kernel))
      node_1582
      (invalid_excluded a [6,5,8,0,8] (by decide +kernel)))

theorem node_1590 : Excluded a [6,5,8,1] :=
  predecessor_excluded a [6,5,8,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1592 : Excluded a [6,5,8,2,0] :=
  predecessor_excluded a [6,5,8,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1593 : Excluded a [6,5,8,2,1] :=
  source_excluded a [6,5,8,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1595 : Excluded a [6,5,8,2,3,0] :=
  source_excluded a [6,5,8,2,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1596 : Excluded a [6,5,8,2,3,1] :=
  source_excluded a [6,5,8,2,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1597 : Excluded a [6,5,8,2,3,4] :=
  predecessor_excluded a [6,5,8,2,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1598 : Excluded a [6,5,8,2,3,7] :=
  source_excluded a [6,5,8,2,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1594 : Excluded a [6,5,8,2,3] :=
  branch_excluded a [6,5,8,2,3] (by decide)
    (fin9_cases _
      node_1595
      node_1596
      (invalid_excluded a [6,5,8,2,3,2] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,3,3] (by decide +kernel))
      node_1597
      (invalid_excluded a [6,5,8,2,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,3,6] (by decide +kernel))
      node_1598
      (invalid_excluded a [6,5,8,2,3,8] (by decide +kernel)))

theorem node_1600 : Excluded a [6,5,8,2,7,0] :=
  source_excluded a [6,5,8,2,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1601 : Excluded a [6,5,8,2,7,1] :=
  source_excluded a [6,5,8,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1604 : Excluded a [6,5,8,2,7,3,0,1] :=
  predecessor_excluded a [6,5,8,2,7,3,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_1606 : Excluded a [6,5,8,2,7,3,0,4,1] :=
  predecessor_excluded a [6,5,8,2,7,3,0,4,1] 0 2 8 3 (by decide) (by decide +kernel)

theorem node_1605 : Excluded a [6,5,8,2,7,3,0,4] :=
  branch_excluded a [6,5,8,2,7,3,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,8,2,7,3,0,4,0] (by decide +kernel))
      node_1606
      (invalid_excluded a [6,5,8,2,7,3,0,4,2] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,4,3] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,4,8] (by decide +kernel)))

theorem node_1603 : Excluded a [6,5,8,2,7,3,0] :=
  branch_excluded a [6,5,8,2,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,8,2,7,3,0,0] (by decide +kernel))
      node_1604
      (invalid_excluded a [6,5,8,2,7,3,0,2] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,3] (by decide +kernel))
      node_1605
      (invalid_excluded a [6,5,8,2,7,3,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,0,8] (by decide +kernel)))

theorem node_1607 : Excluded a [6,5,8,2,7,3,1] :=
  source_excluded a [6,5,8,2,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1608 : Excluded a [6,5,8,2,7,3,4] :=
  source_excluded a [6,5,8,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1602 : Excluded a [6,5,8,2,7,3] :=
  branch_excluded a [6,5,8,2,7,3] (by decide)
    (fin9_cases _
      node_1603
      node_1607
      (invalid_excluded a [6,5,8,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,3] (by decide +kernel))
      node_1608
      (invalid_excluded a [6,5,8,2,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,3,8] (by decide +kernel)))

theorem node_1609 : Excluded a [6,5,8,2,7,4] :=
  predecessor_excluded a [6,5,8,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1599 : Excluded a [6,5,8,2,7] :=
  branch_excluded a [6,5,8,2,7] (by decide)
    (fin9_cases _
      node_1600
      node_1601
      (invalid_excluded a [6,5,8,2,7,2] (by decide +kernel))
      node_1602
      node_1609
      (invalid_excluded a [6,5,8,2,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,8] (by decide +kernel)))

theorem node_1591 : Excluded a [6,5,8,2] :=
  branch_excluded a [6,5,8,2] (by decide)
    (fin9_cases _
      node_1592
      node_1593
      (invalid_excluded a [6,5,8,2,2] (by decide +kernel))
      node_1594
      (invalid_excluded a [6,5,8,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,6] (by decide +kernel))
      node_1599
      (invalid_excluded a [6,5,8,2,8] (by decide +kernel)))

theorem node_1611 : Excluded a [6,5,8,7,0] :=
  predecessor_excluded a [6,5,8,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1612 : Excluded a [6,5,8,7,1] :=
  source_excluded a [6,5,8,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1613 : Excluded a [6,5,8,7,2] :=
  source_excluded a [6,5,8,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1615 : Excluded a [6,5,8,7,3,0] :=
  source_excluded a [6,5,8,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1616 : Excluded a [6,5,8,7,3,1] :=
  source_excluded a [6,5,8,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1617 : Excluded a [6,5,8,7,3,2] :=
  source_excluded a [6,5,8,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1618 : Excluded a [6,5,8,7,3,4] :=
  predecessor_excluded a [6,5,8,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1614 : Excluded a [6,5,8,7,3] :=
  branch_excluded a [6,5,8,7,3] (by decide)
    (fin9_cases _
      node_1615
      node_1616
      node_1617
      (invalid_excluded a [6,5,8,7,3,3] (by decide +kernel))
      node_1618
      (invalid_excluded a [6,5,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,3,8] (by decide +kernel)))

theorem node_1610 : Excluded a [6,5,8,7] :=
  branch_excluded a [6,5,8,7] (by decide)
    (fin9_cases _
      node_1611
      node_1612
      node_1613
      node_1614
      (invalid_excluded a [6,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,8] (by decide +kernel)))

theorem node_1573 : Excluded a [6,5,8] :=
  branch_excluded a [6,5,8] (by decide)
    (fin9_cases _
      node_1574
      node_1590
      node_1591
      (invalid_excluded a [6,5,8,3] (by decide +kernel))
      (invalid_excluded a [6,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,6] (by decide +kernel))
      node_1610
      (invalid_excluded a [6,5,8,8] (by decide +kernel)))

theorem node_1447 : Excluded a [6,5] :=
  branch_excluded a [6,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0] (by decide +kernel))
      node_1448
      (invalid_excluded a [6,5,2] (by decide +kernel))
      node_1449
      node_1482
      (invalid_excluded a [6,5,5] (by decide +kernel))
      (invalid_excluded a [6,5,6] (by decide +kernel))
      node_1518
      node_1573)

theorem node_1619 : Excluded a [6,7] :=
  predecessor_excluded a [6,7] 2 7 0 1 (by decide) (by decide +kernel)

theorem node_1621 : Excluded a [6,8,1] :=
  source_excluded a [6,8,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1622 : Excluded a [6,8,3] :=
  predecessor_excluded a [6,8,3] 0 3 1 2 (by decide) (by decide +kernel)

theorem node_1624 : Excluded a [6,8,4,0] :=
  source_excluded a [6,8,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1626 : Excluded a [6,8,4,1,0] :=
  source_excluded a [6,8,4,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1627 : Excluded a [6,8,4,1,2] :=
  predecessor_excluded a [6,8,4,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1629 : Excluded a [6,8,4,1,3,0] :=
  source_excluded a [6,8,4,1,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1631 : Excluded a [6,8,4,1,3,2,0] :=
  predecessor_excluded a [6,8,4,1,3,2,0] 1 0 5 6 (by decide) (by decide +kernel)

def b_1634 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 4
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 5
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_1634 : LosingRegion (edgeOf a b_1634) 0 :=
  losingMask a b_1634 0 2116801930001435803534336
    (by decide +kernel) (by decide +kernel)

theorem node_1634 : Excluded a [6,8,4,1,3,2,5,0,7] :=
  losing_excluded a [6,8,4,1,3,2,5,0,7] (by decide) b_1634 (by decide +kernel) 1 0 5 cert_1634 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1634 1 0 ∧ 5 ≠ 1 ∧ maskRegion 2116801930001435803534336 1 5; decide +kernel)

theorem node_1633 : Excluded a [6,8,4,1,3,2,5,0] :=
  branch_excluded a [6,8,4,1,3,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,4,1,3,2,5,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,0,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,0,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,0,6] (by decide +kernel))
      node_1634
      (invalid_excluded a [6,8,4,1,3,2,5,0,8] (by decide +kernel)))

theorem node_1632 : Excluded a [6,8,4,1,3,2,5] :=
  branch_excluded a [6,8,4,1,3,2,5] (by decide)
    (fin9_cases _
      node_1633
      (invalid_excluded a [6,8,4,1,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,5,8] (by decide +kernel)))

theorem node_1630 : Excluded a [6,8,4,1,3,2] :=
  branch_excluded a [6,8,4,1,3,2] (by decide)
    (fin9_cases _
      node_1631
      (invalid_excluded a [6,8,4,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,4] (by decide +kernel))
      node_1632
      (invalid_excluded a [6,8,4,1,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,2,8] (by decide +kernel)))

theorem node_1635 : Excluded a [6,8,4,1,3,7] :=
  source_excluded a [6,8,4,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1628 : Excluded a [6,8,4,1,3] :=
  branch_excluded a [6,8,4,1,3] (by decide)
    (fin9_cases _
      node_1629
      (invalid_excluded a [6,8,4,1,3,1] (by decide +kernel))
      node_1630
      (invalid_excluded a [6,8,4,1,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,3,6] (by decide +kernel))
      node_1635
      (invalid_excluded a [6,8,4,1,3,8] (by decide +kernel)))

theorem node_1637 : Excluded a [6,8,4,1,7,0] :=
  source_excluded a [6,8,4,1,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1639 : Excluded a [6,8,4,1,7,2,0] :=
  predecessor_excluded a [6,8,4,1,7,2,0] 1 0 5 6 (by decide) (by decide +kernel)

def b_1642 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 4
  | 3 => 1
  | 4 => 7
  | 5 => 2
  | 6 => 3
  | 7 => 0
  | 8 => 5
  | _ => 0

def cert_1642 : LosingRegion (edgeOf a b_1642) 0 :=
  losingMask a b_1642 0 1465115643729928852098048
    (by decide +kernel) (by decide +kernel)

theorem node_1642 : Excluded a [6,8,4,1,7,2,3,0,5] :=
  losing_excluded a [6,8,4,1,7,2,3,0,5] (by decide) b_1642 (by decide +kernel) 1 0 2 cert_1642 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1642 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1465115643729928852098048 1 2; decide +kernel)

theorem node_1641 : Excluded a [6,8,4,1,7,2,3,0] :=
  branch_excluded a [6,8,4,1,7,2,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,4,1,7,2,3,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,0,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,0,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,0,4] (by decide +kernel))
      node_1642
      (invalid_excluded a [6,8,4,1,7,2,3,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,0,8] (by decide +kernel)))

theorem node_1643 : Excluded a [6,8,4,1,7,2,3,5] :=
  source_excluded a [6,8,4,1,7,2,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1640 : Excluded a [6,8,4,1,7,2,3] :=
  branch_excluded a [6,8,4,1,7,2,3] (by decide)
    (fin9_cases _
      node_1641
      (invalid_excluded a [6,8,4,1,7,2,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,4] (by decide +kernel))
      node_1643
      (invalid_excluded a [6,8,4,1,7,2,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,3,8] (by decide +kernel)))

theorem node_1644 : Excluded a [6,8,4,1,7,2,5] :=
  source_excluded a [6,8,4,1,7,2,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1638 : Excluded a [6,8,4,1,7,2] :=
  branch_excluded a [6,8,4,1,7,2] (by decide)
    (fin9_cases _
      node_1639
      (invalid_excluded a [6,8,4,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,2] (by decide +kernel))
      node_1640
      (invalid_excluded a [6,8,4,1,7,2,4] (by decide +kernel))
      node_1644
      (invalid_excluded a [6,8,4,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,2,8] (by decide +kernel)))

theorem node_1647 : Excluded a [6,8,4,1,7,3,0,2] :=
  source_excluded a [6,8,4,1,7,3,0,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_1648 : Excluded a [6,8,4,1,7,3,0,5] :=
  source_excluded a [6,8,4,1,7,3,0,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1646 : Excluded a [6,8,4,1,7,3,0] :=
  branch_excluded a [6,8,4,1,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,4,1,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,3,0,1] (by decide +kernel))
      node_1647
      (invalid_excluded a [6,8,4,1,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,3,0,4] (by decide +kernel))
      node_1648
      (invalid_excluded a [6,8,4,1,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,3,0,8] (by decide +kernel)))

theorem node_1649 : Excluded a [6,8,4,1,7,3,2] :=
  predecessor_excluded a [6,8,4,1,7,3,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1650 : Excluded a [6,8,4,1,7,3,5] :=
  source_excluded a [6,8,4,1,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1645 : Excluded a [6,8,4,1,7,3] :=
  branch_excluded a [6,8,4,1,7,3] (by decide)
    (fin9_cases _
      node_1646
      (invalid_excluded a [6,8,4,1,7,3,1] (by decide +kernel))
      node_1649
      (invalid_excluded a [6,8,4,1,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,3,4] (by decide +kernel))
      node_1650
      (invalid_excluded a [6,8,4,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,3,8] (by decide +kernel)))

theorem node_1636 : Excluded a [6,8,4,1,7] :=
  branch_excluded a [6,8,4,1,7] (by decide)
    (fin9_cases _
      node_1637
      (invalid_excluded a [6,8,4,1,7,1] (by decide +kernel))
      node_1638
      node_1645
      (invalid_excluded a [6,8,4,1,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,7,8] (by decide +kernel)))

theorem node_1625 : Excluded a [6,8,4,1] :=
  branch_excluded a [6,8,4,1] (by decide)
    (fin9_cases _
      node_1626
      (invalid_excluded a [6,8,4,1,1] (by decide +kernel))
      node_1627
      node_1628
      (invalid_excluded a [6,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,1,6] (by decide +kernel))
      node_1636
      (invalid_excluded a [6,8,4,1,8] (by decide +kernel)))

theorem node_1651 : Excluded a [6,8,4,2] :=
  source_excluded a [6,8,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_1652 : Excluded a [6,8,4,5] :=
  source_excluded a [6,8,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1654 : Excluded a [6,8,4,7,0] :=
  source_excluded a [6,8,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1655 : Excluded a [6,8,4,7,1] :=
  predecessor_excluded a [6,8,4,7,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_1657 : Excluded a [6,8,4,7,2,0] :=
  source_excluded a [6,8,4,7,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1658 : Excluded a [6,8,4,7,2,1] :=
  source_excluded a [6,8,4,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1659 : Excluded a [6,8,4,7,2,3] :=
  predecessor_excluded a [6,8,4,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1656 : Excluded a [6,8,4,7,2] :=
  branch_excluded a [6,8,4,7,2] (by decide)
    (fin9_cases _
      node_1657
      node_1658
      (invalid_excluded a [6,8,4,7,2,2] (by decide +kernel))
      node_1659
      (invalid_excluded a [6,8,4,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,2,8] (by decide +kernel)))

theorem node_1661 : Excluded a [6,8,4,7,3,0] :=
  source_excluded a [6,8,4,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1662 : Excluded a [6,8,4,7,3,1] :=
  source_excluded a [6,8,4,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1664 : Excluded a [6,8,4,7,3,2,0] :=
  predecessor_excluded a [6,8,4,7,3,2,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_1665 : Excluded a [6,8,4,7,3,2,1] :=
  source_excluded a [6,8,4,7,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1668 : Excluded a [6,8,4,7,3,2,5,0,1] :=
  predecessor_excluded a [6,8,4,7,3,2,5,0,1] 2 1 7 8 (by decide) (by decide +kernel)

theorem node_1667 : Excluded a [6,8,4,7,3,2,5,0] :=
  branch_excluded a [6,8,4,7,3,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,4,7,3,2,5,0,0] (by decide +kernel))
      node_1668
      (invalid_excluded a [6,8,4,7,3,2,5,0,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,0,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,0,8] (by decide +kernel)))

theorem node_1669 : Excluded a [6,8,4,7,3,2,5,1] :=
  source_excluded a [6,8,4,7,3,2,5,1] 7 0 1 (by decide) (by decide +kernel)

theorem node_1666 : Excluded a [6,8,4,7,3,2,5] :=
  branch_excluded a [6,8,4,7,3,2,5] (by decide)
    (fin9_cases _
      node_1667
      node_1669
      (invalid_excluded a [6,8,4,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,5,8] (by decide +kernel)))

theorem node_1663 : Excluded a [6,8,4,7,3,2] :=
  branch_excluded a [6,8,4,7,3,2] (by decide)
    (fin9_cases _
      node_1664
      node_1665
      (invalid_excluded a [6,8,4,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,4] (by decide +kernel))
      node_1666
      (invalid_excluded a [6,8,4,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,2,8] (by decide +kernel)))

theorem node_1660 : Excluded a [6,8,4,7,3] :=
  branch_excluded a [6,8,4,7,3] (by decide)
    (fin9_cases _
      node_1661
      node_1662
      node_1663
      (invalid_excluded a [6,8,4,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,3,8] (by decide +kernel)))

theorem node_1653 : Excluded a [6,8,4,7] :=
  branch_excluded a [6,8,4,7] (by decide)
    (fin9_cases _
      node_1654
      node_1655
      node_1656
      node_1660
      (invalid_excluded a [6,8,4,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,4,7,8] (by decide +kernel)))

theorem node_1623 : Excluded a [6,8,4] :=
  branch_excluded a [6,8,4] (by decide)
    (fin9_cases _
      node_1624
      node_1625
      node_1651
      (invalid_excluded a [6,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,8,4,4] (by decide +kernel))
      node_1652
      (invalid_excluded a [6,8,4,6] (by decide +kernel))
      node_1653
      (invalid_excluded a [6,8,4,8] (by decide +kernel)))

theorem node_1670 : Excluded a [6,8,5] :=
  predecessor_excluded a [6,8,5] 1 6 2 0 (by decide) (by decide +kernel)

theorem node_1673 : Excluded a [6,8,7,0,1] :=
  predecessor_excluded a [6,8,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1675 : Excluded a [6,8,7,0,2,1] :=
  source_excluded a [6,8,7,0,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1677 : Excluded a [6,8,7,0,2,3,1] :=
  source_excluded a [6,8,7,0,2,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1678 : Excluded a [6,8,7,0,2,3,4] :=
  predecessor_excluded a [6,8,7,0,2,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1680 : Excluded a [6,8,7,0,2,3,5,1] :=
  source_excluded a [6,8,7,0,2,3,5,1] 7 0 1 (by decide) (by decide +kernel)

def b_1682 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 0
  | 4 => 2
  | 5 => 3
  | 6 => 5
  | 7 => 4
  | 8 => 1
  | _ => 0

def cert_1682 : LosingRegion (edgeOf a b_1682) 0 :=
  losingMask a b_1682 0 1212494157834521572017152
    (by decide +kernel) (by decide +kernel)

theorem node_1682 : Excluded a [6,8,7,0,2,3,5,4,1] :=
  losing_excluded a [6,8,7,0,2,3,5,4,1] (by decide) b_1682 (by decide +kernel) 4 0 1 cert_1682 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1682 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1212494157834521572017152 4 1; decide +kernel)

theorem node_1681 : Excluded a [6,8,7,0,2,3,5,4] :=
  branch_excluded a [6,8,7,0,2,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,3,5,4,0] (by decide +kernel))
      node_1682
      (invalid_excluded a [6,8,7,0,2,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,4,8] (by decide +kernel)))

theorem node_1679 : Excluded a [6,8,7,0,2,3,5] :=
  branch_excluded a [6,8,7,0,2,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,3,5,0] (by decide +kernel))
      node_1680
      (invalid_excluded a [6,8,7,0,2,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,3] (by decide +kernel))
      node_1681
      (invalid_excluded a [6,8,7,0,2,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,5,8] (by decide +kernel)))

theorem node_1676 : Excluded a [6,8,7,0,2,3] :=
  branch_excluded a [6,8,7,0,2,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,3,0] (by decide +kernel))
      node_1677
      (invalid_excluded a [6,8,7,0,2,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,3] (by decide +kernel))
      node_1678
      node_1679
      (invalid_excluded a [6,8,7,0,2,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,3,8] (by decide +kernel)))

theorem node_1684 : Excluded a [6,8,7,0,2,4,1] :=
  source_excluded a [6,8,7,0,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1686 : Excluded a [6,8,7,0,2,4,3,1] :=
  source_excluded a [6,8,7,0,2,4,3,1] 7 0 1 (by decide) (by decide +kernel)

def b_1688 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 7
  | 3 => 0
  | 4 => 2
  | 5 => 4
  | 6 => 3
  | 7 => 5
  | 8 => 1
  | _ => 0

def cert_1688 : LosingRegion (edgeOf a b_1688) 0 :=
  losingMask a b_1688 0 1212491816068543333532672
    (by decide +kernel) (by decide +kernel)

theorem node_1688 : Excluded a [6,8,7,0,2,4,3,5,1] :=
  losing_excluded a [6,8,7,0,2,4,3,5,1] (by decide) b_1688 (by decide +kernel) 4 0 1 cert_1688 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1688 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1212491816068543333532672 4 1; decide +kernel)

theorem node_1687 : Excluded a [6,8,7,0,2,4,3,5] :=
  branch_excluded a [6,8,7,0,2,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,4,3,5,0] (by decide +kernel))
      node_1688
      (invalid_excluded a [6,8,7,0,2,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,5,8] (by decide +kernel)))

theorem node_1685 : Excluded a [6,8,7,0,2,4,3] :=
  branch_excluded a [6,8,7,0,2,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,4,3,0] (by decide +kernel))
      node_1686
      (invalid_excluded a [6,8,7,0,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,4] (by decide +kernel))
      node_1687
      (invalid_excluded a [6,8,7,0,2,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,3,8] (by decide +kernel)))

theorem node_1689 : Excluded a [6,8,7,0,2,4,5] :=
  predecessor_excluded a [6,8,7,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1683 : Excluded a [6,8,7,0,2,4] :=
  branch_excluded a [6,8,7,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,4,0] (by decide +kernel))
      node_1684
      (invalid_excluded a [6,8,7,0,2,4,2] (by decide +kernel))
      node_1685
      (invalid_excluded a [6,8,7,0,2,4,4] (by decide +kernel))
      node_1689
      (invalid_excluded a [6,8,7,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,8] (by decide +kernel)))

theorem node_1674 : Excluded a [6,8,7,0,2] :=
  branch_excluded a [6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,0] (by decide +kernel))
      node_1675
      (invalid_excluded a [6,8,7,0,2,2] (by decide +kernel))
      node_1676
      node_1683
      (invalid_excluded a [6,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,8] (by decide +kernel)))

theorem node_1691 : Excluded a [6,8,7,0,3,1] :=
  source_excluded a [6,8,7,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1692 : Excluded a [6,8,7,0,3,2] :=
  predecessor_excluded a [6,8,7,0,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1693 : Excluded a [6,8,7,0,3,4] :=
  predecessor_excluded a [6,8,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1690 : Excluded a [6,8,7,0,3] :=
  branch_excluded a [6,8,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,3,0] (by decide +kernel))
      node_1691
      node_1692
      (invalid_excluded a [6,8,7,0,3,3] (by decide +kernel))
      node_1693
      (invalid_excluded a [6,8,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,3,8] (by decide +kernel)))

theorem node_1672 : Excluded a [6,8,7,0] :=
  branch_excluded a [6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,0] (by decide +kernel))
      node_1673
      node_1674
      node_1690
      (invalid_excluded a [6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,8] (by decide +kernel)))

theorem node_1695 : Excluded a [6,8,7,1,0] :=
  predecessor_excluded a [6,8,7,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1696 : Excluded a [6,8,7,1,2] :=
  predecessor_excluded a [6,8,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1698 : Excluded a [6,8,7,1,3,0] :=
  source_excluded a [6,8,7,1,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1699 : Excluded a [6,8,7,1,3,2] :=
  predecessor_excluded a [6,8,7,1,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1700 : Excluded a [6,8,7,1,3,4] :=
  predecessor_excluded a [6,8,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1697 : Excluded a [6,8,7,1,3] :=
  branch_excluded a [6,8,7,1,3] (by decide)
    (fin9_cases _
      node_1698
      (invalid_excluded a [6,8,7,1,3,1] (by decide +kernel))
      node_1699
      (invalid_excluded a [6,8,7,1,3,3] (by decide +kernel))
      node_1700
      (invalid_excluded a [6,8,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,3,8] (by decide +kernel)))

theorem node_1694 : Excluded a [6,8,7,1] :=
  branch_excluded a [6,8,7,1] (by decide)
    (fin9_cases _
      node_1695
      (invalid_excluded a [6,8,7,1,1] (by decide +kernel))
      node_1696
      node_1697
      (invalid_excluded a [6,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,8] (by decide +kernel)))

theorem node_1702 : Excluded a [6,8,7,2,0] :=
  predecessor_excluded a [6,8,7,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1704 : Excluded a [6,8,7,2,1,0] :=
  source_excluded a [6,8,7,2,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1706 : Excluded a [6,8,7,2,1,3,0] :=
  source_excluded a [6,8,7,2,1,3,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1707 : Excluded a [6,8,7,2,1,3,4] :=
  predecessor_excluded a [6,8,7,2,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1709 : Excluded a [6,8,7,2,1,3,5,0] :=
  source_excluded a [6,8,7,2,1,3,5,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_1711 : Excluded a [6,8,7,2,1,3,5,4,0] :=
  predecessor_excluded a [6,8,7,2,1,3,5,4,0] 3 0 1 8 (by decide) (by decide +kernel)

theorem node_1710 : Excluded a [6,8,7,2,1,3,5,4] :=
  branch_excluded a [6,8,7,2,1,3,5,4] (by decide)
    (fin9_cases _
      node_1711
      (invalid_excluded a [6,8,7,2,1,3,5,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,4,8] (by decide +kernel)))

theorem node_1708 : Excluded a [6,8,7,2,1,3,5] :=
  branch_excluded a [6,8,7,2,1,3,5] (by decide)
    (fin9_cases _
      node_1709
      (invalid_excluded a [6,8,7,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,3] (by decide +kernel))
      node_1710
      (invalid_excluded a [6,8,7,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,8] (by decide +kernel)))

theorem node_1705 : Excluded a [6,8,7,2,1,3] :=
  branch_excluded a [6,8,7,2,1,3] (by decide)
    (fin9_cases _
      node_1706
      (invalid_excluded a [6,8,7,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,3] (by decide +kernel))
      node_1707
      node_1708
      (invalid_excluded a [6,8,7,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,8] (by decide +kernel)))

theorem node_1713 : Excluded a [6,8,7,2,1,4,0] :=
  source_excluded a [6,8,7,2,1,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_1715 : Excluded a [6,8,7,2,1,4,3,0] :=
  source_excluded a [6,8,7,2,1,4,3,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_1717 : Excluded a [6,8,7,2,1,4,3,5,0] :=
  predecessor_excluded a [6,8,7,2,1,4,3,5,0] 3 0 1 8 (by decide) (by decide +kernel)

theorem node_1716 : Excluded a [6,8,7,2,1,4,3,5] :=
  branch_excluded a [6,8,7,2,1,4,3,5] (by decide)
    (fin9_cases _
      node_1717
      (invalid_excluded a [6,8,7,2,1,4,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,5,8] (by decide +kernel)))

theorem node_1714 : Excluded a [6,8,7,2,1,4,3] :=
  branch_excluded a [6,8,7,2,1,4,3] (by decide)
    (fin9_cases _
      node_1715
      (invalid_excluded a [6,8,7,2,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,4] (by decide +kernel))
      node_1716
      (invalid_excluded a [6,8,7,2,1,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,3,8] (by decide +kernel)))

theorem node_1718 : Excluded a [6,8,7,2,1,4,5] :=
  predecessor_excluded a [6,8,7,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1712 : Excluded a [6,8,7,2,1,4] :=
  branch_excluded a [6,8,7,2,1,4] (by decide)
    (fin9_cases _
      node_1713
      (invalid_excluded a [6,8,7,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,2] (by decide +kernel))
      node_1714
      (invalid_excluded a [6,8,7,2,1,4,4] (by decide +kernel))
      node_1718
      (invalid_excluded a [6,8,7,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,8] (by decide +kernel)))

theorem node_1703 : Excluded a [6,8,7,2,1] :=
  branch_excluded a [6,8,7,2,1] (by decide)
    (fin9_cases _
      node_1704
      (invalid_excluded a [6,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,2] (by decide +kernel))
      node_1705
      node_1712
      (invalid_excluded a [6,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,8] (by decide +kernel)))

theorem node_1720 : Excluded a [6,8,7,2,3,0] :=
  source_excluded a [6,8,7,2,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1721 : Excluded a [6,8,7,2,3,1] :=
  source_excluded a [6,8,7,2,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1722 : Excluded a [6,8,7,2,3,4] :=
  predecessor_excluded a [6,8,7,2,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1719 : Excluded a [6,8,7,2,3] :=
  branch_excluded a [6,8,7,2,3] (by decide)
    (fin9_cases _
      node_1720
      node_1721
      (invalid_excluded a [6,8,7,2,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,3,3] (by decide +kernel))
      node_1722
      (invalid_excluded a [6,8,7,2,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,3,8] (by decide +kernel)))

theorem node_1701 : Excluded a [6,8,7,2] :=
  branch_excluded a [6,8,7,2] (by decide)
    (fin9_cases _
      node_1702
      node_1703
      (invalid_excluded a [6,8,7,2,2] (by decide +kernel))
      node_1719
      (invalid_excluded a [6,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,8] (by decide +kernel)))

theorem node_1723 : Excluded a [6,8,7,5] :=
  source_excluded a [6,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1671 : Excluded a [6,8,7] :=
  branch_excluded a [6,8,7] (by decide)
    (fin9_cases _
      node_1672
      node_1694
      node_1701
      (invalid_excluded a [6,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,4] (by decide +kernel))
      node_1723
      (invalid_excluded a [6,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,8] (by decide +kernel)))

theorem node_1620 : Excluded a [6,8] :=
  branch_excluded a [6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0] (by decide +kernel))
      node_1621
      (invalid_excluded a [6,8,2] (by decide +kernel))
      node_1622
      node_1623
      node_1670
      (invalid_excluded a [6,8,6] (by decide +kernel))
      node_1671
      (invalid_excluded a [6,8,8] (by decide +kernel)))

theorem node_1265 : Excluded a [6] :=
  branch_excluded a [6] (by decide)
    (fin9_cases _
      node_1266
      (invalid_excluded a [6,1] (by decide +kernel))
      (invalid_excluded a [6,2] (by decide +kernel))
      node_1267
      node_1335
      node_1447
      (invalid_excluded a [6,6] (by decide +kernel))
      node_1619
      node_1620)

theorem node_1725 : Excluded a [7,0] :=
  source_excluded a [7,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_1727 : Excluded a [7,3,1] :=
  source_excluded a [7,3,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1728 : Excluded a [7,3,4] :=
  predecessor_excluded a [7,3,4] 0 4 1 2 (by decide) (by decide +kernel)

theorem node_1730 : Excluded a [7,3,5,0] :=
  predecessor_excluded a [7,3,5,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1732 : Excluded a [7,3,5,1,0] :=
  source_excluded a [7,3,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1733 : Excluded a [7,3,5,1,2] :=
  source_excluded a [7,3,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1734 : Excluded a [7,3,5,1,6] :=
  source_excluded a [7,3,5,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1736 : Excluded a [7,3,5,1,8,0] :=
  source_excluded a [7,3,5,1,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1738 : Excluded a [7,3,5,1,8,2,0] :=
  source_excluded a [7,3,5,1,8,2,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1739 : Excluded a [7,3,5,1,8,2,4] :=
  predecessor_excluded a [7,3,5,1,8,2,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1737 : Excluded a [7,3,5,1,8,2] :=
  branch_excluded a [7,3,5,1,8,2] (by decide)
    (fin9_cases _
      node_1738
      (invalid_excluded a [7,3,5,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,2,3] (by decide +kernel))
      node_1739
      (invalid_excluded a [7,3,5,1,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,2,8] (by decide +kernel)))

theorem node_1741 : Excluded a [7,3,5,1,8,4,0] :=
  source_excluded a [7,3,5,1,8,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1743 : Excluded a [7,3,5,1,8,4,2,0] :=
  predecessor_excluded a [7,3,5,1,8,4,2,0] 1 0 6 7 (by decide) (by decide +kernel)

theorem node_1745 : Excluded a [7,3,5,1,8,4,2,6,0] :=
  predecessor_excluded a [7,3,5,1,8,4,2,6,0] 2 1 8 3 (by decide) (by decide +kernel)

theorem node_1744 : Excluded a [7,3,5,1,8,4,2,6] :=
  branch_excluded a [7,3,5,1,8,4,2,6] (by decide)
    (fin9_cases _
      node_1745
      (invalid_excluded a [7,3,5,1,8,4,2,6,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,6,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,6,8] (by decide +kernel)))

theorem node_1742 : Excluded a [7,3,5,1,8,4,2] :=
  branch_excluded a [7,3,5,1,8,4,2] (by decide)
    (fin9_cases _
      node_1743
      (invalid_excluded a [7,3,5,1,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,5] (by decide +kernel))
      node_1744
      (invalid_excluded a [7,3,5,1,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,2,8] (by decide +kernel)))

theorem node_1740 : Excluded a [7,3,5,1,8,4] :=
  branch_excluded a [7,3,5,1,8,4] (by decide)
    (fin9_cases _
      node_1741
      (invalid_excluded a [7,3,5,1,8,4,1] (by decide +kernel))
      node_1742
      (invalid_excluded a [7,3,5,1,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,4,8] (by decide +kernel)))

theorem node_1735 : Excluded a [7,3,5,1,8] :=
  branch_excluded a [7,3,5,1,8] (by decide)
    (fin9_cases _
      node_1736
      (invalid_excluded a [7,3,5,1,8,1] (by decide +kernel))
      node_1737
      (invalid_excluded a [7,3,5,1,8,3] (by decide +kernel))
      node_1740
      (invalid_excluded a [7,3,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,8,8] (by decide +kernel)))

theorem node_1731 : Excluded a [7,3,5,1] :=
  branch_excluded a [7,3,5,1] (by decide)
    (fin9_cases _
      node_1732
      (invalid_excluded a [7,3,5,1,1] (by decide +kernel))
      node_1733
      (invalid_excluded a [7,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,1,5] (by decide +kernel))
      node_1734
      (invalid_excluded a [7,3,5,1,7] (by decide +kernel))
      node_1735)

theorem node_1746 : Excluded a [7,3,5,2] :=
  source_excluded a [7,3,5,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1748 : Excluded a [7,3,5,6,0] :=
  source_excluded a [7,3,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1750 : Excluded a [7,3,5,6,1,0] :=
  source_excluded a [7,3,5,6,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1751 : Excluded a [7,3,5,6,1,2] :=
  predecessor_excluded a [7,3,5,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1752 : Excluded a [7,3,5,6,1,4] :=
  source_excluded a [7,3,5,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1754 : Excluded a [7,3,5,6,1,8,0] :=
  source_excluded a [7,3,5,6,1,8,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1756 : Excluded a [7,3,5,6,1,8,2,0] :=
  predecessor_excluded a [7,3,5,6,1,8,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_1758 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 5
  | 3 => 6
  | 4 => 1
  | 5 => 8
  | 6 => 2
  | 7 => 4
  | 8 => 0
  | _ => 0

def cert_1758 : LosingRegion (edgeOf a b_1758) 0 :=
  losingMask a b_1758 0 1210402785249112668277760
    (by decide +kernel) (by decide +kernel)

theorem node_1758 : Excluded a [7,3,5,6,1,8,2,4,0] :=
  losing_excluded a [7,3,5,6,1,8,2,4,0] (by decide) b_1758 (by decide +kernel) 1 0 2 cert_1758 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1758 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1210402785249112668277760 1 2; decide +kernel)

theorem node_1757 : Excluded a [7,3,5,6,1,8,2,4] :=
  branch_excluded a [7,3,5,6,1,8,2,4] (by decide)
    (fin9_cases _
      node_1758
      (invalid_excluded a [7,3,5,6,1,8,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,4,8] (by decide +kernel)))

theorem node_1755 : Excluded a [7,3,5,6,1,8,2] :=
  branch_excluded a [7,3,5,6,1,8,2] (by decide)
    (fin9_cases _
      node_1756
      (invalid_excluded a [7,3,5,6,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,3] (by decide +kernel))
      node_1757
      (invalid_excluded a [7,3,5,6,1,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,2,8] (by decide +kernel)))

theorem node_1759 : Excluded a [7,3,5,6,1,8,4] :=
  source_excluded a [7,3,5,6,1,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1753 : Excluded a [7,3,5,6,1,8] :=
  branch_excluded a [7,3,5,6,1,8] (by decide)
    (fin9_cases _
      node_1754
      (invalid_excluded a [7,3,5,6,1,8,1] (by decide +kernel))
      node_1755
      (invalid_excluded a [7,3,5,6,1,8,3] (by decide +kernel))
      node_1759
      (invalid_excluded a [7,3,5,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,8,8] (by decide +kernel)))

theorem node_1749 : Excluded a [7,3,5,6,1] :=
  branch_excluded a [7,3,5,6,1] (by decide)
    (fin9_cases _
      node_1750
      (invalid_excluded a [7,3,5,6,1,1] (by decide +kernel))
      node_1751
      (invalid_excluded a [7,3,5,6,1,3] (by decide +kernel))
      node_1752
      (invalid_excluded a [7,3,5,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,1,7] (by decide +kernel))
      node_1753)

theorem node_1760 : Excluded a [7,3,5,6,2] :=
  source_excluded a [7,3,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1762 : Excluded a [7,3,5,6,8,0] :=
  source_excluded a [7,3,5,6,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1763 : Excluded a [7,3,5,6,8,1] :=
  predecessor_excluded a [7,3,5,6,8,1] 3 1 2 5 (by decide) (by decide +kernel)

theorem node_1765 : Excluded a [7,3,5,6,8,2,0] :=
  source_excluded a [7,3,5,6,8,2,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1766 : Excluded a [7,3,5,6,8,2,1] :=
  source_excluded a [7,3,5,6,8,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1767 : Excluded a [7,3,5,6,8,2,4] :=
  source_excluded a [7,3,5,6,8,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1764 : Excluded a [7,3,5,6,8,2] :=
  branch_excluded a [7,3,5,6,8,2] (by decide)
    (fin9_cases _
      node_1765
      node_1766
      (invalid_excluded a [7,3,5,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,2,3] (by decide +kernel))
      node_1767
      (invalid_excluded a [7,3,5,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,2,8] (by decide +kernel)))

theorem node_1768 : Excluded a [7,3,5,6,8,4] :=
  source_excluded a [7,3,5,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1761 : Excluded a [7,3,5,6,8] :=
  branch_excluded a [7,3,5,6,8] (by decide)
    (fin9_cases _
      node_1762
      node_1763
      node_1764
      (invalid_excluded a [7,3,5,6,8,3] (by decide +kernel))
      node_1768
      (invalid_excluded a [7,3,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,8,8] (by decide +kernel)))

theorem node_1747 : Excluded a [7,3,5,6] :=
  branch_excluded a [7,3,5,6] (by decide)
    (fin9_cases _
      node_1748
      node_1749
      node_1760
      (invalid_excluded a [7,3,5,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,6,7] (by decide +kernel))
      node_1761)

theorem node_1770 : Excluded a [7,3,5,8,0] :=
  source_excluded a [7,3,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1772 : Excluded a [7,3,5,8,1,0] :=
  source_excluded a [7,3,5,8,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_1773 : Excluded a [7,3,5,8,1,2] :=
  predecessor_excluded a [7,3,5,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1775 : Excluded a [7,3,5,8,1,4,0] :=
  source_excluded a [7,3,5,8,1,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1777 : Excluded a [7,3,5,8,1,4,2,0] :=
  predecessor_excluded a [7,3,5,8,1,4,2,0] 1 0 6 7 (by decide) (by decide +kernel)

def b_1779 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | 4 => 1
  | 5 => 4
  | 6 => 2
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_1779 : LosingRegion (edgeOf a b_1779) 0 :=
  losingMask a b_1779 0 1210107572054764549080064
    (by decide +kernel) (by decide +kernel)

theorem node_1779 : Excluded a [7,3,5,8,1,4,2,6,0] :=
  losing_excluded a [7,3,5,8,1,4,2,6,0] (by decide) b_1779 (by decide +kernel) 1 0 6 cert_1779 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1779 1 0 ∧ 6 ≠ 1 ∧ maskRegion 1210107572054764549080064 1 6; decide +kernel)

theorem node_1778 : Excluded a [7,3,5,8,1,4,2,6] :=
  branch_excluded a [7,3,5,8,1,4,2,6] (by decide)
    (fin9_cases _
      node_1779
      (invalid_excluded a [7,3,5,8,1,4,2,6,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,6,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,6,8] (by decide +kernel)))

theorem node_1776 : Excluded a [7,3,5,8,1,4,2] :=
  branch_excluded a [7,3,5,8,1,4,2] (by decide)
    (fin9_cases _
      node_1777
      (invalid_excluded a [7,3,5,8,1,4,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,5] (by decide +kernel))
      node_1778
      (invalid_excluded a [7,3,5,8,1,4,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,2,8] (by decide +kernel)))

theorem node_1774 : Excluded a [7,3,5,8,1,4] :=
  branch_excluded a [7,3,5,8,1,4] (by decide)
    (fin9_cases _
      node_1775
      (invalid_excluded a [7,3,5,8,1,4,1] (by decide +kernel))
      node_1776
      (invalid_excluded a [7,3,5,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,4,8] (by decide +kernel)))

theorem node_1771 : Excluded a [7,3,5,8,1] :=
  branch_excluded a [7,3,5,8,1] (by decide)
    (fin9_cases _
      node_1772
      (invalid_excluded a [7,3,5,8,1,1] (by decide +kernel))
      node_1773
      (invalid_excluded a [7,3,5,8,1,3] (by decide +kernel))
      node_1774
      (invalid_excluded a [7,3,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,8] (by decide +kernel)))

theorem node_1780 : Excluded a [7,3,5,8,2] :=
  source_excluded a [7,3,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1781 : Excluded a [7,3,5,8,6] :=
  source_excluded a [7,3,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1769 : Excluded a [7,3,5,8] :=
  branch_excluded a [7,3,5,8] (by decide)
    (fin9_cases _
      node_1770
      node_1771
      node_1780
      (invalid_excluded a [7,3,5,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,5] (by decide +kernel))
      node_1781
      (invalid_excluded a [7,3,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,8] (by decide +kernel)))

theorem node_1729 : Excluded a [7,3,5] :=
  branch_excluded a [7,3,5] (by decide)
    (fin9_cases _
      node_1730
      node_1731
      node_1746
      (invalid_excluded a [7,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,5] (by decide +kernel))
      node_1747
      (invalid_excluded a [7,3,5,7] (by decide +kernel))
      node_1769)

theorem node_1782 : Excluded a [7,3,6] :=
  predecessor_excluded a [7,3,6] 1 7 2 0 (by decide) (by decide +kernel)

theorem node_1784 : Excluded a [7,3,8,0] :=
  predecessor_excluded a [7,3,8,0] 4 0 1 3 (by decide) (by decide +kernel)

theorem node_1789 : Excluded a [7,3,8,1,0,2,4,5] :=
  predecessor_excluded a [7,3,8,1,0,2,4,5] 0 5 6 7 (by decide) (by decide +kernel)

def b_1791 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 8
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_1791 : LosingRegion (edgeOf a b_1791) 0 :=
  losingMask a b_1791 0 1259784791259908328653824
    (by decide +kernel) (by decide +kernel)

theorem node_1791 : Excluded a [7,3,8,1,0,2,4,6,5] :=
  losing_excluded a [7,3,8,1,0,2,4,6,5] (by decide) b_1791 (by decide +kernel) 5 0 1 cert_1791 (by change 5 ≠ 0 ∧ ¬ edgeOf a b_1791 5 0 ∧ 1 ≠ 5 ∧ maskRegion 1259784791259908328653824 5 1; decide +kernel)

theorem node_1790 : Excluded a [7,3,8,1,0,2,4,6] :=
  branch_excluded a [7,3,8,1,0,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,2,4,6,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,6,4] (by decide +kernel))
      node_1791
      (invalid_excluded a [7,3,8,1,0,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,6,8] (by decide +kernel)))

theorem node_1788 : Excluded a [7,3,8,1,0,2,4] :=
  branch_excluded a [7,3,8,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,4] (by decide +kernel))
      node_1789
      node_1790
      (invalid_excluded a [7,3,8,1,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,4,8] (by decide +kernel)))

def b_1794 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 8
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 5
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_1794 : LosingRegion (edgeOf a b_1794) 0 :=
  losingMask a b_1794 0 1257405215458332813296640
    (by decide +kernel) (by decide +kernel)

theorem node_1794 : Excluded a [7,3,8,1,0,2,5,4,6] :=
  losing_excluded a [7,3,8,1,0,2,5,4,6] (by decide) b_1794 (by decide +kernel) 5 0 1 cert_1794 (by change 5 ≠ 0 ∧ ¬ edgeOf a b_1794 5 0 ∧ 1 ≠ 5 ∧ maskRegion 1257405215458332813296640 5 1; decide +kernel)

theorem node_1793 : Excluded a [7,3,8,1,0,2,5,4] :=
  branch_excluded a [7,3,8,1,0,2,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,2,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,4,1] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,4,5] (by decide +kernel))
      node_1794
      (invalid_excluded a [7,3,8,1,0,2,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,4,8] (by decide +kernel)))

theorem node_1795 : Excluded a [7,3,8,1,0,2,5,6] :=
  predecessor_excluded a [7,3,8,1,0,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1792 : Excluded a [7,3,8,1,0,2,5] :=
  branch_excluded a [7,3,8,1,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,2,5,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,1] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,3] (by decide +kernel))
      node_1793
      (invalid_excluded a [7,3,8,1,0,2,5,5] (by decide +kernel))
      node_1795
      (invalid_excluded a [7,3,8,1,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,5,8] (by decide +kernel)))

theorem node_1787 : Excluded a [7,3,8,1,0,2] :=
  branch_excluded a [7,3,8,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,3] (by decide +kernel))
      node_1788
      node_1792
      (invalid_excluded a [7,3,8,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,2,8] (by decide +kernel)))

theorem node_1797 : Excluded a [7,3,8,1,0,4,2] :=
  predecessor_excluded a [7,3,8,1,0,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1798 : Excluded a [7,3,8,1,0,4,5] :=
  predecessor_excluded a [7,3,8,1,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1796 : Excluded a [7,3,8,1,0,4] :=
  branch_excluded a [7,3,8,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,4,1] (by decide +kernel))
      node_1797
      (invalid_excluded a [7,3,8,1,0,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,4,4] (by decide +kernel))
      node_1798
      (invalid_excluded a [7,3,8,1,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,4,8] (by decide +kernel)))

theorem node_1786 : Excluded a [7,3,8,1,0] :=
  branch_excluded a [7,3,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,1] (by decide +kernel))
      node_1787
      (invalid_excluded a [7,3,8,1,0,3] (by decide +kernel))
      node_1796
      (invalid_excluded a [7,3,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,0,8] (by decide +kernel)))

theorem node_1799 : Excluded a [7,3,8,1,2] :=
  predecessor_excluded a [7,3,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1800 : Excluded a [7,3,8,1,6] :=
  source_excluded a [7,3,8,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1785 : Excluded a [7,3,8,1] :=
  branch_excluded a [7,3,8,1] (by decide)
    (fin9_cases _
      node_1786
      (invalid_excluded a [7,3,8,1,1] (by decide +kernel))
      node_1799
      (invalid_excluded a [7,3,8,1,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,5] (by decide +kernel))
      node_1800
      (invalid_excluded a [7,3,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,1,8] (by decide +kernel)))

theorem node_1801 : Excluded a [7,3,8,2] :=
  source_excluded a [7,3,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1802 : Excluded a [7,3,8,5] :=
  source_excluded a [7,3,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1805 : Excluded a [7,3,8,6,0,1] :=
  predecessor_excluded a [7,3,8,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1807 : Excluded a [7,3,8,6,0,2,1] :=
  source_excluded a [7,3,8,6,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1808 : Excluded a [7,3,8,6,0,2,4] :=
  source_excluded a [7,3,8,6,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1809 : Excluded a [7,3,8,6,0,2,5] :=
  predecessor_excluded a [7,3,8,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1806 : Excluded a [7,3,8,6,0,2] :=
  branch_excluded a [7,3,8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,2,0] (by decide +kernel))
      node_1807
      (invalid_excluded a [7,3,8,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,3] (by decide +kernel))
      node_1808
      node_1809
      (invalid_excluded a [7,3,8,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,8] (by decide +kernel)))

theorem node_1810 : Excluded a [7,3,8,6,0,4] :=
  source_excluded a [7,3,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1804 : Excluded a [7,3,8,6,0] :=
  branch_excluded a [7,3,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,0] (by decide +kernel))
      node_1805
      node_1806
      (invalid_excluded a [7,3,8,6,0,3] (by decide +kernel))
      node_1810
      (invalid_excluded a [7,3,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,8] (by decide +kernel)))

theorem node_1812 : Excluded a [7,3,8,6,1,0] :=
  predecessor_excluded a [7,3,8,6,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1813 : Excluded a [7,3,8,6,1,2] :=
  predecessor_excluded a [7,3,8,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1814 : Excluded a [7,3,8,6,1,4] :=
  source_excluded a [7,3,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1811 : Excluded a [7,3,8,6,1] :=
  branch_excluded a [7,3,8,6,1] (by decide)
    (fin9_cases _
      node_1812
      (invalid_excluded a [7,3,8,6,1,1] (by decide +kernel))
      node_1813
      (invalid_excluded a [7,3,8,6,1,3] (by decide +kernel))
      node_1814
      (invalid_excluded a [7,3,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,8] (by decide +kernel)))

theorem node_1816 : Excluded a [7,3,8,6,2,0] :=
  predecessor_excluded a [7,3,8,6,2,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1818 : Excluded a [7,3,8,6,2,1,0] :=
  source_excluded a [7,3,8,6,2,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1819 : Excluded a [7,3,8,6,2,1,4] :=
  source_excluded a [7,3,8,6,2,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1820 : Excluded a [7,3,8,6,2,1,5] :=
  predecessor_excluded a [7,3,8,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1817 : Excluded a [7,3,8,6,2,1] :=
  branch_excluded a [7,3,8,6,2,1] (by decide)
    (fin9_cases _
      node_1818
      (invalid_excluded a [7,3,8,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,1,3] (by decide +kernel))
      node_1819
      node_1820
      (invalid_excluded a [7,3,8,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,1,8] (by decide +kernel)))

theorem node_1821 : Excluded a [7,3,8,6,2,4] :=
  source_excluded a [7,3,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1815 : Excluded a [7,3,8,6,2] :=
  branch_excluded a [7,3,8,6,2] (by decide)
    (fin9_cases _
      node_1816
      node_1817
      (invalid_excluded a [7,3,8,6,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,3] (by decide +kernel))
      node_1821
      (invalid_excluded a [7,3,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,8] (by decide +kernel)))

theorem node_1803 : Excluded a [7,3,8,6] :=
  branch_excluded a [7,3,8,6] (by decide)
    (fin9_cases _
      node_1804
      node_1811
      node_1815
      (invalid_excluded a [7,3,8,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,8] (by decide +kernel)))

theorem node_1783 : Excluded a [7,3,8] :=
  branch_excluded a [7,3,8] (by decide)
    (fin9_cases _
      node_1784
      node_1785
      node_1801
      (invalid_excluded a [7,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,4] (by decide +kernel))
      node_1802
      node_1803
      (invalid_excluded a [7,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,8] (by decide +kernel)))

theorem node_1726 : Excluded a [7,3] :=
  branch_excluded a [7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,0] (by decide +kernel))
      node_1727
      (invalid_excluded a [7,3,2] (by decide +kernel))
      (invalid_excluded a [7,3,3] (by decide +kernel))
      node_1728
      node_1729
      node_1782
      (invalid_excluded a [7,3,7] (by decide +kernel))
      node_1783)

theorem node_1823 : Excluded a [7,4,1] :=
  source_excluded a [7,4,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1825 : Excluded a [7,4,3,0] :=
  source_excluded a [7,4,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1826 : Excluded a [7,4,3,1] :=
  source_excluded a [7,4,3,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1827 : Excluded a [7,4,3,2] :=
  source_excluded a [7,4,3,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1828 : Excluded a [7,4,3,5] :=
  source_excluded a [7,4,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1830 : Excluded a [7,4,3,6,0] :=
  predecessor_excluded a [7,4,3,6,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1832 : Excluded a [7,4,3,6,1,0] :=
  predecessor_excluded a [7,4,3,6,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1833 : Excluded a [7,4,3,6,1,2] :=
  predecessor_excluded a [7,4,3,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1835 : Excluded a [7,4,3,6,1,8,0] :=
  source_excluded a [7,4,3,6,1,8,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1837 : Excluded a [7,4,3,6,1,8,2,0] :=
  predecessor_excluded a [7,4,3,6,1,8,2,0] 1 0 6 7 (by decide) (by decide +kernel)

theorem node_1838 : Excluded a [7,4,3,6,1,8,2,5] :=
  source_excluded a [7,4,3,6,1,8,2,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_1836 : Excluded a [7,4,3,6,1,8,2] :=
  branch_excluded a [7,4,3,6,1,8,2] (by decide)
    (fin9_cases _
      node_1837
      (invalid_excluded a [7,4,3,6,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,8,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,8,2,4] (by decide +kernel))
      node_1838
      (invalid_excluded a [7,4,3,6,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,8,2,8] (by decide +kernel)))

theorem node_1839 : Excluded a [7,4,3,6,1,8,5] :=
  predecessor_excluded a [7,4,3,6,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1834 : Excluded a [7,4,3,6,1,8] :=
  branch_excluded a [7,4,3,6,1,8] (by decide)
    (fin9_cases _
      node_1835
      (invalid_excluded a [7,4,3,6,1,8,1] (by decide +kernel))
      node_1836
      (invalid_excluded a [7,4,3,6,1,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,8,4] (by decide +kernel))
      node_1839
      (invalid_excluded a [7,4,3,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,8,8] (by decide +kernel)))

theorem node_1831 : Excluded a [7,4,3,6,1] :=
  branch_excluded a [7,4,3,6,1] (by decide)
    (fin9_cases _
      node_1832
      (invalid_excluded a [7,4,3,6,1,1] (by decide +kernel))
      node_1833
      (invalid_excluded a [7,4,3,6,1,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,1,7] (by decide +kernel))
      node_1834)

theorem node_1840 : Excluded a [7,4,3,6,2] :=
  source_excluded a [7,4,3,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1842 : Excluded a [7,4,3,6,8,0] :=
  predecessor_excluded a [7,4,3,6,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1844 : Excluded a [7,4,3,6,8,1,0] :=
  source_excluded a [7,4,3,6,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1845 : Excluded a [7,4,3,6,8,1,2] :=
  predecessor_excluded a [7,4,3,6,8,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1846 : Excluded a [7,4,3,6,8,1,5] :=
  predecessor_excluded a [7,4,3,6,8,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1843 : Excluded a [7,4,3,6,8,1] :=
  branch_excluded a [7,4,3,6,8,1] (by decide)
    (fin9_cases _
      node_1844
      (invalid_excluded a [7,4,3,6,8,1,1] (by decide +kernel))
      node_1845
      (invalid_excluded a [7,4,3,6,8,1,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,1,4] (by decide +kernel))
      node_1846
      (invalid_excluded a [7,4,3,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,1,8] (by decide +kernel)))

theorem node_1848 : Excluded a [7,4,3,6,8,2,0] :=
  source_excluded a [7,4,3,6,8,2,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1849 : Excluded a [7,4,3,6,8,2,1] :=
  source_excluded a [7,4,3,6,8,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1850 : Excluded a [7,4,3,6,8,2,5] :=
  predecessor_excluded a [7,4,3,6,8,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1847 : Excluded a [7,4,3,6,8,2] :=
  branch_excluded a [7,4,3,6,8,2] (by decide)
    (fin9_cases _
      node_1848
      node_1849
      (invalid_excluded a [7,4,3,6,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,2,4] (by decide +kernel))
      node_1850
      (invalid_excluded a [7,4,3,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,2,8] (by decide +kernel)))

theorem node_1841 : Excluded a [7,4,3,6,8] :=
  branch_excluded a [7,4,3,6,8] (by decide)
    (fin9_cases _
      node_1842
      node_1843
      node_1847
      (invalid_excluded a [7,4,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,8,8] (by decide +kernel)))

theorem node_1829 : Excluded a [7,4,3,6] :=
  branch_excluded a [7,4,3,6] (by decide)
    (fin9_cases _
      node_1830
      node_1831
      node_1840
      (invalid_excluded a [7,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,6,7] (by decide +kernel))
      node_1841)

theorem node_1852 : Excluded a [7,4,3,8,0] :=
  predecessor_excluded a [7,4,3,8,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1854 : Excluded a [7,4,3,8,1,0] :=
  predecessor_excluded a [7,4,3,8,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1855 : Excluded a [7,4,3,8,1,2] :=
  predecessor_excluded a [7,4,3,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1853 : Excluded a [7,4,3,8,1] :=
  branch_excluded a [7,4,3,8,1] (by decide)
    (fin9_cases _
      node_1854
      (invalid_excluded a [7,4,3,8,1,1] (by decide +kernel))
      node_1855
      (invalid_excluded a [7,4,3,8,1,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,1,8] (by decide +kernel)))

theorem node_1856 : Excluded a [7,4,3,8,2] :=
  source_excluded a [7,4,3,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1857 : Excluded a [7,4,3,8,6] :=
  source_excluded a [7,4,3,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1851 : Excluded a [7,4,3,8] :=
  branch_excluded a [7,4,3,8] (by decide)
    (fin9_cases _
      node_1852
      node_1853
      node_1856
      (invalid_excluded a [7,4,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,5] (by decide +kernel))
      node_1857
      (invalid_excluded a [7,4,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,3,8,8] (by decide +kernel)))

theorem node_1824 : Excluded a [7,4,3] :=
  branch_excluded a [7,4,3] (by decide)
    (fin9_cases _
      node_1825
      node_1826
      node_1827
      (invalid_excluded a [7,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,3,4] (by decide +kernel))
      node_1828
      node_1829
      (invalid_excluded a [7,4,3,7] (by decide +kernel))
      node_1851)

theorem node_1858 : Excluded a [7,4,5] :=
  predecessor_excluded a [7,4,5] 0 5 1 2 (by decide) (by decide +kernel)

theorem node_1859 : Excluded a [7,4,6] :=
  predecessor_excluded a [7,4,6] 1 7 2 0 (by decide) (by decide +kernel)

theorem node_1862 : Excluded a [7,4,8,0,1] :=
  predecessor_excluded a [7,4,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1863 : Excluded a [7,4,8,0,2] :=
  source_excluded a [7,4,8,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1866 : Excluded a [7,4,8,0,3,1,2] :=
  predecessor_excluded a [7,4,8,0,3,1,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1868 : Excluded a [7,4,8,0,3,1,5,2] :=
  source_excluded a [7,4,8,0,3,1,5,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_1869 : Excluded a [7,4,8,0,3,1,5,6] :=
  predecessor_excluded a [7,4,8,0,3,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1867 : Excluded a [7,4,8,0,3,1,5] :=
  branch_excluded a [7,4,8,0,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,0,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,1,5,1] (by decide +kernel))
      node_1868
      (invalid_excluded a [7,4,8,0,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,1,5,5] (by decide +kernel))
      node_1869
      (invalid_excluded a [7,4,8,0,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,1,5,8] (by decide +kernel)))

theorem node_1865 : Excluded a [7,4,8,0,3,1] :=
  branch_excluded a [7,4,8,0,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,0,3,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,1,1] (by decide +kernel))
      node_1866
      (invalid_excluded a [7,4,8,0,3,1,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,1,4] (by decide +kernel))
      node_1867
      (invalid_excluded a [7,4,8,0,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,1,8] (by decide +kernel)))

theorem node_1871 : Excluded a [7,4,8,0,3,2,1] :=
  source_excluded a [7,4,8,0,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1873 : Excluded a [7,4,8,0,3,2,5,1] :=
  source_excluded a [7,4,8,0,3,2,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_1874 : Excluded a [7,4,8,0,3,2,5,6] :=
  predecessor_excluded a [7,4,8,0,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1872 : Excluded a [7,4,8,0,3,2,5] :=
  branch_excluded a [7,4,8,0,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,0,3,2,5,0] (by decide +kernel))
      node_1873
      (invalid_excluded a [7,4,8,0,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,2,5,5] (by decide +kernel))
      node_1874
      (invalid_excluded a [7,4,8,0,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,2,5,8] (by decide +kernel)))

theorem node_1870 : Excluded a [7,4,8,0,3,2] :=
  branch_excluded a [7,4,8,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,0,3,2,0] (by decide +kernel))
      node_1871
      (invalid_excluded a [7,4,8,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,2,4] (by decide +kernel))
      node_1872
      (invalid_excluded a [7,4,8,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,2,8] (by decide +kernel)))

theorem node_1864 : Excluded a [7,4,8,0,3] :=
  branch_excluded a [7,4,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,0,3,0] (by decide +kernel))
      node_1865
      node_1870
      (invalid_excluded a [7,4,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,3,8] (by decide +kernel)))

theorem node_1875 : Excluded a [7,4,8,0,6] :=
  source_excluded a [7,4,8,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1861 : Excluded a [7,4,8,0] :=
  branch_excluded a [7,4,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,0,0] (by decide +kernel))
      node_1862
      node_1863
      node_1864
      (invalid_excluded a [7,4,8,0,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,5] (by decide +kernel))
      node_1875
      (invalid_excluded a [7,4,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,0,8] (by decide +kernel)))

theorem node_1876 : Excluded a [7,4,8,1] :=
  source_excluded a [7,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1877 : Excluded a [7,4,8,2] :=
  source_excluded a [7,4,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1878 : Excluded a [7,4,8,5] :=
  source_excluded a [7,4,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1880 : Excluded a [7,4,8,6,0] :=
  predecessor_excluded a [7,4,8,6,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_1882 : Excluded a [7,4,8,6,1,0] :=
  predecessor_excluded a [7,4,8,6,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1883 : Excluded a [7,4,8,6,1,2] :=
  predecessor_excluded a [7,4,8,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1884 : Excluded a [7,4,8,6,1,3] :=
  source_excluded a [7,4,8,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1881 : Excluded a [7,4,8,6,1] :=
  branch_excluded a [7,4,8,6,1] (by decide)
    (fin9_cases _
      node_1882
      (invalid_excluded a [7,4,8,6,1,1] (by decide +kernel))
      node_1883
      node_1884
      (invalid_excluded a [7,4,8,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,8] (by decide +kernel)))

theorem node_1885 : Excluded a [7,4,8,6,2] :=
  source_excluded a [7,4,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1886 : Excluded a [7,4,8,6,3] :=
  predecessor_excluded a [7,4,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1879 : Excluded a [7,4,8,6] :=
  branch_excluded a [7,4,8,6] (by decide)
    (fin9_cases _
      node_1880
      node_1881
      node_1885
      node_1886
      (invalid_excluded a [7,4,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,8] (by decide +kernel)))

theorem node_1860 : Excluded a [7,4,8] :=
  branch_excluded a [7,4,8] (by decide)
    (fin9_cases _
      node_1861
      node_1876
      node_1877
      (invalid_excluded a [7,4,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,4] (by decide +kernel))
      node_1878
      node_1879
      (invalid_excluded a [7,4,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,8] (by decide +kernel)))

theorem node_1822 : Excluded a [7,4] :=
  branch_excluded a [7,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0] (by decide +kernel))
      node_1823
      (invalid_excluded a [7,4,2] (by decide +kernel))
      node_1824
      (invalid_excluded a [7,4,4] (by decide +kernel))
      node_1858
      node_1859
      (invalid_excluded a [7,4,7] (by decide +kernel))
      node_1860)

theorem node_1888 : Excluded a [7,5,1] :=
  source_excluded a [7,5,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_1890 : Excluded a [7,5,3,0] :=
  source_excluded a [7,5,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1891 : Excluded a [7,5,3,1] :=
  predecessor_excluded a [7,5,3,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1893 : Excluded a [7,5,3,2,0] :=
  predecessor_excluded a [7,5,3,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1894 : Excluded a [7,5,3,2,1] :=
  source_excluded a [7,5,3,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1895 : Excluded a [7,5,3,2,6] :=
  source_excluded a [7,5,3,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1897 : Excluded a [7,5,3,2,8,0] :=
  predecessor_excluded a [7,5,3,2,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1899 : Excluded a [7,5,3,2,8,1,0] :=
  source_excluded a [7,5,3,2,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1900 : Excluded a [7,5,3,2,8,1,4] :=
  predecessor_excluded a [7,5,3,2,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1898 : Excluded a [7,5,3,2,8,1] :=
  branch_excluded a [7,5,3,2,8,1] (by decide)
    (fin9_cases _
      node_1899
      (invalid_excluded a [7,5,3,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,1,2] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,1,3] (by decide +kernel))
      node_1900
      (invalid_excluded a [7,5,3,2,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,1,8] (by decide +kernel)))

theorem node_1902 : Excluded a [7,5,3,2,8,4,0] :=
  source_excluded a [7,5,3,2,8,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1903 : Excluded a [7,5,3,2,8,4,1] :=
  source_excluded a [7,5,3,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1901 : Excluded a [7,5,3,2,8,4] :=
  branch_excluded a [7,5,3,2,8,4] (by decide)
    (fin9_cases _
      node_1902
      node_1903
      (invalid_excluded a [7,5,3,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,4,8] (by decide +kernel)))

theorem node_1896 : Excluded a [7,5,3,2,8] :=
  branch_excluded a [7,5,3,2,8] (by decide)
    (fin9_cases _
      node_1897
      node_1898
      (invalid_excluded a [7,5,3,2,8,2] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,3] (by decide +kernel))
      node_1901
      (invalid_excluded a [7,5,3,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,8,8] (by decide +kernel)))

theorem node_1892 : Excluded a [7,5,3,2] :=
  branch_excluded a [7,5,3,2] (by decide)
    (fin9_cases _
      node_1893
      node_1894
      (invalid_excluded a [7,5,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,3] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,3,2,5] (by decide +kernel))
      node_1895
      (invalid_excluded a [7,5,3,2,7] (by decide +kernel))
      node_1896)

theorem node_1906 : Excluded a [7,5,3,6,0,1] :=
  predecessor_excluded a [7,5,3,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1907 : Excluded a [7,5,3,6,0,2] :=
  source_excluded a [7,5,3,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1908 : Excluded a [7,5,3,6,0,4] :=
  source_excluded a [7,5,3,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1910 : Excluded a [7,5,3,6,0,8,1] :=
  source_excluded a [7,5,3,6,0,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1912 : Excluded a [7,5,3,6,0,8,2,1] :=
  source_excluded a [7,5,3,6,0,8,2,1] 0 2 7 (by decide) (by decide +kernel)

def b_1914 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 5
  | 2 => 3
  | 3 => 6
  | 4 => 0
  | 5 => 8
  | 6 => 2
  | 7 => 4
  | 8 => 1
  | _ => 0

def cert_1914 : LosingRegion (edgeOf a b_1914) 0 :=
  losingMask a b_1914 0 1266849824856557327780864
    (by decide +kernel) (by decide +kernel)

theorem node_1914 : Excluded a [7,5,3,6,0,8,2,4,1] :=
  losing_excluded a [7,5,3,6,0,8,2,4,1] (by decide) b_1914 (by decide +kernel) 1 0 2 cert_1914 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1914 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1266849824856557327780864 1 2; decide +kernel)

theorem node_1913 : Excluded a [7,5,3,6,0,8,2,4] :=
  branch_excluded a [7,5,3,6,0,8,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,3,6,0,8,2,4,0] (by decide +kernel))
      node_1914
      (invalid_excluded a [7,5,3,6,0,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,4,8] (by decide +kernel)))

theorem node_1911 : Excluded a [7,5,3,6,0,8,2] :=
  branch_excluded a [7,5,3,6,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,3,6,0,8,2,0] (by decide +kernel))
      node_1912
      (invalid_excluded a [7,5,3,6,0,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,3] (by decide +kernel))
      node_1913
      (invalid_excluded a [7,5,3,6,0,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,2,8] (by decide +kernel)))

theorem node_1915 : Excluded a [7,5,3,6,0,8,4] :=
  source_excluded a [7,5,3,6,0,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1909 : Excluded a [7,5,3,6,0,8] :=
  branch_excluded a [7,5,3,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,3,6,0,8,0] (by decide +kernel))
      node_1910
      node_1911
      (invalid_excluded a [7,5,3,6,0,8,3] (by decide +kernel))
      node_1915
      (invalid_excluded a [7,5,3,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,8,8] (by decide +kernel)))

theorem node_1905 : Excluded a [7,5,3,6,0] :=
  branch_excluded a [7,5,3,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,3,6,0,0] (by decide +kernel))
      node_1906
      node_1907
      (invalid_excluded a [7,5,3,6,0,3] (by decide +kernel))
      node_1908
      (invalid_excluded a [7,5,3,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,0,7] (by decide +kernel))
      node_1909)

theorem node_1916 : Excluded a [7,5,3,6,1] :=
  source_excluded a [7,5,3,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1917 : Excluded a [7,5,3,6,2] :=
  source_excluded a [7,5,3,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1919 : Excluded a [7,5,3,6,8,0] :=
  predecessor_excluded a [7,5,3,6,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1921 : Excluded a [7,5,3,6,8,1,0] :=
  source_excluded a [7,5,3,6,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1922 : Excluded a [7,5,3,6,8,1,2] :=
  predecessor_excluded a [7,5,3,6,8,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1923 : Excluded a [7,5,3,6,8,1,4] :=
  source_excluded a [7,5,3,6,8,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1920 : Excluded a [7,5,3,6,8,1] :=
  branch_excluded a [7,5,3,6,8,1] (by decide)
    (fin9_cases _
      node_1921
      (invalid_excluded a [7,5,3,6,8,1,1] (by decide +kernel))
      node_1922
      (invalid_excluded a [7,5,3,6,8,1,3] (by decide +kernel))
      node_1923
      (invalid_excluded a [7,5,3,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,8,1,8] (by decide +kernel)))

theorem node_1924 : Excluded a [7,5,3,6,8,2] :=
  source_excluded a [7,5,3,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1925 : Excluded a [7,5,3,6,8,4] :=
  source_excluded a [7,5,3,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1918 : Excluded a [7,5,3,6,8] :=
  branch_excluded a [7,5,3,6,8] (by decide)
    (fin9_cases _
      node_1919
      node_1920
      node_1924
      (invalid_excluded a [7,5,3,6,8,3] (by decide +kernel))
      node_1925
      (invalid_excluded a [7,5,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,8,8] (by decide +kernel)))

theorem node_1904 : Excluded a [7,5,3,6] :=
  branch_excluded a [7,5,3,6] (by decide)
    (fin9_cases _
      node_1905
      node_1916
      node_1917
      (invalid_excluded a [7,5,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,6,7] (by decide +kernel))
      node_1918)

theorem node_1928 : Excluded a [7,5,3,8,0,1] :=
  predecessor_excluded a [7,5,3,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1929 : Excluded a [7,5,3,8,0,2] :=
  source_excluded a [7,5,3,8,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1931 : Excluded a [7,5,3,8,0,4,1] :=
  source_excluded a [7,5,3,8,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1933 : Excluded a [7,5,3,8,0,4,2,1] :=
  source_excluded a [7,5,3,8,0,4,2,1] 0 2 7 (by decide) (by decide +kernel)

def b_1935 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 5
  | 2 => 3
  | 3 => 8
  | 4 => 0
  | 5 => 4
  | 6 => 2
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_1935 : LosingRegion (edgeOf a b_1935) 3 :=
  losingMask a b_1935 3 1210107572054711935730881
    (by decide +kernel) (by decide +kernel)

theorem node_1935 : Excluded a [7,5,3,8,0,4,2,6,1] :=
  losing_excluded a [7,5,3,8,0,4,2,6,1] (by decide) b_1935 (by decide +kernel) 0 3 6 cert_1935 (by change 0 ≠ 3 ∧ ¬ edgeOf a b_1935 0 3 ∧ 6 ≠ 0 ∧ maskRegion 1210107572054711935730881 0 6; decide +kernel)

theorem node_1934 : Excluded a [7,5,3,8,0,4,2,6] :=
  branch_excluded a [7,5,3,8,0,4,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,3,8,0,4,2,6,0] (by decide +kernel))
      node_1935
      (invalid_excluded a [7,5,3,8,0,4,2,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,6,8] (by decide +kernel)))

theorem node_1932 : Excluded a [7,5,3,8,0,4,2] :=
  branch_excluded a [7,5,3,8,0,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,3,8,0,4,2,0] (by decide +kernel))
      node_1933
      (invalid_excluded a [7,5,3,8,0,4,2,2] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,3] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,5] (by decide +kernel))
      node_1934
      (invalid_excluded a [7,5,3,8,0,4,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,2,8] (by decide +kernel)))

theorem node_1930 : Excluded a [7,5,3,8,0,4] :=
  branch_excluded a [7,5,3,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,3,8,0,4,0] (by decide +kernel))
      node_1931
      node_1932
      (invalid_excluded a [7,5,3,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,4,8] (by decide +kernel)))

theorem node_1927 : Excluded a [7,5,3,8,0] :=
  branch_excluded a [7,5,3,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,3,8,0,0] (by decide +kernel))
      node_1928
      node_1929
      (invalid_excluded a [7,5,3,8,0,3] (by decide +kernel))
      node_1930
      (invalid_excluded a [7,5,3,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,0,8] (by decide +kernel)))

theorem node_1936 : Excluded a [7,5,3,8,1] :=
  source_excluded a [7,5,3,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1937 : Excluded a [7,5,3,8,2] :=
  source_excluded a [7,5,3,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1938 : Excluded a [7,5,3,8,6] :=
  source_excluded a [7,5,3,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1926 : Excluded a [7,5,3,8] :=
  branch_excluded a [7,5,3,8] (by decide)
    (fin9_cases _
      node_1927
      node_1936
      node_1937
      (invalid_excluded a [7,5,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,5] (by decide +kernel))
      node_1938
      (invalid_excluded a [7,5,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,3,8,8] (by decide +kernel)))

theorem node_1889 : Excluded a [7,5,3] :=
  branch_excluded a [7,5,3] (by decide)
    (fin9_cases _
      node_1890
      node_1891
      node_1892
      (invalid_excluded a [7,5,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,3,5] (by decide +kernel))
      node_1904
      (invalid_excluded a [7,5,3,7] (by decide +kernel))
      node_1926)

theorem node_1940 : Excluded a [7,5,4,0] :=
  source_excluded a [7,5,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_1941 : Excluded a [7,5,4,1] :=
  predecessor_excluded a [7,5,4,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1942 : Excluded a [7,5,4,2] :=
  source_excluded a [7,5,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_1944 : Excluded a [7,5,4,6,0] :=
  source_excluded a [7,5,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1945 : Excluded a [7,5,4,6,1] :=
  source_excluded a [7,5,4,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1946 : Excluded a [7,5,4,6,2] :=
  source_excluded a [7,5,4,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1947 : Excluded a [7,5,4,6,3] :=
  predecessor_excluded a [7,5,4,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1949 : Excluded a [7,5,4,6,8,0] :=
  predecessor_excluded a [7,5,4,6,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1951 : Excluded a [7,5,4,6,8,1,0] :=
  source_excluded a [7,5,4,6,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1952 : Excluded a [7,5,4,6,8,1,2] :=
  predecessor_excluded a [7,5,4,6,8,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1955 : Excluded a [7,5,4,6,8,1,3,0,2] :=
  predecessor_excluded a [7,5,4,6,8,1,3,0,2] 0 4 8 2 (by decide) (by decide +kernel)

theorem node_1954 : Excluded a [7,5,4,6,8,1,3,0] :=
  branch_excluded a [7,5,4,6,8,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,4,6,8,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,1] (by decide +kernel))
      node_1955
      (invalid_excluded a [7,5,4,6,8,1,3,0,3] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,0,8] (by decide +kernel)))

theorem node_1956 : Excluded a [7,5,4,6,8,1,3,2] :=
  predecessor_excluded a [7,5,4,6,8,1,3,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_1953 : Excluded a [7,5,4,6,8,1,3] :=
  branch_excluded a [7,5,4,6,8,1,3] (by decide)
    (fin9_cases _
      node_1954
      (invalid_excluded a [7,5,4,6,8,1,3,1] (by decide +kernel))
      node_1956
      (invalid_excluded a [7,5,4,6,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,3,8] (by decide +kernel)))

theorem node_1950 : Excluded a [7,5,4,6,8,1] :=
  branch_excluded a [7,5,4,6,8,1] (by decide)
    (fin9_cases _
      node_1951
      (invalid_excluded a [7,5,4,6,8,1,1] (by decide +kernel))
      node_1952
      node_1953
      (invalid_excluded a [7,5,4,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,1,8] (by decide +kernel)))

theorem node_1957 : Excluded a [7,5,4,6,8,2] :=
  source_excluded a [7,5,4,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1958 : Excluded a [7,5,4,6,8,3] :=
  source_excluded a [7,5,4,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1948 : Excluded a [7,5,4,6,8] :=
  branch_excluded a [7,5,4,6,8] (by decide)
    (fin9_cases _
      node_1949
      node_1950
      node_1957
      node_1958
      (invalid_excluded a [7,5,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,8,8] (by decide +kernel)))

theorem node_1943 : Excluded a [7,5,4,6] :=
  branch_excluded a [7,5,4,6] (by decide)
    (fin9_cases _
      node_1944
      node_1945
      node_1946
      node_1947
      (invalid_excluded a [7,5,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,4,6,7] (by decide +kernel))
      node_1948)

theorem node_1960 : Excluded a [7,5,4,8,0] :=
  source_excluded a [7,5,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_1961 : Excluded a [7,5,4,8,1] :=
  source_excluded a [7,5,4,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1962 : Excluded a [7,5,4,8,2] :=
  source_excluded a [7,5,4,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1963 : Excluded a [7,5,4,8,3] :=
  predecessor_excluded a [7,5,4,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1964 : Excluded a [7,5,4,8,6] :=
  source_excluded a [7,5,4,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1959 : Excluded a [7,5,4,8] :=
  branch_excluded a [7,5,4,8] (by decide)
    (fin9_cases _
      node_1960
      node_1961
      node_1962
      node_1963
      (invalid_excluded a [7,5,4,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,8,5] (by decide +kernel))
      node_1964
      (invalid_excluded a [7,5,4,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,4,8,8] (by decide +kernel)))

theorem node_1939 : Excluded a [7,5,4] :=
  branch_excluded a [7,5,4] (by decide)
    (fin9_cases _
      node_1940
      node_1941
      node_1942
      (invalid_excluded a [7,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,4,5] (by decide +kernel))
      node_1943
      (invalid_excluded a [7,5,4,7] (by decide +kernel))
      node_1959)

theorem node_1965 : Excluded a [7,5,6] :=
  predecessor_excluded a [7,5,6] 1 7 2 0 (by decide) (by decide +kernel)

theorem node_1968 : Excluded a [7,5,8,0,1] :=
  source_excluded a [7,5,8,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1969 : Excluded a [7,5,8,0,2] :=
  source_excluded a [7,5,8,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1972 : Excluded a [7,5,8,0,3,1,2] :=
  predecessor_excluded a [7,5,8,0,3,1,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1974 : Excluded a [7,5,8,0,3,1,4,2] :=
  source_excluded a [7,5,8,0,3,1,4,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_1976 : Excluded a [7,5,8,0,3,1,4,6,2] :=
  predecessor_excluded a [7,5,8,0,3,1,4,6,2] 1 0 8 3 (by decide) (by decide +kernel)

theorem node_1975 : Excluded a [7,5,8,0,3,1,4,6] :=
  branch_excluded a [7,5,8,0,3,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,3,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,6,1] (by decide +kernel))
      node_1976
      (invalid_excluded a [7,5,8,0,3,1,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,6,8] (by decide +kernel)))

theorem node_1973 : Excluded a [7,5,8,0,3,1,4] :=
  branch_excluded a [7,5,8,0,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,1] (by decide +kernel))
      node_1974
      (invalid_excluded a [7,5,8,0,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,5] (by decide +kernel))
      node_1975
      (invalid_excluded a [7,5,8,0,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,4,8] (by decide +kernel)))

theorem node_1971 : Excluded a [7,5,8,0,3,1] :=
  branch_excluded a [7,5,8,0,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,3,1,0] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,1] (by decide +kernel))
      node_1972
      (invalid_excluded a [7,5,8,0,3,1,3] (by decide +kernel))
      node_1973
      (invalid_excluded a [7,5,8,0,3,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,1,8] (by decide +kernel)))

theorem node_1977 : Excluded a [7,5,8,0,3,2] :=
  source_excluded a [7,5,8,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1978 : Excluded a [7,5,8,0,3,4] :=
  predecessor_excluded a [7,5,8,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1970 : Excluded a [7,5,8,0,3] :=
  branch_excluded a [7,5,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,3,0] (by decide +kernel))
      node_1971
      node_1977
      (invalid_excluded a [7,5,8,0,3,3] (by decide +kernel))
      node_1978
      (invalid_excluded a [7,5,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,8] (by decide +kernel)))

theorem node_1979 : Excluded a [7,5,8,0,6] :=
  source_excluded a [7,5,8,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1967 : Excluded a [7,5,8,0] :=
  branch_excluded a [7,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,0] (by decide +kernel))
      node_1968
      node_1969
      node_1970
      (invalid_excluded a [7,5,8,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,5] (by decide +kernel))
      node_1979
      (invalid_excluded a [7,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,8] (by decide +kernel)))

theorem node_1980 : Excluded a [7,5,8,1] :=
  predecessor_excluded a [7,5,8,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1982 : Excluded a [7,5,8,2,0] :=
  predecessor_excluded a [7,5,8,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_1983 : Excluded a [7,5,8,2,1] :=
  source_excluded a [7,5,8,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1985 : Excluded a [7,5,8,2,3,0] :=
  predecessor_excluded a [7,5,8,2,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_1987 : Excluded a [7,5,8,2,3,1,0] :=
  source_excluded a [7,5,8,2,3,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_1989 : Excluded a [7,5,8,2,3,1,4,0] :=
  source_excluded a [7,5,8,2,3,1,4,0] 2 1 7 (by decide) (by decide +kernel)

theorem node_1991 : Excluded a [7,5,8,2,3,1,4,6,0] :=
  source_excluded a [7,5,8,2,3,1,4,6,0] 2 1 8 (by decide) (by decide +kernel)

theorem node_1990 : Excluded a [7,5,8,2,3,1,4,6] :=
  branch_excluded a [7,5,8,2,3,1,4,6] (by decide)
    (fin9_cases _
      node_1991
      (invalid_excluded a [7,5,8,2,3,1,4,6,1] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,6,8] (by decide +kernel)))

theorem node_1988 : Excluded a [7,5,8,2,3,1,4] :=
  branch_excluded a [7,5,8,2,3,1,4] (by decide)
    (fin9_cases _
      node_1989
      (invalid_excluded a [7,5,8,2,3,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,5] (by decide +kernel))
      node_1990
      (invalid_excluded a [7,5,8,2,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,4,8] (by decide +kernel)))

theorem node_1986 : Excluded a [7,5,8,2,3,1] :=
  branch_excluded a [7,5,8,2,3,1] (by decide)
    (fin9_cases _
      node_1987
      (invalid_excluded a [7,5,8,2,3,1,1] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,3] (by decide +kernel))
      node_1988
      (invalid_excluded a [7,5,8,2,3,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,1,8] (by decide +kernel)))

theorem node_1992 : Excluded a [7,5,8,2,3,4] :=
  predecessor_excluded a [7,5,8,2,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1984 : Excluded a [7,5,8,2,3] :=
  branch_excluded a [7,5,8,2,3] (by decide)
    (fin9_cases _
      node_1985
      node_1986
      (invalid_excluded a [7,5,8,2,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,3] (by decide +kernel))
      node_1992
      (invalid_excluded a [7,5,8,2,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,3,8] (by decide +kernel)))

theorem node_1993 : Excluded a [7,5,8,2,6] :=
  source_excluded a [7,5,8,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1981 : Excluded a [7,5,8,2] :=
  branch_excluded a [7,5,8,2] (by decide)
    (fin9_cases _
      node_1982
      node_1983
      (invalid_excluded a [7,5,8,2,2] (by decide +kernel))
      node_1984
      (invalid_excluded a [7,5,8,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,5] (by decide +kernel))
      node_1993
      (invalid_excluded a [7,5,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,8] (by decide +kernel)))

theorem node_1996 : Excluded a [7,5,8,6,0,1] :=
  predecessor_excluded a [7,5,8,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_1997 : Excluded a [7,5,8,6,0,2] :=
  source_excluded a [7,5,8,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1998 : Excluded a [7,5,8,6,0,3] :=
  source_excluded a [7,5,8,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1999 : Excluded a [7,5,8,6,0,4] :=
  source_excluded a [7,5,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1995 : Excluded a [7,5,8,6,0] :=
  branch_excluded a [7,5,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,6,0,0] (by decide +kernel))
      node_1996
      node_1997
      node_1998
      node_1999
      (invalid_excluded a [7,5,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,8] (by decide +kernel)))

theorem node_2000 : Excluded a [7,5,8,6,1] :=
  source_excluded a [7,5,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2001 : Excluded a [7,5,8,6,2] :=
  source_excluded a [7,5,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2002 : Excluded a [7,5,8,6,3] :=
  predecessor_excluded a [7,5,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1994 : Excluded a [7,5,8,6] :=
  branch_excluded a [7,5,8,6] (by decide)
    (fin9_cases _
      node_1995
      node_2000
      node_2001
      node_2002
      (invalid_excluded a [7,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,8] (by decide +kernel)))

theorem node_1966 : Excluded a [7,5,8] :=
  branch_excluded a [7,5,8] (by decide)
    (fin9_cases _
      node_1967
      node_1980
      node_1981
      (invalid_excluded a [7,5,8,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,5] (by decide +kernel))
      node_1994
      (invalid_excluded a [7,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,8] (by decide +kernel)))

theorem node_1887 : Excluded a [7,5] :=
  branch_excluded a [7,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0] (by decide +kernel))
      node_1888
      (invalid_excluded a [7,5,2] (by decide +kernel))
      node_1889
      node_1939
      (invalid_excluded a [7,5,5] (by decide +kernel))
      node_1965
      (invalid_excluded a [7,5,7] (by decide +kernel))
      node_1966)

theorem node_2004 : Excluded a [7,6,1] :=
  source_excluded a [7,6,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_2006 : Excluded a [7,6,3,0] :=
  source_excluded a [7,6,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2007 : Excluded a [7,6,3,1] :=
  predecessor_excluded a [7,6,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_2009 : Excluded a [7,6,3,2,0] :=
  predecessor_excluded a [7,6,3,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2010 : Excluded a [7,6,3,2,1] :=
  predecessor_excluded a [7,6,3,2,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2012 : Excluded a [7,6,3,2,8,0] :=
  predecessor_excluded a [7,6,3,2,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2013 : Excluded a [7,6,3,2,8,1] :=
  source_excluded a [7,6,3,2,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2015 : Excluded a [7,6,3,2,8,4,0] :=
  source_excluded a [7,6,3,2,8,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2016 : Excluded a [7,6,3,2,8,4,1] :=
  source_excluded a [7,6,3,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2017 : Excluded a [7,6,3,2,8,4,5] :=
  predecessor_excluded a [7,6,3,2,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2014 : Excluded a [7,6,3,2,8,4] :=
  branch_excluded a [7,6,3,2,8,4] (by decide)
    (fin9_cases _
      node_2015
      node_2016
      (invalid_excluded a [7,6,3,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,4,4] (by decide +kernel))
      node_2017
      (invalid_excluded a [7,6,3,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,4,8] (by decide +kernel)))

theorem node_2011 : Excluded a [7,6,3,2,8] :=
  branch_excluded a [7,6,3,2,8] (by decide)
    (fin9_cases _
      node_2012
      node_2013
      (invalid_excluded a [7,6,3,2,8,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,3] (by decide +kernel))
      node_2014
      (invalid_excluded a [7,6,3,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,8,8] (by decide +kernel)))

theorem node_2008 : Excluded a [7,6,3,2] :=
  branch_excluded a [7,6,3,2] (by decide)
    (fin9_cases _
      node_2009
      node_2010
      (invalid_excluded a [7,6,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,4] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,2,7] (by decide +kernel))
      node_2011)

theorem node_2018 : Excluded a [7,6,3,5] :=
  source_excluded a [7,6,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2021 : Excluded a [7,6,3,8,0,1] :=
  source_excluded a [7,6,3,8,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2022 : Excluded a [7,6,3,8,0,2] :=
  source_excluded a [7,6,3,8,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2024 : Excluded a [7,6,3,8,0,4,1] :=
  source_excluded a [7,6,3,8,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2025 : Excluded a [7,6,3,8,0,4,2] :=
  source_excluded a [7,6,3,8,0,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2026 : Excluded a [7,6,3,8,0,4,5] :=
  predecessor_excluded a [7,6,3,8,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2023 : Excluded a [7,6,3,8,0,4] :=
  branch_excluded a [7,6,3,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,3,8,0,4,0] (by decide +kernel))
      node_2024
      node_2025
      (invalid_excluded a [7,6,3,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,0,4,4] (by decide +kernel))
      node_2026
      (invalid_excluded a [7,6,3,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,0,4,8] (by decide +kernel)))

theorem node_2020 : Excluded a [7,6,3,8,0] :=
  branch_excluded a [7,6,3,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,3,8,0,0] (by decide +kernel))
      node_2021
      node_2022
      (invalid_excluded a [7,6,3,8,0,3] (by decide +kernel))
      node_2023
      (invalid_excluded a [7,6,3,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,0,8] (by decide +kernel)))

theorem node_2027 : Excluded a [7,6,3,8,1] :=
  predecessor_excluded a [7,6,3,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2029 : Excluded a [7,6,3,8,2,0] :=
  predecessor_excluded a [7,6,3,8,2,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2030 : Excluded a [7,6,3,8,2,1] :=
  source_excluded a [7,6,3,8,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2032 : Excluded a [7,6,3,8,2,4,0] :=
  source_excluded a [7,6,3,8,2,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2033 : Excluded a [7,6,3,8,2,4,1] :=
  source_excluded a [7,6,3,8,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2034 : Excluded a [7,6,3,8,2,4,5] :=
  predecessor_excluded a [7,6,3,8,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2031 : Excluded a [7,6,3,8,2,4] :=
  branch_excluded a [7,6,3,8,2,4] (by decide)
    (fin9_cases _
      node_2032
      node_2033
      (invalid_excluded a [7,6,3,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,2,4,4] (by decide +kernel))
      node_2034
      (invalid_excluded a [7,6,3,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,2,4,8] (by decide +kernel)))

theorem node_2028 : Excluded a [7,6,3,8,2] :=
  branch_excluded a [7,6,3,8,2] (by decide)
    (fin9_cases _
      node_2029
      node_2030
      (invalid_excluded a [7,6,3,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,2,3] (by decide +kernel))
      node_2031
      (invalid_excluded a [7,6,3,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,2,8] (by decide +kernel)))

theorem node_2019 : Excluded a [7,6,3,8] :=
  branch_excluded a [7,6,3,8] (by decide)
    (fin9_cases _
      node_2020
      node_2027
      node_2028
      (invalid_excluded a [7,6,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,3,8,8] (by decide +kernel)))

theorem node_2005 : Excluded a [7,6,3] :=
  branch_excluded a [7,6,3] (by decide)
    (fin9_cases _
      node_2006
      node_2007
      node_2008
      (invalid_excluded a [7,6,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,3,4] (by decide +kernel))
      node_2018
      (invalid_excluded a [7,6,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,3,7] (by decide +kernel))
      node_2019)

theorem node_2036 : Excluded a [7,6,4,0] :=
  source_excluded a [7,6,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2038 : Excluded a [7,6,4,1,0] :=
  source_excluded a [7,6,4,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2039 : Excluded a [7,6,4,1,2] :=
  predecessor_excluded a [7,6,4,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2041 : Excluded a [7,6,4,1,3,0] :=
  predecessor_excluded a [7,6,4,1,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2042 : Excluded a [7,6,4,1,3,2] :=
  source_excluded a [7,6,4,1,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2044 : Excluded a [7,6,4,1,3,8,0] :=
  source_excluded a [7,6,4,1,3,8,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2045 : Excluded a [7,6,4,1,3,8,2] :=
  source_excluded a [7,6,4,1,3,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2046 : Excluded a [7,6,4,1,3,8,5] :=
  predecessor_excluded a [7,6,4,1,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2043 : Excluded a [7,6,4,1,3,8] :=
  branch_excluded a [7,6,4,1,3,8] (by decide)
    (fin9_cases _
      node_2044
      (invalid_excluded a [7,6,4,1,3,8,1] (by decide +kernel))
      node_2045
      (invalid_excluded a [7,6,4,1,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,3,8,4] (by decide +kernel))
      node_2046
      (invalid_excluded a [7,6,4,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,3,8,8] (by decide +kernel)))

theorem node_2040 : Excluded a [7,6,4,1,3] :=
  branch_excluded a [7,6,4,1,3] (by decide)
    (fin9_cases _
      node_2041
      (invalid_excluded a [7,6,4,1,3,1] (by decide +kernel))
      node_2042
      (invalid_excluded a [7,6,4,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,3,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,3,7] (by decide +kernel))
      node_2043)

theorem node_2048 : Excluded a [7,6,4,1,8,0] :=
  predecessor_excluded a [7,6,4,1,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2049 : Excluded a [7,6,4,1,8,2] :=
  source_excluded a [7,6,4,1,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2050 : Excluded a [7,6,4,1,8,3] :=
  predecessor_excluded a [7,6,4,1,8,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2047 : Excluded a [7,6,4,1,8] :=
  branch_excluded a [7,6,4,1,8] (by decide)
    (fin9_cases _
      node_2048
      (invalid_excluded a [7,6,4,1,8,1] (by decide +kernel))
      node_2049
      node_2050
      (invalid_excluded a [7,6,4,1,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,8,8] (by decide +kernel)))

theorem node_2037 : Excluded a [7,6,4,1] :=
  branch_excluded a [7,6,4,1] (by decide)
    (fin9_cases _
      node_2038
      (invalid_excluded a [7,6,4,1,1] (by decide +kernel))
      node_2039
      node_2040
      (invalid_excluded a [7,6,4,1,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,1,7] (by decide +kernel))
      node_2047)

theorem node_2051 : Excluded a [7,6,4,2] :=
  source_excluded a [7,6,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_2052 : Excluded a [7,6,4,5] :=
  source_excluded a [7,6,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2054 : Excluded a [7,6,4,8,0] :=
  source_excluded a [7,6,4,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2055 : Excluded a [7,6,4,8,1] :=
  predecessor_excluded a [7,6,4,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2057 : Excluded a [7,6,4,8,2,0] :=
  predecessor_excluded a [7,6,4,8,2,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2058 : Excluded a [7,6,4,8,2,1] :=
  source_excluded a [7,6,4,8,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2060 : Excluded a [7,6,4,8,2,3,0] :=
  source_excluded a [7,6,4,8,2,3,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2061 : Excluded a [7,6,4,8,2,3,1] :=
  source_excluded a [7,6,4,8,2,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2064 : Excluded a [7,6,4,8,2,3,5,0,1] :=
  predecessor_excluded a [7,6,4,8,2,3,5,0,1] 2 1 7 8 (by decide) (by decide +kernel)

theorem node_2063 : Excluded a [7,6,4,8,2,3,5,0] :=
  branch_excluded a [7,6,4,8,2,3,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,4,8,2,3,5,0,0] (by decide +kernel))
      node_2064
      (invalid_excluded a [7,6,4,8,2,3,5,0,2] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,0,3] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,0,8] (by decide +kernel)))

theorem node_2065 : Excluded a [7,6,4,8,2,3,5,1] :=
  source_excluded a [7,6,4,8,2,3,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2062 : Excluded a [7,6,4,8,2,3,5] :=
  branch_excluded a [7,6,4,8,2,3,5] (by decide)
    (fin9_cases _
      node_2063
      node_2065
      (invalid_excluded a [7,6,4,8,2,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,5,8] (by decide +kernel)))

theorem node_2059 : Excluded a [7,6,4,8,2,3] :=
  branch_excluded a [7,6,4,8,2,3] (by decide)
    (fin9_cases _
      node_2060
      node_2061
      (invalid_excluded a [7,6,4,8,2,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,4] (by decide +kernel))
      node_2062
      (invalid_excluded a [7,6,4,8,2,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,3,8] (by decide +kernel)))

theorem node_2056 : Excluded a [7,6,4,8,2] :=
  branch_excluded a [7,6,4,8,2] (by decide)
    (fin9_cases _
      node_2057
      node_2058
      (invalid_excluded a [7,6,4,8,2,2] (by decide +kernel))
      node_2059
      (invalid_excluded a [7,6,4,8,2,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,2,8] (by decide +kernel)))

theorem node_2066 : Excluded a [7,6,4,8,3] :=
  predecessor_excluded a [7,6,4,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2053 : Excluded a [7,6,4,8] :=
  branch_excluded a [7,6,4,8] (by decide)
    (fin9_cases _
      node_2054
      node_2055
      node_2056
      node_2066
      (invalid_excluded a [7,6,4,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,4,8,8] (by decide +kernel)))

theorem node_2035 : Excluded a [7,6,4] :=
  branch_excluded a [7,6,4] (by decide)
    (fin9_cases _
      node_2036
      node_2037
      node_2051
      (invalid_excluded a [7,6,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,4,4] (by decide +kernel))
      node_2052
      (invalid_excluded a [7,6,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,4,7] (by decide +kernel))
      node_2053)

theorem node_2069 : Excluded a [7,6,5,0,1] :=
  predecessor_excluded a [7,6,5,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2070 : Excluded a [7,6,5,0,2] :=
  source_excluded a [7,6,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2072 : Excluded a [7,6,5,0,3,1] :=
  source_excluded a [7,6,5,0,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2073 : Excluded a [7,6,5,0,3,2] :=
  source_excluded a [7,6,5,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2074 : Excluded a [7,6,5,0,3,4] :=
  predecessor_excluded a [7,6,5,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2076 : Excluded a [7,6,5,0,3,8,1] :=
  source_excluded a [7,6,5,0,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2077 : Excluded a [7,6,5,0,3,8,2] :=
  source_excluded a [7,6,5,0,3,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2079 : Excluded a [7,6,5,0,3,8,4,1] :=
  source_excluded a [7,6,5,0,3,8,4,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2080 : Excluded a [7,6,5,0,3,8,4,2] :=
  predecessor_excluded a [7,6,5,0,3,8,4,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2078 : Excluded a [7,6,5,0,3,8,4] :=
  branch_excluded a [7,6,5,0,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,3,8,4,0] (by decide +kernel))
      node_2079
      node_2080
      (invalid_excluded a [7,6,5,0,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,8,4,8] (by decide +kernel)))

theorem node_2075 : Excluded a [7,6,5,0,3,8] :=
  branch_excluded a [7,6,5,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,3,8,0] (by decide +kernel))
      node_2076
      node_2077
      (invalid_excluded a [7,6,5,0,3,8,3] (by decide +kernel))
      node_2078
      (invalid_excluded a [7,6,5,0,3,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,8,8] (by decide +kernel)))

theorem node_2071 : Excluded a [7,6,5,0,3] :=
  branch_excluded a [7,6,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,3,0] (by decide +kernel))
      node_2072
      node_2073
      (invalid_excluded a [7,6,5,0,3,3] (by decide +kernel))
      node_2074
      (invalid_excluded a [7,6,5,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,3,7] (by decide +kernel))
      node_2075)

theorem node_2082 : Excluded a [7,6,5,0,8,1] :=
  source_excluded a [7,6,5,0,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2083 : Excluded a [7,6,5,0,8,2] :=
  source_excluded a [7,6,5,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2084 : Excluded a [7,6,5,0,8,3] :=
  predecessor_excluded a [7,6,5,0,8,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2086 : Excluded a [7,6,5,0,8,4,1] :=
  source_excluded a [7,6,5,0,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2087 : Excluded a [7,6,5,0,8,4,2] :=
  source_excluded a [7,6,5,0,8,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2089 : Excluded a [7,6,5,0,8,4,3,1] :=
  source_excluded a [7,6,5,0,8,4,3,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2090 : Excluded a [7,6,5,0,8,4,3,2] :=
  predecessor_excluded a [7,6,5,0,8,4,3,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2088 : Excluded a [7,6,5,0,8,4,3] :=
  branch_excluded a [7,6,5,0,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,8,4,3,0] (by decide +kernel))
      node_2089
      node_2090
      (invalid_excluded a [7,6,5,0,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,4,3,8] (by decide +kernel)))

theorem node_2085 : Excluded a [7,6,5,0,8,4] :=
  branch_excluded a [7,6,5,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,8,4,0] (by decide +kernel))
      node_2086
      node_2087
      node_2088
      (invalid_excluded a [7,6,5,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,4,8] (by decide +kernel)))

theorem node_2081 : Excluded a [7,6,5,0,8] :=
  branch_excluded a [7,6,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,8,0] (by decide +kernel))
      node_2082
      node_2083
      node_2084
      node_2085
      (invalid_excluded a [7,6,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,8] (by decide +kernel)))

theorem node_2068 : Excluded a [7,6,5,0] :=
  branch_excluded a [7,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,0] (by decide +kernel))
      node_2069
      node_2070
      node_2071
      (invalid_excluded a [7,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,7] (by decide +kernel))
      node_2081)

theorem node_2092 : Excluded a [7,6,5,1,0] :=
  source_excluded a [7,6,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2093 : Excluded a [7,6,5,1,2] :=
  source_excluded a [7,6,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2095 : Excluded a [7,6,5,1,3,0] :=
  source_excluded a [7,6,5,1,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2096 : Excluded a [7,6,5,1,3,2] :=
  source_excluded a [7,6,5,1,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2097 : Excluded a [7,6,5,1,3,4] :=
  predecessor_excluded a [7,6,5,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2099 : Excluded a [7,6,5,1,3,8,0] :=
  source_excluded a [7,6,5,1,3,8,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2100 : Excluded a [7,6,5,1,3,8,2] :=
  source_excluded a [7,6,5,1,3,8,2] 1 0 6 (by decide) (by decide +kernel)

def b_2103 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 5
  | 3 => 1
  | 4 => 3
  | 5 => 8
  | 6 => 4
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_2103 : LosingRegion (edgeOf a b_2103) 0 :=
  losingMask a b_2103 0 1238444092818020906306560
    (by decide +kernel) (by decide +kernel)

theorem node_2103 : Excluded a [7,6,5,1,3,8,4,0,2] :=
  losing_excluded a [7,6,5,1,3,8,4,0,2] (by decide) b_2103 (by decide +kernel) 1 0 2 cert_2103 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2103 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1238444092818020906306560 1 2; decide +kernel)

theorem node_2102 : Excluded a [7,6,5,1,3,8,4,0] :=
  branch_excluded a [7,6,5,1,3,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,1,3,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,0,1] (by decide +kernel))
      node_2103
      (invalid_excluded a [7,6,5,1,3,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,0,8] (by decide +kernel)))

theorem node_2104 : Excluded a [7,6,5,1,3,8,4,2] :=
  predecessor_excluded a [7,6,5,1,3,8,4,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2101 : Excluded a [7,6,5,1,3,8,4] :=
  branch_excluded a [7,6,5,1,3,8,4] (by decide)
    (fin9_cases _
      node_2102
      (invalid_excluded a [7,6,5,1,3,8,4,1] (by decide +kernel))
      node_2104
      (invalid_excluded a [7,6,5,1,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,4,8] (by decide +kernel)))

theorem node_2098 : Excluded a [7,6,5,1,3,8] :=
  branch_excluded a [7,6,5,1,3,8] (by decide)
    (fin9_cases _
      node_2099
      (invalid_excluded a [7,6,5,1,3,8,1] (by decide +kernel))
      node_2100
      (invalid_excluded a [7,6,5,1,3,8,3] (by decide +kernel))
      node_2101
      (invalid_excluded a [7,6,5,1,3,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,8,8] (by decide +kernel)))

theorem node_2094 : Excluded a [7,6,5,1,3] :=
  branch_excluded a [7,6,5,1,3] (by decide)
    (fin9_cases _
      node_2095
      (invalid_excluded a [7,6,5,1,3,1] (by decide +kernel))
      node_2096
      (invalid_excluded a [7,6,5,1,3,3] (by decide +kernel))
      node_2097
      (invalid_excluded a [7,6,5,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,3,7] (by decide +kernel))
      node_2098)

theorem node_2106 : Excluded a [7,6,5,1,8,0] :=
  source_excluded a [7,6,5,1,8,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2107 : Excluded a [7,6,5,1,8,2] :=
  source_excluded a [7,6,5,1,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2108 : Excluded a [7,6,5,1,8,3] :=
  predecessor_excluded a [7,6,5,1,8,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2110 : Excluded a [7,6,5,1,8,4,0] :=
  source_excluded a [7,6,5,1,8,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2111 : Excluded a [7,6,5,1,8,4,2] :=
  source_excluded a [7,6,5,1,8,4,2] 1 0 6 (by decide) (by decide +kernel)

def b_2114 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 5
  | 3 => 1
  | 4 => 8
  | 5 => 4
  | 6 => 3
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_2114 : LosingRegion (edgeOf a b_2114) 0 :=
  losingMask a b_2114 0 1238444095067621696736256
    (by decide +kernel) (by decide +kernel)

theorem node_2114 : Excluded a [7,6,5,1,8,4,3,0,2] :=
  losing_excluded a [7,6,5,1,8,4,3,0,2] (by decide) b_2114 (by decide +kernel) 1 0 2 cert_2114 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2114 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1238444095067621696736256 1 2; decide +kernel)

theorem node_2113 : Excluded a [7,6,5,1,8,4,3,0] :=
  branch_excluded a [7,6,5,1,8,4,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,1,8,4,3,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,0,1] (by decide +kernel))
      node_2114
      (invalid_excluded a [7,6,5,1,8,4,3,0,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,0,8] (by decide +kernel)))

theorem node_2115 : Excluded a [7,6,5,1,8,4,3,2] :=
  predecessor_excluded a [7,6,5,1,8,4,3,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2112 : Excluded a [7,6,5,1,8,4,3] :=
  branch_excluded a [7,6,5,1,8,4,3] (by decide)
    (fin9_cases _
      node_2113
      (invalid_excluded a [7,6,5,1,8,4,3,1] (by decide +kernel))
      node_2115
      (invalid_excluded a [7,6,5,1,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,3,8] (by decide +kernel)))

theorem node_2109 : Excluded a [7,6,5,1,8,4] :=
  branch_excluded a [7,6,5,1,8,4] (by decide)
    (fin9_cases _
      node_2110
      (invalid_excluded a [7,6,5,1,8,4,1] (by decide +kernel))
      node_2111
      node_2112
      (invalid_excluded a [7,6,5,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,4,8] (by decide +kernel)))

theorem node_2105 : Excluded a [7,6,5,1,8] :=
  branch_excluded a [7,6,5,1,8] (by decide)
    (fin9_cases _
      node_2106
      (invalid_excluded a [7,6,5,1,8,1] (by decide +kernel))
      node_2107
      node_2108
      node_2109
      (invalid_excluded a [7,6,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,8] (by decide +kernel)))

theorem node_2091 : Excluded a [7,6,5,1] :=
  branch_excluded a [7,6,5,1] (by decide)
    (fin9_cases _
      node_2092
      (invalid_excluded a [7,6,5,1,1] (by decide +kernel))
      node_2093
      node_2094
      (invalid_excluded a [7,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,7] (by decide +kernel))
      node_2105)

theorem node_2116 : Excluded a [7,6,5,2] :=
  predecessor_excluded a [7,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2118 : Excluded a [7,6,5,8,0] :=
  source_excluded a [7,6,5,8,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2119 : Excluded a [7,6,5,8,1] :=
  predecessor_excluded a [7,6,5,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2120 : Excluded a [7,6,5,8,2] :=
  source_excluded a [7,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2121 : Excluded a [7,6,5,8,3] :=
  predecessor_excluded a [7,6,5,8,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2117 : Excluded a [7,6,5,8] :=
  branch_excluded a [7,6,5,8] (by decide)
    (fin9_cases _
      node_2118
      node_2119
      node_2120
      node_2121
      (invalid_excluded a [7,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,8] (by decide +kernel)))

theorem node_2067 : Excluded a [7,6,5] :=
  branch_excluded a [7,6,5] (by decide)
    (fin9_cases _
      node_2068
      node_2091
      node_2116
      (invalid_excluded a [7,6,5,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,7] (by decide +kernel))
      node_2117)

theorem node_2124 : Excluded a [7,6,8,0,1] :=
  predecessor_excluded a [7,6,8,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2126 : Excluded a [7,6,8,0,2,1] :=
  source_excluded a [7,6,8,0,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2128 : Excluded a [7,6,8,0,2,3,1] :=
  source_excluded a [7,6,8,0,2,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2129 : Excluded a [7,6,8,0,2,3,4] :=
  predecessor_excluded a [7,6,8,0,2,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2131 : Excluded a [7,6,8,0,2,3,5,1] :=
  source_excluded a [7,6,8,0,2,3,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2133 : Excluded a [7,6,8,0,2,3,5,4,1] :=
  predecessor_excluded a [7,6,8,0,2,3,5,4,1] 3 1 2 8 (by decide) (by decide +kernel)

theorem node_2132 : Excluded a [7,6,8,0,2,3,5,4] :=
  branch_excluded a [7,6,8,0,2,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,3,5,4,0] (by decide +kernel))
      node_2133
      (invalid_excluded a [7,6,8,0,2,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,4,8] (by decide +kernel)))

theorem node_2130 : Excluded a [7,6,8,0,2,3,5] :=
  branch_excluded a [7,6,8,0,2,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,3,5,0] (by decide +kernel))
      node_2131
      (invalid_excluded a [7,6,8,0,2,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,3] (by decide +kernel))
      node_2132
      (invalid_excluded a [7,6,8,0,2,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,5,8] (by decide +kernel)))

theorem node_2127 : Excluded a [7,6,8,0,2,3] :=
  branch_excluded a [7,6,8,0,2,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,3,0] (by decide +kernel))
      node_2128
      (invalid_excluded a [7,6,8,0,2,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,3] (by decide +kernel))
      node_2129
      node_2130
      (invalid_excluded a [7,6,8,0,2,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,3,8] (by decide +kernel)))

theorem node_2135 : Excluded a [7,6,8,0,2,4,1] :=
  source_excluded a [7,6,8,0,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2137 : Excluded a [7,6,8,0,2,4,3,1] :=
  source_excluded a [7,6,8,0,2,4,3,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2139 : Excluded a [7,6,8,0,2,4,3,5,1] :=
  predecessor_excluded a [7,6,8,0,2,4,3,5,1] 3 1 2 8 (by decide) (by decide +kernel)

theorem node_2138 : Excluded a [7,6,8,0,2,4,3,5] :=
  branch_excluded a [7,6,8,0,2,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,4,3,5,0] (by decide +kernel))
      node_2139
      (invalid_excluded a [7,6,8,0,2,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,5,8] (by decide +kernel)))

theorem node_2136 : Excluded a [7,6,8,0,2,4,3] :=
  branch_excluded a [7,6,8,0,2,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,4,3,0] (by decide +kernel))
      node_2137
      (invalid_excluded a [7,6,8,0,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,4] (by decide +kernel))
      node_2138
      (invalid_excluded a [7,6,8,0,2,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,3,8] (by decide +kernel)))

theorem node_2140 : Excluded a [7,6,8,0,2,4,5] :=
  predecessor_excluded a [7,6,8,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2134 : Excluded a [7,6,8,0,2,4] :=
  branch_excluded a [7,6,8,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,4,0] (by decide +kernel))
      node_2135
      (invalid_excluded a [7,6,8,0,2,4,2] (by decide +kernel))
      node_2136
      (invalid_excluded a [7,6,8,0,2,4,4] (by decide +kernel))
      node_2140
      (invalid_excluded a [7,6,8,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,4,8] (by decide +kernel)))

theorem node_2125 : Excluded a [7,6,8,0,2] :=
  branch_excluded a [7,6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,2,0] (by decide +kernel))
      node_2126
      (invalid_excluded a [7,6,8,0,2,2] (by decide +kernel))
      node_2127
      node_2134
      (invalid_excluded a [7,6,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,2,8] (by decide +kernel)))

theorem node_2142 : Excluded a [7,6,8,0,3,1] :=
  source_excluded a [7,6,8,0,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2143 : Excluded a [7,6,8,0,3,2] :=
  source_excluded a [7,6,8,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2144 : Excluded a [7,6,8,0,3,4] :=
  predecessor_excluded a [7,6,8,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2141 : Excluded a [7,6,8,0,3] :=
  branch_excluded a [7,6,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,3,0] (by decide +kernel))
      node_2142
      node_2143
      (invalid_excluded a [7,6,8,0,3,3] (by decide +kernel))
      node_2144
      (invalid_excluded a [7,6,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,3,8] (by decide +kernel)))

theorem node_2123 : Excluded a [7,6,8,0] :=
  branch_excluded a [7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,0,0] (by decide +kernel))
      node_2124
      node_2125
      node_2141
      (invalid_excluded a [7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,0,8] (by decide +kernel)))

theorem node_2147 : Excluded a [7,6,8,1,0,2] :=
  source_excluded a [7,6,8,1,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2149 : Excluded a [7,6,8,1,0,3,2] :=
  source_excluded a [7,6,8,1,0,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2150 : Excluded a [7,6,8,1,0,3,4] :=
  predecessor_excluded a [7,6,8,1,0,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2152 : Excluded a [7,6,8,1,0,3,5,2] :=
  source_excluded a [7,6,8,1,0,3,5,2] 7 0 2 (by decide) (by decide +kernel)

def b_2154 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 1
  | 4 => 0
  | 5 => 3
  | 6 => 5
  | 7 => 4
  | 8 => 2
  | _ => 0

def cert_2154 : LosingRegion (edgeOf a b_2154) 1 :=
  losingMask a b_2154 1 1212512640607529739485185
    (by decide +kernel) (by decide +kernel)

theorem node_2154 : Excluded a [7,6,8,1,0,3,5,4,2] :=
  losing_excluded a [7,6,8,1,0,3,5,4,2] (by decide) b_2154 (by decide +kernel) 4 1 2 cert_2154 (by change 4 ≠ 1 ∧ ¬ edgeOf a b_2154 4 1 ∧ 2 ≠ 4 ∧ maskRegion 1212512640607529739485185 4 2; decide +kernel)

theorem node_2153 : Excluded a [7,6,8,1,0,3,5,4] :=
  branch_excluded a [7,6,8,1,0,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,3,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,4,1] (by decide +kernel))
      node_2154
      (invalid_excluded a [7,6,8,1,0,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,4,8] (by decide +kernel)))

theorem node_2151 : Excluded a [7,6,8,1,0,3,5] :=
  branch_excluded a [7,6,8,1,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,1] (by decide +kernel))
      node_2152
      (invalid_excluded a [7,6,8,1,0,3,5,3] (by decide +kernel))
      node_2153
      (invalid_excluded a [7,6,8,1,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,8] (by decide +kernel)))

theorem node_2148 : Excluded a [7,6,8,1,0,3] :=
  branch_excluded a [7,6,8,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,1] (by decide +kernel))
      node_2149
      (invalid_excluded a [7,6,8,1,0,3,3] (by decide +kernel))
      node_2150
      node_2151
      (invalid_excluded a [7,6,8,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,8] (by decide +kernel)))

theorem node_2156 : Excluded a [7,6,8,1,0,4,2] :=
  source_excluded a [7,6,8,1,0,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2158 : Excluded a [7,6,8,1,0,4,3,2] :=
  source_excluded a [7,6,8,1,0,4,3,2] 7 0 2 (by decide) (by decide +kernel)

def b_2160 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 8
  | 3 => 1
  | 4 => 0
  | 5 => 4
  | 6 => 3
  | 7 => 5
  | 8 => 2
  | _ => 0

def cert_2160 : LosingRegion (edgeOf a b_2160) 1 :=
  losingMask a b_2160 1 1212510262918101439873025
    (by decide +kernel) (by decide +kernel)

theorem node_2160 : Excluded a [7,6,8,1,0,4,3,5,2] :=
  losing_excluded a [7,6,8,1,0,4,3,5,2] (by decide) b_2160 (by decide +kernel) 4 1 0 cert_2160 (by change 4 ≠ 1 ∧ ¬ edgeOf a b_2160 4 1 ∧ 0 ≠ 4 ∧ maskRegion 1212510262918101439873025 4 0; decide +kernel)

theorem node_2159 : Excluded a [7,6,8,1,0,4,3,5] :=
  branch_excluded a [7,6,8,1,0,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,4,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,5,1] (by decide +kernel))
      node_2160
      (invalid_excluded a [7,6,8,1,0,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,5,8] (by decide +kernel)))

theorem node_2157 : Excluded a [7,6,8,1,0,4,3] :=
  branch_excluded a [7,6,8,1,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,4,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,1] (by decide +kernel))
      node_2158
      (invalid_excluded a [7,6,8,1,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,4] (by decide +kernel))
      node_2159
      (invalid_excluded a [7,6,8,1,0,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,3,8] (by decide +kernel)))

theorem node_2161 : Excluded a [7,6,8,1,0,4,5] :=
  predecessor_excluded a [7,6,8,1,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2155 : Excluded a [7,6,8,1,0,4] :=
  branch_excluded a [7,6,8,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,1] (by decide +kernel))
      node_2156
      node_2157
      (invalid_excluded a [7,6,8,1,0,4,4] (by decide +kernel))
      node_2161
      (invalid_excluded a [7,6,8,1,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,8] (by decide +kernel)))

theorem node_2146 : Excluded a [7,6,8,1,0] :=
  branch_excluded a [7,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,1] (by decide +kernel))
      node_2147
      node_2148
      node_2155
      (invalid_excluded a [7,6,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,8] (by decide +kernel)))

theorem node_2162 : Excluded a [7,6,8,1,2] :=
  predecessor_excluded a [7,6,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2164 : Excluded a [7,6,8,1,3,0] :=
  predecessor_excluded a [7,6,8,1,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2165 : Excluded a [7,6,8,1,3,2] :=
  source_excluded a [7,6,8,1,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2166 : Excluded a [7,6,8,1,3,4] :=
  predecessor_excluded a [7,6,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2163 : Excluded a [7,6,8,1,3] :=
  branch_excluded a [7,6,8,1,3] (by decide)
    (fin9_cases _
      node_2164
      (invalid_excluded a [7,6,8,1,3,1] (by decide +kernel))
      node_2165
      (invalid_excluded a [7,6,8,1,3,3] (by decide +kernel))
      node_2166
      (invalid_excluded a [7,6,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,3,8] (by decide +kernel)))

theorem node_2145 : Excluded a [7,6,8,1] :=
  branch_excluded a [7,6,8,1] (by decide)
    (fin9_cases _
      node_2146
      (invalid_excluded a [7,6,8,1,1] (by decide +kernel))
      node_2162
      node_2163
      (invalid_excluded a [7,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,8] (by decide +kernel)))

theorem node_2168 : Excluded a [7,6,8,2,0] :=
  predecessor_excluded a [7,6,8,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2169 : Excluded a [7,6,8,2,1] :=
  predecessor_excluded a [7,6,8,2,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2171 : Excluded a [7,6,8,2,3,0] :=
  predecessor_excluded a [7,6,8,2,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2172 : Excluded a [7,6,8,2,3,1] :=
  source_excluded a [7,6,8,2,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2173 : Excluded a [7,6,8,2,3,4] :=
  predecessor_excluded a [7,6,8,2,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2170 : Excluded a [7,6,8,2,3] :=
  branch_excluded a [7,6,8,2,3] (by decide)
    (fin9_cases _
      node_2171
      node_2172
      (invalid_excluded a [7,6,8,2,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,3,3] (by decide +kernel))
      node_2173
      (invalid_excluded a [7,6,8,2,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,3,8] (by decide +kernel)))

theorem node_2167 : Excluded a [7,6,8,2] :=
  branch_excluded a [7,6,8,2] (by decide)
    (fin9_cases _
      node_2168
      node_2169
      (invalid_excluded a [7,6,8,2,2] (by decide +kernel))
      node_2170
      (invalid_excluded a [7,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,8] (by decide +kernel)))

theorem node_2174 : Excluded a [7,6,8,5] :=
  source_excluded a [7,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2122 : Excluded a [7,6,8] :=
  branch_excluded a [7,6,8] (by decide)
    (fin9_cases _
      node_2123
      node_2145
      node_2167
      (invalid_excluded a [7,6,8,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,4] (by decide +kernel))
      node_2174
      (invalid_excluded a [7,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,8] (by decide +kernel)))

theorem node_2003 : Excluded a [7,6] :=
  branch_excluded a [7,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0] (by decide +kernel))
      node_2004
      (invalid_excluded a [7,6,2] (by decide +kernel))
      node_2005
      node_2035
      node_2067
      (invalid_excluded a [7,6,6] (by decide +kernel))
      (invalid_excluded a [7,6,7] (by decide +kernel))
      node_2122)

theorem node_2175 : Excluded a [7,8] :=
  predecessor_excluded a [7,8] 2 8 0 1 (by decide) (by decide +kernel)

theorem node_1724 : Excluded a [7] :=
  branch_excluded a [7] (by decide)
    (fin9_cases _
      node_1725
      (invalid_excluded a [7,1] (by decide +kernel))
      (invalid_excluded a [7,2] (by decide +kernel))
      node_1726
      node_1822
      node_1887
      node_2003
      (invalid_excluded a [7,7] (by decide +kernel))
      node_2175)

theorem node_2177 : Excluded a [8,0] :=
  source_excluded a [8,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_2178 : Excluded a [8,3] :=
  predecessor_excluded a [8,3] 2 3 0 1 (by decide) (by decide +kernel)

theorem node_2180 : Excluded a [8,4,1] :=
  source_excluded a [8,4,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_2182 : Excluded a [8,4,3,0] :=
  source_excluded a [8,4,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2183 : Excluded a [8,4,3,1] :=
  source_excluded a [8,4,3,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2184 : Excluded a [8,4,3,2] :=
  source_excluded a [8,4,3,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_2185 : Excluded a [8,4,3,5] :=
  source_excluded a [8,4,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2187 : Excluded a [8,4,3,6,0] :=
  predecessor_excluded a [8,4,3,6,0] 3 0 1 4 (by decide) (by decide +kernel)

def b_2192 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 3
  | 3 => 6
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_2192 : LosingRegion (edgeOf a b_2192) 0 :=
  losingMask a b_2192 0 1333036703819851572970496
    (by decide +kernel) (by decide +kernel)

theorem node_2192 : Excluded a [8,4,3,6,1,0,2,5,7] :=
  losing_excluded a [8,4,3,6,1,0,2,5,7] (by decide) b_2192 (by decide +kernel) 3 0 1 cert_2192 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2192 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1333036703819851572970496 3 1; decide +kernel)

theorem node_2191 : Excluded a [8,4,3,6,1,0,2,5] :=
  branch_excluded a [8,4,3,6,1,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,3,6,1,0,2,5,0] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,5,1] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,5,2] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,5,6] (by decide +kernel))
      node_2192
      (invalid_excluded a [8,4,3,6,1,0,2,5,8] (by decide +kernel)))

theorem node_2190 : Excluded a [8,4,3,6,1,0,2] :=
  branch_excluded a [8,4,3,6,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,3,6,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,4] (by decide +kernel))
      node_2191
      (invalid_excluded a [8,4,3,6,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,2,8] (by decide +kernel)))

theorem node_2193 : Excluded a [8,4,3,6,1,0,5] :=
  predecessor_excluded a [8,4,3,6,1,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2189 : Excluded a [8,4,3,6,1,0] :=
  branch_excluded a [8,4,3,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,3,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,1] (by decide +kernel))
      node_2190
      (invalid_excluded a [8,4,3,6,1,0,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,4] (by decide +kernel))
      node_2193
      (invalid_excluded a [8,4,3,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,0,8] (by decide +kernel)))

theorem node_2194 : Excluded a [8,4,3,6,1,2] :=
  predecessor_excluded a [8,4,3,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2195 : Excluded a [8,4,3,6,1,7] :=
  source_excluded a [8,4,3,6,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2188 : Excluded a [8,4,3,6,1] :=
  branch_excluded a [8,4,3,6,1] (by decide)
    (fin9_cases _
      node_2189
      (invalid_excluded a [8,4,3,6,1,1] (by decide +kernel))
      node_2194
      (invalid_excluded a [8,4,3,6,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,1,6] (by decide +kernel))
      node_2195
      (invalid_excluded a [8,4,3,6,1,8] (by decide +kernel)))

theorem node_2196 : Excluded a [8,4,3,6,2] :=
  source_excluded a [8,4,3,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2197 : Excluded a [8,4,3,6,7] :=
  predecessor_excluded a [8,4,3,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_2186 : Excluded a [8,4,3,6] :=
  branch_excluded a [8,4,3,6] (by decide)
    (fin9_cases _
      node_2187
      node_2188
      node_2196
      (invalid_excluded a [8,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,3,6,6] (by decide +kernel))
      node_2197
      (invalid_excluded a [8,4,3,6,8] (by decide +kernel)))

theorem node_2199 : Excluded a [8,4,3,7,0] :=
  predecessor_excluded a [8,4,3,7,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_2203 : Excluded a [8,4,3,7,1,0,2,5] :=
  predecessor_excluded a [8,4,3,7,1,0,2,5] 0 5 3 7 (by decide) (by decide +kernel)

def b_2205 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 3
  | 3 => 7
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_2205 : LosingRegion (edgeOf a b_2205) 0 :=
  losingMask a b_2205 0 1285840781164859723088896
    (by decide +kernel) (by decide +kernel)

theorem node_2205 : Excluded a [8,4,3,7,1,0,2,6,5] :=
  losing_excluded a [8,4,3,7,1,0,2,6,5] (by decide) b_2205 (by decide +kernel) 3 0 1 cert_2205 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2205 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1285840781164859723088896 3 1; decide +kernel)

theorem node_2204 : Excluded a [8,4,3,7,1,0,2,6] :=
  branch_excluded a [8,4,3,7,1,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,3,7,1,0,2,6,0] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,6,1] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,6,2] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,6,4] (by decide +kernel))
      node_2205
      (invalid_excluded a [8,4,3,7,1,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,6,8] (by decide +kernel)))

theorem node_2202 : Excluded a [8,4,3,7,1,0,2] :=
  branch_excluded a [8,4,3,7,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,3,7,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,4] (by decide +kernel))
      node_2203
      node_2204
      (invalid_excluded a [8,4,3,7,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,2,8] (by decide +kernel)))

theorem node_2207 : Excluded a [8,4,3,7,1,0,5,2] :=
  predecessor_excluded a [8,4,3,7,1,0,5,2] 0 3 7 2 (by decide) (by decide +kernel)

theorem node_2208 : Excluded a [8,4,3,7,1,0,5,6] :=
  predecessor_excluded a [8,4,3,7,1,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2206 : Excluded a [8,4,3,7,1,0,5] :=
  branch_excluded a [8,4,3,7,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,3,7,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,5,1] (by decide +kernel))
      node_2207
      (invalid_excluded a [8,4,3,7,1,0,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,5,5] (by decide +kernel))
      node_2208
      (invalid_excluded a [8,4,3,7,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,5,8] (by decide +kernel)))

theorem node_2201 : Excluded a [8,4,3,7,1,0] :=
  branch_excluded a [8,4,3,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,3,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,1] (by decide +kernel))
      node_2202
      (invalid_excluded a [8,4,3,7,1,0,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,4] (by decide +kernel))
      node_2206
      (invalid_excluded a [8,4,3,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,0,8] (by decide +kernel)))

theorem node_2209 : Excluded a [8,4,3,7,1,2] :=
  predecessor_excluded a [8,4,3,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2200 : Excluded a [8,4,3,7,1] :=
  branch_excluded a [8,4,3,7,1] (by decide)
    (fin9_cases _
      node_2201
      (invalid_excluded a [8,4,3,7,1,1] (by decide +kernel))
      node_2209
      (invalid_excluded a [8,4,3,7,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,1,8] (by decide +kernel)))

theorem node_2210 : Excluded a [8,4,3,7,2] :=
  source_excluded a [8,4,3,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2211 : Excluded a [8,4,3,7,6] :=
  source_excluded a [8,4,3,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2198 : Excluded a [8,4,3,7] :=
  branch_excluded a [8,4,3,7] (by decide)
    (fin9_cases _
      node_2199
      node_2200
      node_2210
      (invalid_excluded a [8,4,3,7,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,5] (by decide +kernel))
      node_2211
      (invalid_excluded a [8,4,3,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,3,7,8] (by decide +kernel)))

theorem node_2181 : Excluded a [8,4,3] :=
  branch_excluded a [8,4,3] (by decide)
    (fin9_cases _
      node_2182
      node_2183
      node_2184
      (invalid_excluded a [8,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,3,4] (by decide +kernel))
      node_2185
      node_2186
      node_2198
      (invalid_excluded a [8,4,3,8] (by decide +kernel)))

theorem node_2212 : Excluded a [8,4,5] :=
  predecessor_excluded a [8,4,5] 0 5 1 2 (by decide) (by decide +kernel)

theorem node_2215 : Excluded a [8,4,6,0,1] :=
  predecessor_excluded a [8,4,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2216 : Excluded a [8,4,6,0,2] :=
  source_excluded a [8,4,6,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2219 : Excluded a [8,4,6,0,3,1,2] :=
  predecessor_excluded a [8,4,6,0,3,1,2] 0 2 5 6 (by decide) (by decide +kernel)

def b_2222 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 6
  | 3 => 0
  | 4 => 3
  | 5 => 1
  | 6 => 5
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_2222 : LosingRegion (edgeOf a b_2222) 0 :=
  losingMask a b_2222 0 1210114498628804337009664
    (by decide +kernel) (by decide +kernel)

theorem node_2222 : Excluded a [8,4,6,0,3,1,5,2,7] :=
  losing_excluded a [8,4,6,0,3,1,5,2,7] (by decide) b_2222 (by decide +kernel) 1 0 7 cert_2222 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2222 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1210114498628804337009664 1 7; decide +kernel)

theorem node_2221 : Excluded a [8,4,6,0,3,1,5,2] :=
  branch_excluded a [8,4,6,0,3,1,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,3,1,5,2,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,2,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,2,6] (by decide +kernel))
      node_2222
      (invalid_excluded a [8,4,6,0,3,1,5,2,8] (by decide +kernel)))

theorem node_2220 : Excluded a [8,4,6,0,3,1,5] :=
  branch_excluded a [8,4,6,0,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,1] (by decide +kernel))
      node_2221
      (invalid_excluded a [8,4,6,0,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,5,8] (by decide +kernel)))

theorem node_2218 : Excluded a [8,4,6,0,3,1] :=
  branch_excluded a [8,4,6,0,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,3,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,1] (by decide +kernel))
      node_2219
      (invalid_excluded a [8,4,6,0,3,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,4] (by decide +kernel))
      node_2220
      (invalid_excluded a [8,4,6,0,3,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,1,8] (by decide +kernel)))

theorem node_2223 : Excluded a [8,4,6,0,3,2] :=
  source_excluded a [8,4,6,0,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2224 : Excluded a [8,4,6,0,3,7] :=
  source_excluded a [8,4,6,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2217 : Excluded a [8,4,6,0,3] :=
  branch_excluded a [8,4,6,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,3,0] (by decide +kernel))
      node_2218
      node_2223
      (invalid_excluded a [8,4,6,0,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,3,6] (by decide +kernel))
      node_2224
      (invalid_excluded a [8,4,6,0,3,8] (by decide +kernel)))

theorem node_2227 : Excluded a [8,4,6,0,7,1,2] :=
  predecessor_excluded a [8,4,6,0,7,1,2] 0 2 5 6 (by decide) (by decide +kernel)

def b_2230 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 6
  | 3 => 0
  | 4 => 7
  | 5 => 1
  | 6 => 3
  | 7 => 2
  | 8 => 5
  | _ => 0

def cert_2230 : LosingRegion (edgeOf a b_2230) 0 :=
  losingMask a b_2230 0 1512375916081800157400064
    (by decide +kernel) (by decide +kernel)

theorem node_2230 : Excluded a [8,4,6,0,7,1,3,2,5] :=
  losing_excluded a [8,4,6,0,7,1,3,2,5] (by decide) b_2230 (by decide +kernel) 1 0 2 cert_2230 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2230 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1512375916081800157400064 1 2; decide +kernel)

theorem node_2229 : Excluded a [8,4,6,0,7,1,3,2] :=
  branch_excluded a [8,4,6,0,7,1,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,7,1,3,2,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,2,4] (by decide +kernel))
      node_2230
      (invalid_excluded a [8,4,6,0,7,1,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,2,8] (by decide +kernel)))

theorem node_2231 : Excluded a [8,4,6,0,7,1,3,5] :=
  source_excluded a [8,4,6,0,7,1,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_2228 : Excluded a [8,4,6,0,7,1,3] :=
  branch_excluded a [8,4,6,0,7,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,7,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,1] (by decide +kernel))
      node_2229
      (invalid_excluded a [8,4,6,0,7,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,4] (by decide +kernel))
      node_2231
      (invalid_excluded a [8,4,6,0,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,3,8] (by decide +kernel)))

theorem node_2232 : Excluded a [8,4,6,0,7,1,5] :=
  source_excluded a [8,4,6,0,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2226 : Excluded a [8,4,6,0,7,1] :=
  branch_excluded a [8,4,6,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,1] (by decide +kernel))
      node_2227
      node_2228
      (invalid_excluded a [8,4,6,0,7,1,4] (by decide +kernel))
      node_2232
      (invalid_excluded a [8,4,6,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,8] (by decide +kernel)))

theorem node_2233 : Excluded a [8,4,6,0,7,2] :=
  source_excluded a [8,4,6,0,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2235 : Excluded a [8,4,6,0,7,3,1] :=
  predecessor_excluded a [8,4,6,0,7,3,1] 3 1 2 6 (by decide) (by decide +kernel)

theorem node_2237 : Excluded a [8,4,6,0,7,3,2,1] :=
  source_excluded a [8,4,6,0,7,3,2,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2238 : Excluded a [8,4,6,0,7,3,2,5] :=
  source_excluded a [8,4,6,0,7,3,2,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_2236 : Excluded a [8,4,6,0,7,3,2] :=
  branch_excluded a [8,4,6,0,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,7,3,2,0] (by decide +kernel))
      node_2237
      (invalid_excluded a [8,4,6,0,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,3,2,4] (by decide +kernel))
      node_2238
      (invalid_excluded a [8,4,6,0,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,3,2,8] (by decide +kernel)))

theorem node_2239 : Excluded a [8,4,6,0,7,3,5] :=
  source_excluded a [8,4,6,0,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2234 : Excluded a [8,4,6,0,7,3] :=
  branch_excluded a [8,4,6,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,7,3,0] (by decide +kernel))
      node_2235
      node_2236
      (invalid_excluded a [8,4,6,0,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,3,4] (by decide +kernel))
      node_2239
      (invalid_excluded a [8,4,6,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,3,8] (by decide +kernel)))

theorem node_2225 : Excluded a [8,4,6,0,7] :=
  branch_excluded a [8,4,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,7,0] (by decide +kernel))
      node_2226
      node_2233
      node_2234
      (invalid_excluded a [8,4,6,0,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,8] (by decide +kernel)))

theorem node_2214 : Excluded a [8,4,6,0] :=
  branch_excluded a [8,4,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,0] (by decide +kernel))
      node_2215
      node_2216
      node_2217
      (invalid_excluded a [8,4,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,6] (by decide +kernel))
      node_2225
      (invalid_excluded a [8,4,6,0,8] (by decide +kernel)))

theorem node_2240 : Excluded a [8,4,6,1] :=
  source_excluded a [8,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2241 : Excluded a [8,4,6,2] :=
  source_excluded a [8,4,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_2242 : Excluded a [8,4,6,5] :=
  source_excluded a [8,4,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2244 : Excluded a [8,4,6,7,0] :=
  predecessor_excluded a [8,4,6,7,0] 3 0 1 4 (by decide) (by decide +kernel)

theorem node_2246 : Excluded a [8,4,6,7,1,0] :=
  source_excluded a [8,4,6,7,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2247 : Excluded a [8,4,6,7,1,2] :=
  source_excluded a [8,4,6,7,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2248 : Excluded a [8,4,6,7,1,3] :=
  predecessor_excluded a [8,4,6,7,1,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2245 : Excluded a [8,4,6,7,1] :=
  branch_excluded a [8,4,6,7,1] (by decide)
    (fin9_cases _
      node_2246
      (invalid_excluded a [8,4,6,7,1,1] (by decide +kernel))
      node_2247
      node_2248
      (invalid_excluded a [8,4,6,7,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,1,8] (by decide +kernel)))

theorem node_2249 : Excluded a [8,4,6,7,2] :=
  source_excluded a [8,4,6,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2251 : Excluded a [8,4,6,7,3,0] :=
  source_excluded a [8,4,6,7,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2253 : Excluded a [8,4,6,7,3,1,0] :=
  source_excluded a [8,4,6,7,3,1,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_2254 : Excluded a [8,4,6,7,3,1,2] :=
  predecessor_excluded a [8,4,6,7,3,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2256 : Excluded a [8,4,6,7,3,1,5,0] :=
  source_excluded a [8,4,6,7,3,1,5,0] 7 1 0 (by decide) (by decide +kernel)

theorem node_2258 : Excluded a [8,4,6,7,3,1,5,2,0] :=
  predecessor_excluded a [8,4,6,7,3,1,5,2,0] 1 0 7 8 (by decide) (by decide +kernel)

theorem node_2257 : Excluded a [8,4,6,7,3,1,5,2] :=
  branch_excluded a [8,4,6,7,3,1,5,2] (by decide)
    (fin9_cases _
      node_2258
      (invalid_excluded a [8,4,6,7,3,1,5,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,2,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,2,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,2,8] (by decide +kernel)))

theorem node_2255 : Excluded a [8,4,6,7,3,1,5] :=
  branch_excluded a [8,4,6,7,3,1,5] (by decide)
    (fin9_cases _
      node_2256
      (invalid_excluded a [8,4,6,7,3,1,5,1] (by decide +kernel))
      node_2257
      (invalid_excluded a [8,4,6,7,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,5,8] (by decide +kernel)))

theorem node_2252 : Excluded a [8,4,6,7,3,1] :=
  branch_excluded a [8,4,6,7,3,1] (by decide)
    (fin9_cases _
      node_2253
      (invalid_excluded a [8,4,6,7,3,1,1] (by decide +kernel))
      node_2254
      (invalid_excluded a [8,4,6,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,4] (by decide +kernel))
      node_2255
      (invalid_excluded a [8,4,6,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,1,8] (by decide +kernel)))

theorem node_2259 : Excluded a [8,4,6,7,3,2] :=
  source_excluded a [8,4,6,7,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2250 : Excluded a [8,4,6,7,3] :=
  branch_excluded a [8,4,6,7,3] (by decide)
    (fin9_cases _
      node_2251
      node_2252
      node_2259
      (invalid_excluded a [8,4,6,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,3,8] (by decide +kernel)))

theorem node_2243 : Excluded a [8,4,6,7] :=
  branch_excluded a [8,4,6,7] (by decide)
    (fin9_cases _
      node_2244
      node_2245
      node_2249
      node_2250
      (invalid_excluded a [8,4,6,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,7,8] (by decide +kernel)))

theorem node_2213 : Excluded a [8,4,6] :=
  branch_excluded a [8,4,6] (by decide)
    (fin9_cases _
      node_2214
      node_2240
      node_2241
      (invalid_excluded a [8,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,4] (by decide +kernel))
      node_2242
      (invalid_excluded a [8,4,6,6] (by decide +kernel))
      node_2243
      (invalid_excluded a [8,4,6,8] (by decide +kernel)))

theorem node_2260 : Excluded a [8,4,7] :=
  predecessor_excluded a [8,4,7] 1 8 2 0 (by decide) (by decide +kernel)

theorem node_2179 : Excluded a [8,4] :=
  branch_excluded a [8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0] (by decide +kernel))
      node_2180
      (invalid_excluded a [8,4,2] (by decide +kernel))
      node_2181
      (invalid_excluded a [8,4,4] (by decide +kernel))
      node_2212
      node_2213
      node_2260
      (invalid_excluded a [8,4,8] (by decide +kernel)))

theorem node_2262 : Excluded a [8,5,1] :=
  source_excluded a [8,5,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_2264 : Excluded a [8,5,3,0] :=
  source_excluded a [8,5,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2265 : Excluded a [8,5,3,1] :=
  predecessor_excluded a [8,5,3,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_2267 : Excluded a [8,5,3,2,0] :=
  predecessor_excluded a [8,5,3,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2268 : Excluded a [8,5,3,2,1] :=
  source_excluded a [8,5,3,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2269 : Excluded a [8,5,3,2,6] :=
  source_excluded a [8,5,3,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2271 : Excluded a [8,5,3,2,7,0] :=
  predecessor_excluded a [8,5,3,2,7,0] 3 0 1 5 (by decide) (by decide +kernel)

theorem node_2273 : Excluded a [8,5,3,2,7,1,0] :=
  predecessor_excluded a [8,5,3,2,7,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2274 : Excluded a [8,5,3,2,7,1,4] :=
  source_excluded a [8,5,3,2,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2272 : Excluded a [8,5,3,2,7,1] :=
  branch_excluded a [8,5,3,2,7,1] (by decide)
    (fin9_cases _
      node_2273
      (invalid_excluded a [8,5,3,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,7,1,2] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,7,1,3] (by decide +kernel))
      node_2274
      (invalid_excluded a [8,5,3,2,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,7,1,8] (by decide +kernel)))

theorem node_2275 : Excluded a [8,5,3,2,7,4] :=
  predecessor_excluded a [8,5,3,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2270 : Excluded a [8,5,3,2,7] :=
  branch_excluded a [8,5,3,2,7] (by decide)
    (fin9_cases _
      node_2271
      node_2272
      (invalid_excluded a [8,5,3,2,7,2] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,7,3] (by decide +kernel))
      node_2275
      (invalid_excluded a [8,5,3,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,7,8] (by decide +kernel)))

theorem node_2266 : Excluded a [8,5,3,2] :=
  branch_excluded a [8,5,3,2] (by decide)
    (fin9_cases _
      node_2267
      node_2268
      (invalid_excluded a [8,5,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,3,2,5] (by decide +kernel))
      node_2269
      node_2270
      (invalid_excluded a [8,5,3,2,8] (by decide +kernel)))

theorem node_2278 : Excluded a [8,5,3,6,0,1] :=
  predecessor_excluded a [8,5,3,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2279 : Excluded a [8,5,3,6,0,2] :=
  source_excluded a [8,5,3,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2280 : Excluded a [8,5,3,6,0,4] :=
  source_excluded a [8,5,3,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2281 : Excluded a [8,5,3,6,0,7] :=
  source_excluded a [8,5,3,6,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2277 : Excluded a [8,5,3,6,0] :=
  branch_excluded a [8,5,3,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,3,6,0,0] (by decide +kernel))
      node_2278
      node_2279
      (invalid_excluded a [8,5,3,6,0,3] (by decide +kernel))
      node_2280
      (invalid_excluded a [8,5,3,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,3,6,0,6] (by decide +kernel))
      node_2281
      (invalid_excluded a [8,5,3,6,0,8] (by decide +kernel)))

theorem node_2282 : Excluded a [8,5,3,6,1] :=
  source_excluded a [8,5,3,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2283 : Excluded a [8,5,3,6,2] :=
  source_excluded a [8,5,3,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2284 : Excluded a [8,5,3,6,7] :=
  predecessor_excluded a [8,5,3,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_2276 : Excluded a [8,5,3,6] :=
  branch_excluded a [8,5,3,6] (by decide)
    (fin9_cases _
      node_2277
      node_2282
      node_2283
      (invalid_excluded a [8,5,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,5,3,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,3,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,3,6,6] (by decide +kernel))
      node_2284
      (invalid_excluded a [8,5,3,6,8] (by decide +kernel)))

theorem node_2287 : Excluded a [8,5,3,7,0,1] :=
  predecessor_excluded a [8,5,3,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2288 : Excluded a [8,5,3,7,0,2] :=
  source_excluded a [8,5,3,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2291 : Excluded a [8,5,3,7,0,4,1,2] :=
  predecessor_excluded a [8,5,3,7,0,4,1,2] 0 3 7 2 (by decide) (by decide +kernel)

theorem node_2293 : Excluded a [8,5,3,7,0,4,1,6,2] :=
  source_excluded a [8,5,3,7,0,4,1,6,2] 8 0 2 (by decide) (by decide +kernel)

theorem node_2292 : Excluded a [8,5,3,7,0,4,1,6] :=
  branch_excluded a [8,5,3,7,0,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,3,7,0,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,6,1] (by decide +kernel))
      node_2293
      (invalid_excluded a [8,5,3,7,0,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,6,8] (by decide +kernel)))

theorem node_2290 : Excluded a [8,5,3,7,0,4,1] :=
  branch_excluded a [8,5,3,7,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,3,7,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,1] (by decide +kernel))
      node_2291
      (invalid_excluded a [8,5,3,7,0,4,1,3] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,4] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,5] (by decide +kernel))
      node_2292
      (invalid_excluded a [8,5,3,7,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,1,8] (by decide +kernel)))

theorem node_2295 : Excluded a [8,5,3,7,0,4,2,1] :=
  source_excluded a [8,5,3,7,0,4,2,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2297 : Excluded a [8,5,3,7,0,4,2,6,1] :=
  source_excluded a [8,5,3,7,0,4,2,6,1] 0 2 8 (by decide) (by decide +kernel)

theorem node_2296 : Excluded a [8,5,3,7,0,4,2,6] :=
  branch_excluded a [8,5,3,7,0,4,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,3,7,0,4,2,6,0] (by decide +kernel))
      node_2297
      (invalid_excluded a [8,5,3,7,0,4,2,6,2] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,6,3] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,6,8] (by decide +kernel)))

theorem node_2294 : Excluded a [8,5,3,7,0,4,2] :=
  branch_excluded a [8,5,3,7,0,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,3,7,0,4,2,0] (by decide +kernel))
      node_2295
      (invalid_excluded a [8,5,3,7,0,4,2,2] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,3] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,5] (by decide +kernel))
      node_2296
      (invalid_excluded a [8,5,3,7,0,4,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,2,8] (by decide +kernel)))

theorem node_2289 : Excluded a [8,5,3,7,0,4] :=
  branch_excluded a [8,5,3,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,3,7,0,4,0] (by decide +kernel))
      node_2290
      node_2294
      (invalid_excluded a [8,5,3,7,0,4,3] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,5] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,4,8] (by decide +kernel)))

theorem node_2286 : Excluded a [8,5,3,7,0] :=
  branch_excluded a [8,5,3,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,3,7,0,0] (by decide +kernel))
      node_2287
      node_2288
      (invalid_excluded a [8,5,3,7,0,3] (by decide +kernel))
      node_2289
      (invalid_excluded a [8,5,3,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,0,8] (by decide +kernel)))

theorem node_2298 : Excluded a [8,5,3,7,1] :=
  source_excluded a [8,5,3,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2299 : Excluded a [8,5,3,7,2] :=
  source_excluded a [8,5,3,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2300 : Excluded a [8,5,3,7,6] :=
  source_excluded a [8,5,3,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2285 : Excluded a [8,5,3,7] :=
  branch_excluded a [8,5,3,7] (by decide)
    (fin9_cases _
      node_2286
      node_2298
      node_2299
      (invalid_excluded a [8,5,3,7,3] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,5] (by decide +kernel))
      node_2300
      (invalid_excluded a [8,5,3,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,3,7,8] (by decide +kernel)))

theorem node_2263 : Excluded a [8,5,3] :=
  branch_excluded a [8,5,3] (by decide)
    (fin9_cases _
      node_2264
      node_2265
      node_2266
      (invalid_excluded a [8,5,3,3] (by decide +kernel))
      (invalid_excluded a [8,5,3,4] (by decide +kernel))
      (invalid_excluded a [8,5,3,5] (by decide +kernel))
      node_2276
      node_2285
      (invalid_excluded a [8,5,3,8] (by decide +kernel)))

theorem node_2302 : Excluded a [8,5,4,0] :=
  source_excluded a [8,5,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2303 : Excluded a [8,5,4,1] :=
  predecessor_excluded a [8,5,4,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_2304 : Excluded a [8,5,4,2] :=
  source_excluded a [8,5,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_2306 : Excluded a [8,5,4,6,0] :=
  source_excluded a [8,5,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2307 : Excluded a [8,5,4,6,1] :=
  source_excluded a [8,5,4,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2308 : Excluded a [8,5,4,6,2] :=
  source_excluded a [8,5,4,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2309 : Excluded a [8,5,4,6,3] :=
  predecessor_excluded a [8,5,4,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2310 : Excluded a [8,5,4,6,7] :=
  predecessor_excluded a [8,5,4,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_2305 : Excluded a [8,5,4,6] :=
  branch_excluded a [8,5,4,6] (by decide)
    (fin9_cases _
      node_2306
      node_2307
      node_2308
      node_2309
      (invalid_excluded a [8,5,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,4,6,6] (by decide +kernel))
      node_2310
      (invalid_excluded a [8,5,4,6,8] (by decide +kernel)))

theorem node_2312 : Excluded a [8,5,4,7,0] :=
  source_excluded a [8,5,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2313 : Excluded a [8,5,4,7,1] :=
  source_excluded a [8,5,4,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2314 : Excluded a [8,5,4,7,2] :=
  source_excluded a [8,5,4,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2316 : Excluded a [8,5,4,7,3,0] :=
  predecessor_excluded a [8,5,4,7,3,0] 3 0 1 5 (by decide) (by decide +kernel)

theorem node_2318 : Excluded a [8,5,4,7,3,1,0] :=
  predecessor_excluded a [8,5,4,7,3,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2319 : Excluded a [8,5,4,7,3,1,2] :=
  predecessor_excluded a [8,5,4,7,3,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2317 : Excluded a [8,5,4,7,3,1] :=
  branch_excluded a [8,5,4,7,3,1] (by decide)
    (fin9_cases _
      node_2318
      (invalid_excluded a [8,5,4,7,3,1,1] (by decide +kernel))
      node_2319
      (invalid_excluded a [8,5,4,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,1,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,1,5] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,1,8] (by decide +kernel)))

theorem node_2320 : Excluded a [8,5,4,7,3,2] :=
  source_excluded a [8,5,4,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2315 : Excluded a [8,5,4,7,3] :=
  branch_excluded a [8,5,4,7,3] (by decide)
    (fin9_cases _
      node_2316
      node_2317
      node_2320
      (invalid_excluded a [8,5,4,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,3,8] (by decide +kernel)))

theorem node_2321 : Excluded a [8,5,4,7,6] :=
  source_excluded a [8,5,4,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2311 : Excluded a [8,5,4,7] :=
  branch_excluded a [8,5,4,7] (by decide)
    (fin9_cases _
      node_2312
      node_2313
      node_2314
      node_2315
      (invalid_excluded a [8,5,4,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,5] (by decide +kernel))
      node_2321
      (invalid_excluded a [8,5,4,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,4,7,8] (by decide +kernel)))

theorem node_2301 : Excluded a [8,5,4] :=
  branch_excluded a [8,5,4] (by decide)
    (fin9_cases _
      node_2302
      node_2303
      node_2304
      (invalid_excluded a [8,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,4,5] (by decide +kernel))
      node_2305
      node_2311
      (invalid_excluded a [8,5,4,8] (by decide +kernel)))

theorem node_2322 : Excluded a [8,5,6] :=
  predecessor_excluded a [8,5,6] 0 6 1 2 (by decide) (by decide +kernel)

theorem node_2323 : Excluded a [8,5,7] :=
  predecessor_excluded a [8,5,7] 1 8 2 0 (by decide) (by decide +kernel)

theorem node_2261 : Excluded a [8,5] :=
  branch_excluded a [8,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0] (by decide +kernel))
      node_2262
      (invalid_excluded a [8,5,2] (by decide +kernel))
      node_2263
      node_2301
      (invalid_excluded a [8,5,5] (by decide +kernel))
      node_2322
      node_2323
      (invalid_excluded a [8,5,8] (by decide +kernel)))

theorem node_2325 : Excluded a [8,6,1] :=
  source_excluded a [8,6,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_2327 : Excluded a [8,6,3,0] :=
  source_excluded a [8,6,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2328 : Excluded a [8,6,3,1] :=
  predecessor_excluded a [8,6,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_2330 : Excluded a [8,6,3,2,0] :=
  predecessor_excluded a [8,6,3,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2331 : Excluded a [8,6,3,2,1] :=
  predecessor_excluded a [8,6,3,2,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2334 : Excluded a [8,6,3,2,7,0,1] :=
  predecessor_excluded a [8,6,3,2,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_2335 : Excluded a [8,6,3,2,7,0,4] :=
  source_excluded a [8,6,3,2,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2336 : Excluded a [8,6,3,2,7,0,5] :=
  source_excluded a [8,6,3,2,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2333 : Excluded a [8,6,3,2,7,0] :=
  branch_excluded a [8,6,3,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,3,2,7,0,0] (by decide +kernel))
      node_2334
      (invalid_excluded a [8,6,3,2,7,0,2] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,7,0,3] (by decide +kernel))
      node_2335
      node_2336
      (invalid_excluded a [8,6,3,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,7,0,8] (by decide +kernel)))

theorem node_2337 : Excluded a [8,6,3,2,7,1] :=
  source_excluded a [8,6,3,2,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2338 : Excluded a [8,6,3,2,7,4] :=
  predecessor_excluded a [8,6,3,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2332 : Excluded a [8,6,3,2,7] :=
  branch_excluded a [8,6,3,2,7] (by decide)
    (fin9_cases _
      node_2333
      node_2337
      (invalid_excluded a [8,6,3,2,7,2] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,7,3] (by decide +kernel))
      node_2338
      (invalid_excluded a [8,6,3,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,7,8] (by decide +kernel)))

theorem node_2329 : Excluded a [8,6,3,2] :=
  branch_excluded a [8,6,3,2] (by decide)
    (fin9_cases _
      node_2330
      node_2331
      (invalid_excluded a [8,6,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,4] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,3,2,6] (by decide +kernel))
      node_2332
      (invalid_excluded a [8,6,3,2,8] (by decide +kernel)))

theorem node_2339 : Excluded a [8,6,3,5] :=
  source_excluded a [8,6,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2342 : Excluded a [8,6,3,7,0,1] :=
  source_excluded a [8,6,3,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2343 : Excluded a [8,6,3,7,0,2] :=
  source_excluded a [8,6,3,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2346 : Excluded a [8,6,3,7,0,4,1,2] :=
  predecessor_excluded a [8,6,3,7,0,4,1,2] 0 3 7 2 (by decide) (by decide +kernel)

theorem node_2347 : Excluded a [8,6,3,7,0,4,1,5] :=
  predecessor_excluded a [8,6,3,7,0,4,1,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_2345 : Excluded a [8,6,3,7,0,4,1] :=
  branch_excluded a [8,6,3,7,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,3,7,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,4,1,1] (by decide +kernel))
      node_2346
      (invalid_excluded a [8,6,3,7,0,4,1,3] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,4,1,4] (by decide +kernel))
      node_2347
      (invalid_excluded a [8,6,3,7,0,4,1,6] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,4,1,8] (by decide +kernel)))

theorem node_2348 : Excluded a [8,6,3,7,0,4,2] :=
  source_excluded a [8,6,3,7,0,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2349 : Excluded a [8,6,3,7,0,4,5] :=
  predecessor_excluded a [8,6,3,7,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2344 : Excluded a [8,6,3,7,0,4] :=
  branch_excluded a [8,6,3,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,3,7,0,4,0] (by decide +kernel))
      node_2345
      node_2348
      (invalid_excluded a [8,6,3,7,0,4,3] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,4,4] (by decide +kernel))
      node_2349
      (invalid_excluded a [8,6,3,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,4,8] (by decide +kernel)))

theorem node_2341 : Excluded a [8,6,3,7,0] :=
  branch_excluded a [8,6,3,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,3,7,0,0] (by decide +kernel))
      node_2342
      node_2343
      (invalid_excluded a [8,6,3,7,0,3] (by decide +kernel))
      node_2344
      (invalid_excluded a [8,6,3,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,0,8] (by decide +kernel)))

theorem node_2350 : Excluded a [8,6,3,7,1] :=
  predecessor_excluded a [8,6,3,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2352 : Excluded a [8,6,3,7,2,0] :=
  predecessor_excluded a [8,6,3,7,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_2353 : Excluded a [8,6,3,7,2,1] :=
  source_excluded a [8,6,3,7,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2355 : Excluded a [8,6,3,7,2,4,0] :=
  predecessor_excluded a [8,6,3,7,2,4,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2357 : Excluded a [8,6,3,7,2,4,1,0] :=
  source_excluded a [8,6,3,7,2,4,1,0] 7 1 0 (by decide) (by decide +kernel)

theorem node_2358 : Excluded a [8,6,3,7,2,4,1,5] :=
  predecessor_excluded a [8,6,3,7,2,4,1,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_2356 : Excluded a [8,6,3,7,2,4,1] :=
  branch_excluded a [8,6,3,7,2,4,1] (by decide)
    (fin9_cases _
      node_2357
      (invalid_excluded a [8,6,3,7,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,4,1,2] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,4,1,3] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,4,1,4] (by decide +kernel))
      node_2358
      (invalid_excluded a [8,6,3,7,2,4,1,6] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,4,1,8] (by decide +kernel)))

theorem node_2359 : Excluded a [8,6,3,7,2,4,5] :=
  predecessor_excluded a [8,6,3,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2354 : Excluded a [8,6,3,7,2,4] :=
  branch_excluded a [8,6,3,7,2,4] (by decide)
    (fin9_cases _
      node_2355
      node_2356
      (invalid_excluded a [8,6,3,7,2,4,2] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,4,3] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,4,4] (by decide +kernel))
      node_2359
      (invalid_excluded a [8,6,3,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,4,8] (by decide +kernel)))

theorem node_2351 : Excluded a [8,6,3,7,2] :=
  branch_excluded a [8,6,3,7,2] (by decide)
    (fin9_cases _
      node_2352
      node_2353
      (invalid_excluded a [8,6,3,7,2,2] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,3] (by decide +kernel))
      node_2354
      (invalid_excluded a [8,6,3,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,2,8] (by decide +kernel)))

theorem node_2340 : Excluded a [8,6,3,7] :=
  branch_excluded a [8,6,3,7] (by decide)
    (fin9_cases _
      node_2341
      node_2350
      node_2351
      (invalid_excluded a [8,6,3,7,3] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,3,7,8] (by decide +kernel)))

theorem node_2326 : Excluded a [8,6,3] :=
  branch_excluded a [8,6,3] (by decide)
    (fin9_cases _
      node_2327
      node_2328
      node_2329
      (invalid_excluded a [8,6,3,3] (by decide +kernel))
      (invalid_excluded a [8,6,3,4] (by decide +kernel))
      node_2339
      (invalid_excluded a [8,6,3,6] (by decide +kernel))
      node_2340
      (invalid_excluded a [8,6,3,8] (by decide +kernel)))

theorem node_2361 : Excluded a [8,6,4,0] :=
  source_excluded a [8,6,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2363 : Excluded a [8,6,4,1,0] :=
  source_excluded a [8,6,4,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2364 : Excluded a [8,6,4,1,2] :=
  predecessor_excluded a [8,6,4,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2367 : Excluded a [8,6,4,1,3,0,2] :=
  source_excluded a [8,6,4,1,3,0,2] 1 0 6 (by decide) (by decide +kernel)

def b_2370 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 6
  | 2 => 4
  | 3 => 1
  | 4 => 3
  | 5 => 0
  | 6 => 5
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_2370 : LosingRegion (edgeOf a b_2370) 3 :=
  losingMask a b_2370 3 1210114498610661321409921
    (by decide +kernel) (by decide +kernel)

theorem node_2370 : Excluded a [8,6,4,1,3,0,5,2,7] :=
  losing_excluded a [8,6,4,1,3,0,5,2,7] (by decide) b_2370 (by decide +kernel) 0 3 7 cert_2370 (by change 0 ≠ 3 ∧ ¬ edgeOf a b_2370 0 3 ∧ 7 ≠ 0 ∧ maskRegion 1210114498610661321409921 0 7; decide +kernel)

theorem node_2369 : Excluded a [8,6,4,1,3,0,5,2] :=
  branch_excluded a [8,6,4,1,3,0,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,4,1,3,0,5,2,0] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,2,2] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,2,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,2,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,2,6] (by decide +kernel))
      node_2370
      (invalid_excluded a [8,6,4,1,3,0,5,2,8] (by decide +kernel)))

theorem node_2368 : Excluded a [8,6,4,1,3,0,5] :=
  branch_excluded a [8,6,4,1,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,4,1,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,1] (by decide +kernel))
      node_2369
      (invalid_excluded a [8,6,4,1,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,5,8] (by decide +kernel)))

theorem node_2366 : Excluded a [8,6,4,1,3,0] :=
  branch_excluded a [8,6,4,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,4,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,1] (by decide +kernel))
      node_2367
      (invalid_excluded a [8,6,4,1,3,0,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,4] (by decide +kernel))
      node_2368
      (invalid_excluded a [8,6,4,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,0,8] (by decide +kernel)))

theorem node_2371 : Excluded a [8,6,4,1,3,2] :=
  source_excluded a [8,6,4,1,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2372 : Excluded a [8,6,4,1,3,7] :=
  source_excluded a [8,6,4,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2365 : Excluded a [8,6,4,1,3] :=
  branch_excluded a [8,6,4,1,3] (by decide)
    (fin9_cases _
      node_2366
      (invalid_excluded a [8,6,4,1,3,1] (by decide +kernel))
      node_2371
      (invalid_excluded a [8,6,4,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,3,6] (by decide +kernel))
      node_2372
      (invalid_excluded a [8,6,4,1,3,8] (by decide +kernel)))

theorem node_2375 : Excluded a [8,6,4,1,7,0,2] :=
  source_excluded a [8,6,4,1,7,0,2] 1 0 6 (by decide) (by decide +kernel)

def b_2378 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 6
  | 2 => 4
  | 3 => 1
  | 4 => 7
  | 5 => 0
  | 6 => 3
  | 7 => 2
  | 8 => 5
  | _ => 0

def cert_2378 : LosingRegion (edgeOf a b_2378) 0 :=
  losingMask a b_2378 0 1285705024657692535360512
    (by decide +kernel) (by decide +kernel)

theorem node_2378 : Excluded a [8,6,4,1,7,0,3,2,5] :=
  losing_excluded a [8,6,4,1,7,0,3,2,5] (by decide) b_2378 (by decide +kernel) 1 0 2 cert_2378 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2378 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1285705024657692535360512 1 2; decide +kernel)

theorem node_2377 : Excluded a [8,6,4,1,7,0,3,2] :=
  branch_excluded a [8,6,4,1,7,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,4,1,7,0,3,2,0] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,2,4] (by decide +kernel))
      node_2378
      (invalid_excluded a [8,6,4,1,7,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,2,8] (by decide +kernel)))

theorem node_2379 : Excluded a [8,6,4,1,7,0,3,5] :=
  source_excluded a [8,6,4,1,7,0,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_2376 : Excluded a [8,6,4,1,7,0,3] :=
  branch_excluded a [8,6,4,1,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,4,1,7,0,3,0] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,1] (by decide +kernel))
      node_2377
      (invalid_excluded a [8,6,4,1,7,0,3,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,4] (by decide +kernel))
      node_2379
      (invalid_excluded a [8,6,4,1,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,3,8] (by decide +kernel)))

theorem node_2380 : Excluded a [8,6,4,1,7,0,5] :=
  source_excluded a [8,6,4,1,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2374 : Excluded a [8,6,4,1,7,0] :=
  branch_excluded a [8,6,4,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,4,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,1] (by decide +kernel))
      node_2375
      node_2376
      (invalid_excluded a [8,6,4,1,7,0,4] (by decide +kernel))
      node_2380
      (invalid_excluded a [8,6,4,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,0,8] (by decide +kernel)))

theorem node_2381 : Excluded a [8,6,4,1,7,2] :=
  source_excluded a [8,6,4,1,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2383 : Excluded a [8,6,4,1,7,3,0] :=
  predecessor_excluded a [8,6,4,1,7,3,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2384 : Excluded a [8,6,4,1,7,3,2] :=
  source_excluded a [8,6,4,1,7,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2385 : Excluded a [8,6,4,1,7,3,5] :=
  source_excluded a [8,6,4,1,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2382 : Excluded a [8,6,4,1,7,3] :=
  branch_excluded a [8,6,4,1,7,3] (by decide)
    (fin9_cases _
      node_2383
      (invalid_excluded a [8,6,4,1,7,3,1] (by decide +kernel))
      node_2384
      (invalid_excluded a [8,6,4,1,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,3,4] (by decide +kernel))
      node_2385
      (invalid_excluded a [8,6,4,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,3,8] (by decide +kernel)))

theorem node_2373 : Excluded a [8,6,4,1,7] :=
  branch_excluded a [8,6,4,1,7] (by decide)
    (fin9_cases _
      node_2374
      (invalid_excluded a [8,6,4,1,7,1] (by decide +kernel))
      node_2381
      node_2382
      (invalid_excluded a [8,6,4,1,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,7,8] (by decide +kernel)))

theorem node_2362 : Excluded a [8,6,4,1] :=
  branch_excluded a [8,6,4,1] (by decide)
    (fin9_cases _
      node_2363
      (invalid_excluded a [8,6,4,1,1] (by decide +kernel))
      node_2364
      node_2365
      (invalid_excluded a [8,6,4,1,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,1,6] (by decide +kernel))
      node_2373
      (invalid_excluded a [8,6,4,1,8] (by decide +kernel)))

theorem node_2386 : Excluded a [8,6,4,2] :=
  source_excluded a [8,6,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_2387 : Excluded a [8,6,4,5] :=
  source_excluded a [8,6,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2389 : Excluded a [8,6,4,7,0] :=
  source_excluded a [8,6,4,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2390 : Excluded a [8,6,4,7,1] :=
  predecessor_excluded a [8,6,4,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2392 : Excluded a [8,6,4,7,2,0] :=
  predecessor_excluded a [8,6,4,7,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_2393 : Excluded a [8,6,4,7,2,1] :=
  source_excluded a [8,6,4,7,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2394 : Excluded a [8,6,4,7,2,3] :=
  predecessor_excluded a [8,6,4,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2391 : Excluded a [8,6,4,7,2] :=
  branch_excluded a [8,6,4,7,2] (by decide)
    (fin9_cases _
      node_2392
      node_2393
      (invalid_excluded a [8,6,4,7,2,2] (by decide +kernel))
      node_2394
      (invalid_excluded a [8,6,4,7,2,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,2,8] (by decide +kernel)))

theorem node_2397 : Excluded a [8,6,4,7,3,0,1] :=
  predecessor_excluded a [8,6,4,7,3,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_2398 : Excluded a [8,6,4,7,3,0,2] :=
  source_excluded a [8,6,4,7,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2400 : Excluded a [8,6,4,7,3,0,5,1] :=
  source_excluded a [8,6,4,7,3,0,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2402 : Excluded a [8,6,4,7,3,0,5,2,1] :=
  source_excluded a [8,6,4,7,3,0,5,2,1] 0 2 8 (by decide) (by decide +kernel)

theorem node_2401 : Excluded a [8,6,4,7,3,0,5,2] :=
  branch_excluded a [8,6,4,7,3,0,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,4,7,3,0,5,2,0] (by decide +kernel))
      node_2402
      (invalid_excluded a [8,6,4,7,3,0,5,2,2] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,2,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,2,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,2,8] (by decide +kernel)))

theorem node_2399 : Excluded a [8,6,4,7,3,0,5] :=
  branch_excluded a [8,6,4,7,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,4,7,3,0,5,0] (by decide +kernel))
      node_2400
      node_2401
      (invalid_excluded a [8,6,4,7,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,5,8] (by decide +kernel)))

theorem node_2396 : Excluded a [8,6,4,7,3,0] :=
  branch_excluded a [8,6,4,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,4,7,3,0,0] (by decide +kernel))
      node_2397
      node_2398
      (invalid_excluded a [8,6,4,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,4] (by decide +kernel))
      node_2399
      (invalid_excluded a [8,6,4,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,0,8] (by decide +kernel)))

theorem node_2403 : Excluded a [8,6,4,7,3,1] :=
  source_excluded a [8,6,4,7,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2404 : Excluded a [8,6,4,7,3,2] :=
  source_excluded a [8,6,4,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2395 : Excluded a [8,6,4,7,3] :=
  branch_excluded a [8,6,4,7,3] (by decide)
    (fin9_cases _
      node_2396
      node_2403
      node_2404
      (invalid_excluded a [8,6,4,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,3,8] (by decide +kernel)))

theorem node_2388 : Excluded a [8,6,4,7] :=
  branch_excluded a [8,6,4,7] (by decide)
    (fin9_cases _
      node_2389
      node_2390
      node_2391
      node_2395
      (invalid_excluded a [8,6,4,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,4,7,8] (by decide +kernel)))

theorem node_2360 : Excluded a [8,6,4] :=
  branch_excluded a [8,6,4] (by decide)
    (fin9_cases _
      node_2361
      node_2362
      node_2386
      (invalid_excluded a [8,6,4,3] (by decide +kernel))
      (invalid_excluded a [8,6,4,4] (by decide +kernel))
      node_2387
      (invalid_excluded a [8,6,4,6] (by decide +kernel))
      node_2388
      (invalid_excluded a [8,6,4,8] (by decide +kernel)))

theorem node_2407 : Excluded a [8,6,5,0,1] :=
  predecessor_excluded a [8,6,5,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2408 : Excluded a [8,6,5,0,2] :=
  source_excluded a [8,6,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2410 : Excluded a [8,6,5,0,3,1] :=
  source_excluded a [8,6,5,0,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2411 : Excluded a [8,6,5,0,3,2] :=
  source_excluded a [8,6,5,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2412 : Excluded a [8,6,5,0,3,4] :=
  predecessor_excluded a [8,6,5,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2413 : Excluded a [8,6,5,0,3,7] :=
  source_excluded a [8,6,5,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2409 : Excluded a [8,6,5,0,3] :=
  branch_excluded a [8,6,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,3,0] (by decide +kernel))
      node_2410
      node_2411
      (invalid_excluded a [8,6,5,0,3,3] (by decide +kernel))
      node_2412
      (invalid_excluded a [8,6,5,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,3,6] (by decide +kernel))
      node_2413
      (invalid_excluded a [8,6,5,0,3,8] (by decide +kernel)))

theorem node_2415 : Excluded a [8,6,5,0,7,1] :=
  source_excluded a [8,6,5,0,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2416 : Excluded a [8,6,5,0,7,2] :=
  source_excluded a [8,6,5,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2419 : Excluded a [8,6,5,0,7,3,1,2] :=
  predecessor_excluded a [8,6,5,0,7,3,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_2421 : Excluded a [8,6,5,0,7,3,1,4,2] :=
  predecessor_excluded a [8,6,5,0,7,3,1,4,2] 1 0 8 3 (by decide) (by decide +kernel)

theorem node_2420 : Excluded a [8,6,5,0,7,3,1,4] :=
  branch_excluded a [8,6,5,0,7,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,7,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,4,1] (by decide +kernel))
      node_2421
      (invalid_excluded a [8,6,5,0,7,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,4,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,4,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,4,8] (by decide +kernel)))

theorem node_2418 : Excluded a [8,6,5,0,7,3,1] :=
  branch_excluded a [8,6,5,0,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,1] (by decide +kernel))
      node_2419
      (invalid_excluded a [8,6,5,0,7,3,1,3] (by decide +kernel))
      node_2420
      (invalid_excluded a [8,6,5,0,7,3,1,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,1,8] (by decide +kernel)))

theorem node_2422 : Excluded a [8,6,5,0,7,3,2] :=
  source_excluded a [8,6,5,0,7,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2423 : Excluded a [8,6,5,0,7,3,4] :=
  source_excluded a [8,6,5,0,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2417 : Excluded a [8,6,5,0,7,3] :=
  branch_excluded a [8,6,5,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,7,3,0] (by decide +kernel))
      node_2418
      node_2422
      (invalid_excluded a [8,6,5,0,7,3,3] (by decide +kernel))
      node_2423
      (invalid_excluded a [8,6,5,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,3,8] (by decide +kernel)))

theorem node_2424 : Excluded a [8,6,5,0,7,4] :=
  predecessor_excluded a [8,6,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2414 : Excluded a [8,6,5,0,7] :=
  branch_excluded a [8,6,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,7,0] (by decide +kernel))
      node_2415
      node_2416
      node_2417
      node_2424
      (invalid_excluded a [8,6,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,8] (by decide +kernel)))

theorem node_2406 : Excluded a [8,6,5,0] :=
  branch_excluded a [8,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,0] (by decide +kernel))
      node_2407
      node_2408
      node_2409
      (invalid_excluded a [8,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,6] (by decide +kernel))
      node_2414
      (invalid_excluded a [8,6,5,0,8] (by decide +kernel)))

theorem node_2426 : Excluded a [8,6,5,1,0] :=
  source_excluded a [8,6,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2427 : Excluded a [8,6,5,1,2] :=
  source_excluded a [8,6,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2429 : Excluded a [8,6,5,1,3,0] :=
  source_excluded a [8,6,5,1,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2430 : Excluded a [8,6,5,1,3,2] :=
  source_excluded a [8,6,5,1,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2431 : Excluded a [8,6,5,1,3,4] :=
  predecessor_excluded a [8,6,5,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2432 : Excluded a [8,6,5,1,3,7] :=
  source_excluded a [8,6,5,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2428 : Excluded a [8,6,5,1,3] :=
  branch_excluded a [8,6,5,1,3] (by decide)
    (fin9_cases _
      node_2429
      (invalid_excluded a [8,6,5,1,3,1] (by decide +kernel))
      node_2430
      (invalid_excluded a [8,6,5,1,3,3] (by decide +kernel))
      node_2431
      (invalid_excluded a [8,6,5,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,3,6] (by decide +kernel))
      node_2432
      (invalid_excluded a [8,6,5,1,3,8] (by decide +kernel)))

theorem node_2434 : Excluded a [8,6,5,1,7,0] :=
  source_excluded a [8,6,5,1,7,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2435 : Excluded a [8,6,5,1,7,2] :=
  source_excluded a [8,6,5,1,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2437 : Excluded a [8,6,5,1,7,3,0] :=
  predecessor_excluded a [8,6,5,1,7,3,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2438 : Excluded a [8,6,5,1,7,3,2] :=
  source_excluded a [8,6,5,1,7,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2439 : Excluded a [8,6,5,1,7,3,4] :=
  source_excluded a [8,6,5,1,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2436 : Excluded a [8,6,5,1,7,3] :=
  branch_excluded a [8,6,5,1,7,3] (by decide)
    (fin9_cases _
      node_2437
      (invalid_excluded a [8,6,5,1,7,3,1] (by decide +kernel))
      node_2438
      (invalid_excluded a [8,6,5,1,7,3,3] (by decide +kernel))
      node_2439
      (invalid_excluded a [8,6,5,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,3,8] (by decide +kernel)))

theorem node_2440 : Excluded a [8,6,5,1,7,4] :=
  predecessor_excluded a [8,6,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2433 : Excluded a [8,6,5,1,7] :=
  branch_excluded a [8,6,5,1,7] (by decide)
    (fin9_cases _
      node_2434
      (invalid_excluded a [8,6,5,1,7,1] (by decide +kernel))
      node_2435
      node_2436
      node_2440
      (invalid_excluded a [8,6,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,8] (by decide +kernel)))

theorem node_2425 : Excluded a [8,6,5,1] :=
  branch_excluded a [8,6,5,1] (by decide)
    (fin9_cases _
      node_2426
      (invalid_excluded a [8,6,5,1,1] (by decide +kernel))
      node_2427
      node_2428
      (invalid_excluded a [8,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,6] (by decide +kernel))
      node_2433
      (invalid_excluded a [8,6,5,1,8] (by decide +kernel)))

theorem node_2441 : Excluded a [8,6,5,2] :=
  predecessor_excluded a [8,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2443 : Excluded a [8,6,5,7,0] :=
  source_excluded a [8,6,5,7,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2444 : Excluded a [8,6,5,7,1] :=
  predecessor_excluded a [8,6,5,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2445 : Excluded a [8,6,5,7,2] :=
  source_excluded a [8,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2447 : Excluded a [8,6,5,7,3,0] :=
  source_excluded a [8,6,5,7,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2448 : Excluded a [8,6,5,7,3,1] :=
  source_excluded a [8,6,5,7,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2449 : Excluded a [8,6,5,7,3,2] :=
  source_excluded a [8,6,5,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2450 : Excluded a [8,6,5,7,3,4] :=
  predecessor_excluded a [8,6,5,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2446 : Excluded a [8,6,5,7,3] :=
  branch_excluded a [8,6,5,7,3] (by decide)
    (fin9_cases _
      node_2447
      node_2448
      node_2449
      (invalid_excluded a [8,6,5,7,3,3] (by decide +kernel))
      node_2450
      (invalid_excluded a [8,6,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,3,8] (by decide +kernel)))

theorem node_2442 : Excluded a [8,6,5,7] :=
  branch_excluded a [8,6,5,7] (by decide)
    (fin9_cases _
      node_2443
      node_2444
      node_2445
      node_2446
      (invalid_excluded a [8,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,8] (by decide +kernel)))

theorem node_2405 : Excluded a [8,6,5] :=
  branch_excluded a [8,6,5] (by decide)
    (fin9_cases _
      node_2406
      node_2425
      node_2441
      (invalid_excluded a [8,6,5,3] (by decide +kernel))
      (invalid_excluded a [8,6,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,6] (by decide +kernel))
      node_2442
      (invalid_excluded a [8,6,5,8] (by decide +kernel)))

theorem node_2451 : Excluded a [8,6,7] :=
  predecessor_excluded a [8,6,7] 1 8 2 0 (by decide) (by decide +kernel)

theorem node_2324 : Excluded a [8,6] :=
  branch_excluded a [8,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0] (by decide +kernel))
      node_2325
      (invalid_excluded a [8,6,2] (by decide +kernel))
      node_2326
      node_2360
      node_2405
      (invalid_excluded a [8,6,6] (by decide +kernel))
      node_2451
      (invalid_excluded a [8,6,8] (by decide +kernel)))

theorem node_2453 : Excluded a [8,7,1] :=
  source_excluded a [8,7,1] 2 3 0 (by decide) (by decide +kernel)

theorem node_2455 : Excluded a [8,7,3,0] :=
  source_excluded a [8,7,3,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2456 : Excluded a [8,7,3,1] :=
  predecessor_excluded a [8,7,3,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_2458 : Excluded a [8,7,3,2,0] :=
  predecessor_excluded a [8,7,3,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2462 : Excluded a [8,7,3,2,1,0,4,5] :=
  predecessor_excluded a [8,7,3,2,1,0,4,5] 0 5 6 7 (by decide) (by decide +kernel)

def b_2464 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 4
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_2464 : LosingRegion (edgeOf a b_2464) 1 :=
  losingMask a b_2464 1 1269247971040090072809473
    (by decide +kernel) (by decide +kernel)

theorem node_2464 : Excluded a [8,7,3,2,1,0,4,6,5] :=
  losing_excluded a [8,7,3,2,1,0,4,6,5] (by decide) b_2464 (by decide +kernel) 5 1 2 cert_2464 (by change 5 ≠ 1 ∧ ¬ edgeOf a b_2464 5 1 ∧ 2 ≠ 5 ∧ maskRegion 1269247971040090072809473 5 2; decide +kernel)

theorem node_2463 : Excluded a [8,7,3,2,1,0,4,6] :=
  branch_excluded a [8,7,3,2,1,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,3,2,1,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,6,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,6,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,6,4] (by decide +kernel))
      node_2464
      (invalid_excluded a [8,7,3,2,1,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,6,8] (by decide +kernel)))

theorem node_2461 : Excluded a [8,7,3,2,1,0,4] :=
  branch_excluded a [8,7,3,2,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,3,2,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,4] (by decide +kernel))
      node_2462
      node_2463
      (invalid_excluded a [8,7,3,2,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,4,8] (by decide +kernel)))

def b_2467 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 5
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_2467 : LosingRegion (edgeOf a b_2467) 1 :=
  losingMask a b_2467 1 1266850002432083260080129
    (by decide +kernel) (by decide +kernel)

theorem node_2467 : Excluded a [8,7,3,2,1,0,5,4,6] :=
  losing_excluded a [8,7,3,2,1,0,5,4,6] (by decide) b_2467 (by decide +kernel) 5 1 0 cert_2467 (by change 5 ≠ 1 ∧ ¬ edgeOf a b_2467 5 1 ∧ 0 ≠ 5 ∧ maskRegion 1266850002432083260080129 5 0; decide +kernel)

theorem node_2466 : Excluded a [8,7,3,2,1,0,5,4] :=
  branch_excluded a [8,7,3,2,1,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,3,2,1,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,4,5] (by decide +kernel))
      node_2467
      (invalid_excluded a [8,7,3,2,1,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,4,8] (by decide +kernel)))

theorem node_2468 : Excluded a [8,7,3,2,1,0,5,6] :=
  predecessor_excluded a [8,7,3,2,1,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2465 : Excluded a [8,7,3,2,1,0,5] :=
  branch_excluded a [8,7,3,2,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,3,2,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,3] (by decide +kernel))
      node_2466
      (invalid_excluded a [8,7,3,2,1,0,5,5] (by decide +kernel))
      node_2468
      (invalid_excluded a [8,7,3,2,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,5,8] (by decide +kernel)))

theorem node_2460 : Excluded a [8,7,3,2,1,0] :=
  branch_excluded a [8,7,3,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,3,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,3] (by decide +kernel))
      node_2461
      node_2465
      (invalid_excluded a [8,7,3,2,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,0,8] (by decide +kernel)))

theorem node_2470 : Excluded a [8,7,3,2,1,4,0] :=
  predecessor_excluded a [8,7,3,2,1,4,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2471 : Excluded a [8,7,3,2,1,4,5] :=
  predecessor_excluded a [8,7,3,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2469 : Excluded a [8,7,3,2,1,4] :=
  branch_excluded a [8,7,3,2,1,4] (by decide)
    (fin9_cases _
      node_2470
      (invalid_excluded a [8,7,3,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,4,4] (by decide +kernel))
      node_2471
      (invalid_excluded a [8,7,3,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,4,8] (by decide +kernel)))

theorem node_2459 : Excluded a [8,7,3,2,1] :=
  branch_excluded a [8,7,3,2,1] (by decide)
    (fin9_cases _
      node_2460
      (invalid_excluded a [8,7,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,3] (by decide +kernel))
      node_2469
      (invalid_excluded a [8,7,3,2,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,1,8] (by decide +kernel)))

theorem node_2472 : Excluded a [8,7,3,2,6] :=
  source_excluded a [8,7,3,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2457 : Excluded a [8,7,3,2] :=
  branch_excluded a [8,7,3,2] (by decide)
    (fin9_cases _
      node_2458
      node_2459
      (invalid_excluded a [8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,4] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,5] (by decide +kernel))
      node_2472
      (invalid_excluded a [8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,2,8] (by decide +kernel)))

theorem node_2473 : Excluded a [8,7,3,5] :=
  source_excluded a [8,7,3,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2476 : Excluded a [8,7,3,6,0,1] :=
  predecessor_excluded a [8,7,3,6,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_2478 : Excluded a [8,7,3,6,0,2,1] :=
  source_excluded a [8,7,3,6,0,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_2479 : Excluded a [8,7,3,6,0,2,4] :=
  source_excluded a [8,7,3,6,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2480 : Excluded a [8,7,3,6,0,2,5] :=
  predecessor_excluded a [8,7,3,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2477 : Excluded a [8,7,3,6,0,2] :=
  branch_excluded a [8,7,3,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,3,6,0,2,0] (by decide +kernel))
      node_2478
      (invalid_excluded a [8,7,3,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,0,2,3] (by decide +kernel))
      node_2479
      node_2480
      (invalid_excluded a [8,7,3,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,0,2,8] (by decide +kernel)))

theorem node_2481 : Excluded a [8,7,3,6,0,4] :=
  source_excluded a [8,7,3,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2475 : Excluded a [8,7,3,6,0] :=
  branch_excluded a [8,7,3,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,3,6,0,0] (by decide +kernel))
      node_2476
      node_2477
      (invalid_excluded a [8,7,3,6,0,3] (by decide +kernel))
      node_2481
      (invalid_excluded a [8,7,3,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,0,8] (by decide +kernel)))

theorem node_2484 : Excluded a [8,7,3,6,1,0,2] :=
  source_excluded a [8,7,3,6,1,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2485 : Excluded a [8,7,3,6,1,0,4] :=
  source_excluded a [8,7,3,6,1,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2486 : Excluded a [8,7,3,6,1,0,5] :=
  predecessor_excluded a [8,7,3,6,1,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2483 : Excluded a [8,7,3,6,1,0] :=
  branch_excluded a [8,7,3,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,3,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,1,0,1] (by decide +kernel))
      node_2484
      (invalid_excluded a [8,7,3,6,1,0,3] (by decide +kernel))
      node_2485
      node_2486
      (invalid_excluded a [8,7,3,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,1,0,8] (by decide +kernel)))

theorem node_2487 : Excluded a [8,7,3,6,1,2] :=
  predecessor_excluded a [8,7,3,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2488 : Excluded a [8,7,3,6,1,4] :=
  source_excluded a [8,7,3,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2482 : Excluded a [8,7,3,6,1] :=
  branch_excluded a [8,7,3,6,1] (by decide)
    (fin9_cases _
      node_2483
      (invalid_excluded a [8,7,3,6,1,1] (by decide +kernel))
      node_2487
      (invalid_excluded a [8,7,3,6,1,3] (by decide +kernel))
      node_2488
      (invalid_excluded a [8,7,3,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,1,8] (by decide +kernel)))

theorem node_2490 : Excluded a [8,7,3,6,2,0] :=
  predecessor_excluded a [8,7,3,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_2491 : Excluded a [8,7,3,6,2,1] :=
  predecessor_excluded a [8,7,3,6,2,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_2492 : Excluded a [8,7,3,6,2,4] :=
  source_excluded a [8,7,3,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2489 : Excluded a [8,7,3,6,2] :=
  branch_excluded a [8,7,3,6,2] (by decide)
    (fin9_cases _
      node_2490
      node_2491
      (invalid_excluded a [8,7,3,6,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,2,3] (by decide +kernel))
      node_2492
      (invalid_excluded a [8,7,3,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,2,8] (by decide +kernel)))

theorem node_2474 : Excluded a [8,7,3,6] :=
  branch_excluded a [8,7,3,6] (by decide)
    (fin9_cases _
      node_2475
      node_2482
      node_2489
      (invalid_excluded a [8,7,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,6,8] (by decide +kernel)))

theorem node_2454 : Excluded a [8,7,3] :=
  branch_excluded a [8,7,3] (by decide)
    (fin9_cases _
      node_2455
      node_2456
      node_2457
      (invalid_excluded a [8,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,3,4] (by decide +kernel))
      node_2473
      node_2474
      (invalid_excluded a [8,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,3,8] (by decide +kernel)))

theorem node_2494 : Excluded a [8,7,4,0] :=
  source_excluded a [8,7,4,0] 2 1 3 (by decide) (by decide +kernel)

theorem node_2496 : Excluded a [8,7,4,1,0] :=
  source_excluded a [8,7,4,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2497 : Excluded a [8,7,4,1,2] :=
  predecessor_excluded a [8,7,4,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2500 : Excluded a [8,7,4,1,3,0,2] :=
  source_excluded a [8,7,4,1,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2502 : Excluded a [8,7,4,1,3,0,5,2] :=
  source_excluded a [8,7,4,1,3,0,5,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_2503 : Excluded a [8,7,4,1,3,0,5,6] :=
  predecessor_excluded a [8,7,4,1,3,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2501 : Excluded a [8,7,4,1,3,0,5] :=
  branch_excluded a [8,7,4,1,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,4,1,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,0,5,1] (by decide +kernel))
      node_2502
      (invalid_excluded a [8,7,4,1,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,0,5,5] (by decide +kernel))
      node_2503
      (invalid_excluded a [8,7,4,1,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,0,5,8] (by decide +kernel)))

theorem node_2499 : Excluded a [8,7,4,1,3,0] :=
  branch_excluded a [8,7,4,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,4,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,0,1] (by decide +kernel))
      node_2500
      (invalid_excluded a [8,7,4,1,3,0,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,0,4] (by decide +kernel))
      node_2501
      (invalid_excluded a [8,7,4,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,0,8] (by decide +kernel)))

theorem node_2505 : Excluded a [8,7,4,1,3,2,0] :=
  predecessor_excluded a [8,7,4,1,3,2,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2507 : Excluded a [8,7,4,1,3,2,5,0] :=
  source_excluded a [8,7,4,1,3,2,5,0] 7 1 0 (by decide) (by decide +kernel)

theorem node_2508 : Excluded a [8,7,4,1,3,2,5,6] :=
  predecessor_excluded a [8,7,4,1,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2506 : Excluded a [8,7,4,1,3,2,5] :=
  branch_excluded a [8,7,4,1,3,2,5] (by decide)
    (fin9_cases _
      node_2507
      (invalid_excluded a [8,7,4,1,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,5,5] (by decide +kernel))
      node_2508
      (invalid_excluded a [8,7,4,1,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,5,8] (by decide +kernel)))

theorem node_2504 : Excluded a [8,7,4,1,3,2] :=
  branch_excluded a [8,7,4,1,3,2] (by decide)
    (fin9_cases _
      node_2505
      (invalid_excluded a [8,7,4,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,4] (by decide +kernel))
      node_2506
      (invalid_excluded a [8,7,4,1,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,2,8] (by decide +kernel)))

theorem node_2498 : Excluded a [8,7,4,1,3] :=
  branch_excluded a [8,7,4,1,3] (by decide)
    (fin9_cases _
      node_2499
      (invalid_excluded a [8,7,4,1,3,1] (by decide +kernel))
      node_2504
      (invalid_excluded a [8,7,4,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,3,8] (by decide +kernel)))

theorem node_2509 : Excluded a [8,7,4,1,6] :=
  source_excluded a [8,7,4,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2495 : Excluded a [8,7,4,1] :=
  branch_excluded a [8,7,4,1] (by decide)
    (fin9_cases _
      node_2496
      (invalid_excluded a [8,7,4,1,1] (by decide +kernel))
      node_2497
      node_2498
      (invalid_excluded a [8,7,4,1,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,5] (by decide +kernel))
      node_2509
      (invalid_excluded a [8,7,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,1,8] (by decide +kernel)))

theorem node_2510 : Excluded a [8,7,4,2] :=
  source_excluded a [8,7,4,2] 3 0 2 (by decide) (by decide +kernel)

theorem node_2511 : Excluded a [8,7,4,5] :=
  source_excluded a [8,7,4,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2513 : Excluded a [8,7,4,6,0] :=
  source_excluded a [8,7,4,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2514 : Excluded a [8,7,4,6,1] :=
  predecessor_excluded a [8,7,4,6,1] 3 1 2 4 (by decide) (by decide +kernel)

theorem node_2516 : Excluded a [8,7,4,6,2,0] :=
  predecessor_excluded a [8,7,4,6,2,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_2517 : Excluded a [8,7,4,6,2,1] :=
  predecessor_excluded a [8,7,4,6,2,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_2518 : Excluded a [8,7,4,6,2,3] :=
  source_excluded a [8,7,4,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2515 : Excluded a [8,7,4,6,2] :=
  branch_excluded a [8,7,4,6,2] (by decide)
    (fin9_cases _
      node_2516
      node_2517
      (invalid_excluded a [8,7,4,6,2,2] (by decide +kernel))
      node_2518
      (invalid_excluded a [8,7,4,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,2,8] (by decide +kernel)))

theorem node_2519 : Excluded a [8,7,4,6,3] :=
  predecessor_excluded a [8,7,4,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2512 : Excluded a [8,7,4,6] :=
  branch_excluded a [8,7,4,6] (by decide)
    (fin9_cases _
      node_2513
      node_2514
      node_2515
      node_2519
      (invalid_excluded a [8,7,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,6,8] (by decide +kernel)))

theorem node_2493 : Excluded a [8,7,4] :=
  branch_excluded a [8,7,4] (by decide)
    (fin9_cases _
      node_2494
      node_2495
      node_2510
      (invalid_excluded a [8,7,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,4,4] (by decide +kernel))
      node_2511
      node_2512
      (invalid_excluded a [8,7,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,4,8] (by decide +kernel)))

theorem node_2522 : Excluded a [8,7,5,0,1] :=
  predecessor_excluded a [8,7,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2523 : Excluded a [8,7,5,0,2] :=
  source_excluded a [8,7,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2525 : Excluded a [8,7,5,0,3,1] :=
  predecessor_excluded a [8,7,5,0,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_2527 : Excluded a [8,7,5,0,3,2,1] :=
  source_excluded a [8,7,5,0,3,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_2529 : Excluded a [8,7,5,0,3,2,4,1] :=
  source_excluded a [8,7,5,0,3,2,4,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2531 : Excluded a [8,7,5,0,3,2,4,6,1] :=
  source_excluded a [8,7,5,0,3,2,4,6,1] 0 2 8 (by decide) (by decide +kernel)

theorem node_2530 : Excluded a [8,7,5,0,3,2,4,6] :=
  branch_excluded a [8,7,5,0,3,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,0,3,2,4,6,0] (by decide +kernel))
      node_2531
      (invalid_excluded a [8,7,5,0,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,6,8] (by decide +kernel)))

theorem node_2528 : Excluded a [8,7,5,0,3,2,4] :=
  branch_excluded a [8,7,5,0,3,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,0,3,2,4,0] (by decide +kernel))
      node_2529
      (invalid_excluded a [8,7,5,0,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,5] (by decide +kernel))
      node_2530
      (invalid_excluded a [8,7,5,0,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,4,8] (by decide +kernel)))

theorem node_2526 : Excluded a [8,7,5,0,3,2] :=
  branch_excluded a [8,7,5,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,0,3,2,0] (by decide +kernel))
      node_2527
      (invalid_excluded a [8,7,5,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,3] (by decide +kernel))
      node_2528
      (invalid_excluded a [8,7,5,0,3,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,2,8] (by decide +kernel)))

theorem node_2532 : Excluded a [8,7,5,0,3,4] :=
  predecessor_excluded a [8,7,5,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2524 : Excluded a [8,7,5,0,3] :=
  branch_excluded a [8,7,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,0,3,0] (by decide +kernel))
      node_2525
      node_2526
      (invalid_excluded a [8,7,5,0,3,3] (by decide +kernel))
      node_2532
      (invalid_excluded a [8,7,5,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,3,8] (by decide +kernel)))

theorem node_2533 : Excluded a [8,7,5,0,6] :=
  source_excluded a [8,7,5,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2521 : Excluded a [8,7,5,0] :=
  branch_excluded a [8,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,0,0] (by decide +kernel))
      node_2522
      node_2523
      node_2524
      (invalid_excluded a [8,7,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,5] (by decide +kernel))
      node_2533
      (invalid_excluded a [8,7,5,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,8] (by decide +kernel)))

theorem node_2535 : Excluded a [8,7,5,1,0] :=
  source_excluded a [8,7,5,1,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2536 : Excluded a [8,7,5,1,2] :=
  source_excluded a [8,7,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2538 : Excluded a [8,7,5,1,3,0] :=
  source_excluded a [8,7,5,1,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2540 : Excluded a [8,7,5,1,3,2,0] :=
  predecessor_excluded a [8,7,5,1,3,2,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2542 : Excluded a [8,7,5,1,3,2,4,0] :=
  source_excluded a [8,7,5,1,3,2,4,0] 7 1 0 (by decide) (by decide +kernel)

theorem node_2544 : Excluded a [8,7,5,1,3,2,4,6,0] :=
  predecessor_excluded a [8,7,5,1,3,2,4,6,0] 2 1 8 3 (by decide) (by decide +kernel)

theorem node_2543 : Excluded a [8,7,5,1,3,2,4,6] :=
  branch_excluded a [8,7,5,1,3,2,4,6] (by decide)
    (fin9_cases _
      node_2544
      (invalid_excluded a [8,7,5,1,3,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,6,8] (by decide +kernel)))

theorem node_2541 : Excluded a [8,7,5,1,3,2,4] :=
  branch_excluded a [8,7,5,1,3,2,4] (by decide)
    (fin9_cases _
      node_2542
      (invalid_excluded a [8,7,5,1,3,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,5] (by decide +kernel))
      node_2543
      (invalid_excluded a [8,7,5,1,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,4,8] (by decide +kernel)))

theorem node_2539 : Excluded a [8,7,5,1,3,2] :=
  branch_excluded a [8,7,5,1,3,2] (by decide)
    (fin9_cases _
      node_2540
      (invalid_excluded a [8,7,5,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,3] (by decide +kernel))
      node_2541
      (invalid_excluded a [8,7,5,1,3,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,2,8] (by decide +kernel)))

theorem node_2545 : Excluded a [8,7,5,1,3,4] :=
  predecessor_excluded a [8,7,5,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2537 : Excluded a [8,7,5,1,3] :=
  branch_excluded a [8,7,5,1,3] (by decide)
    (fin9_cases _
      node_2538
      (invalid_excluded a [8,7,5,1,3,1] (by decide +kernel))
      node_2539
      (invalid_excluded a [8,7,5,1,3,3] (by decide +kernel))
      node_2545
      (invalid_excluded a [8,7,5,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,3,8] (by decide +kernel)))

theorem node_2546 : Excluded a [8,7,5,1,6] :=
  source_excluded a [8,7,5,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2534 : Excluded a [8,7,5,1] :=
  branch_excluded a [8,7,5,1] (by decide)
    (fin9_cases _
      node_2535
      (invalid_excluded a [8,7,5,1,1] (by decide +kernel))
      node_2536
      node_2537
      (invalid_excluded a [8,7,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,5] (by decide +kernel))
      node_2546
      (invalid_excluded a [8,7,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,8] (by decide +kernel)))

theorem node_2547 : Excluded a [8,7,5,2] :=
  predecessor_excluded a [8,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2549 : Excluded a [8,7,5,6,0] :=
  source_excluded a [8,7,5,6,0] 2 1 4 (by decide) (by decide +kernel)

theorem node_2551 : Excluded a [8,7,5,6,1,0] :=
  source_excluded a [8,7,5,6,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2552 : Excluded a [8,7,5,6,1,2] :=
  predecessor_excluded a [8,7,5,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2553 : Excluded a [8,7,5,6,1,3] :=
  source_excluded a [8,7,5,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2554 : Excluded a [8,7,5,6,1,4] :=
  source_excluded a [8,7,5,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2550 : Excluded a [8,7,5,6,1] :=
  branch_excluded a [8,7,5,6,1] (by decide)
    (fin9_cases _
      node_2551
      (invalid_excluded a [8,7,5,6,1,1] (by decide +kernel))
      node_2552
      node_2553
      node_2554
      (invalid_excluded a [8,7,5,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,1,8] (by decide +kernel)))

theorem node_2555 : Excluded a [8,7,5,6,2] :=
  source_excluded a [8,7,5,6,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2556 : Excluded a [8,7,5,6,3] :=
  predecessor_excluded a [8,7,5,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2548 : Excluded a [8,7,5,6] :=
  branch_excluded a [8,7,5,6] (by decide)
    (fin9_cases _
      node_2549
      node_2550
      node_2555
      node_2556
      (invalid_excluded a [8,7,5,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,6,8] (by decide +kernel)))

theorem node_2520 : Excluded a [8,7,5] :=
  branch_excluded a [8,7,5] (by decide)
    (fin9_cases _
      node_2521
      node_2534
      node_2547
      (invalid_excluded a [8,7,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,5] (by decide +kernel))
      node_2548
      (invalid_excluded a [8,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,8] (by decide +kernel)))

theorem node_2559 : Excluded a [8,7,6,0,1] :=
  predecessor_excluded a [8,7,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2560 : Excluded a [8,7,6,0,2] :=
  predecessor_excluded a [8,7,6,0,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2562 : Excluded a [8,7,6,0,3,1] :=
  predecessor_excluded a [8,7,6,0,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_2563 : Excluded a [8,7,6,0,3,2] :=
  source_excluded a [8,7,6,0,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2564 : Excluded a [8,7,6,0,3,4] :=
  predecessor_excluded a [8,7,6,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2561 : Excluded a [8,7,6,0,3] :=
  branch_excluded a [8,7,6,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,3,0] (by decide +kernel))
      node_2562
      node_2563
      (invalid_excluded a [8,7,6,0,3,3] (by decide +kernel))
      node_2564
      (invalid_excluded a [8,7,6,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,3,8] (by decide +kernel)))

theorem node_2558 : Excluded a [8,7,6,0] :=
  branch_excluded a [8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,0] (by decide +kernel))
      node_2559
      node_2560
      node_2561
      (invalid_excluded a [8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,8] (by decide +kernel)))

theorem node_2567 : Excluded a [8,7,6,1,0,2] :=
  source_excluded a [8,7,6,1,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2569 : Excluded a [8,7,6,1,0,3,2] :=
  source_excluded a [8,7,6,1,0,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2570 : Excluded a [8,7,6,1,0,3,4] :=
  predecessor_excluded a [8,7,6,1,0,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2572 : Excluded a [8,7,6,1,0,3,5,2] :=
  source_excluded a [8,7,6,1,0,3,5,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_2574 : Excluded a [8,7,6,1,0,3,5,4,2] :=
  predecessor_excluded a [8,7,6,1,0,3,5,4,2] 3 2 0 8 (by decide) (by decide +kernel)

theorem node_2573 : Excluded a [8,7,6,1,0,3,5,4] :=
  branch_excluded a [8,7,6,1,0,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,3,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,4,1] (by decide +kernel))
      node_2574
      (invalid_excluded a [8,7,6,1,0,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,4,8] (by decide +kernel)))

theorem node_2571 : Excluded a [8,7,6,1,0,3,5] :=
  branch_excluded a [8,7,6,1,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,1] (by decide +kernel))
      node_2572
      (invalid_excluded a [8,7,6,1,0,3,5,3] (by decide +kernel))
      node_2573
      (invalid_excluded a [8,7,6,1,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,5,8] (by decide +kernel)))

theorem node_2568 : Excluded a [8,7,6,1,0,3] :=
  branch_excluded a [8,7,6,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,1] (by decide +kernel))
      node_2569
      (invalid_excluded a [8,7,6,1,0,3,3] (by decide +kernel))
      node_2570
      node_2571
      (invalid_excluded a [8,7,6,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,3,8] (by decide +kernel)))

theorem node_2576 : Excluded a [8,7,6,1,0,4,2] :=
  source_excluded a [8,7,6,1,0,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2578 : Excluded a [8,7,6,1,0,4,3,2] :=
  source_excluded a [8,7,6,1,0,4,3,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_2580 : Excluded a [8,7,6,1,0,4,3,5,2] :=
  predecessor_excluded a [8,7,6,1,0,4,3,5,2] 3 2 0 8 (by decide) (by decide +kernel)

theorem node_2579 : Excluded a [8,7,6,1,0,4,3,5] :=
  branch_excluded a [8,7,6,1,0,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,4,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,5,1] (by decide +kernel))
      node_2580
      (invalid_excluded a [8,7,6,1,0,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,5,8] (by decide +kernel)))

theorem node_2577 : Excluded a [8,7,6,1,0,4,3] :=
  branch_excluded a [8,7,6,1,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,4,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,1] (by decide +kernel))
      node_2578
      (invalid_excluded a [8,7,6,1,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,4] (by decide +kernel))
      node_2579
      (invalid_excluded a [8,7,6,1,0,4,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,3,8] (by decide +kernel)))

theorem node_2581 : Excluded a [8,7,6,1,0,4,5] :=
  predecessor_excluded a [8,7,6,1,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2575 : Excluded a [8,7,6,1,0,4] :=
  branch_excluded a [8,7,6,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,1] (by decide +kernel))
      node_2576
      node_2577
      (invalid_excluded a [8,7,6,1,0,4,4] (by decide +kernel))
      node_2581
      (invalid_excluded a [8,7,6,1,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,8] (by decide +kernel)))

theorem node_2566 : Excluded a [8,7,6,1,0] :=
  branch_excluded a [8,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,1] (by decide +kernel))
      node_2567
      node_2568
      node_2575
      (invalid_excluded a [8,7,6,1,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,8] (by decide +kernel)))

theorem node_2582 : Excluded a [8,7,6,1,2] :=
  predecessor_excluded a [8,7,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2584 : Excluded a [8,7,6,1,3,0] :=
  source_excluded a [8,7,6,1,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2585 : Excluded a [8,7,6,1,3,2] :=
  source_excluded a [8,7,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2586 : Excluded a [8,7,6,1,3,4] :=
  predecessor_excluded a [8,7,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2583 : Excluded a [8,7,6,1,3] :=
  branch_excluded a [8,7,6,1,3] (by decide)
    (fin9_cases _
      node_2584
      (invalid_excluded a [8,7,6,1,3,1] (by decide +kernel))
      node_2585
      (invalid_excluded a [8,7,6,1,3,3] (by decide +kernel))
      node_2586
      (invalid_excluded a [8,7,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,8] (by decide +kernel)))

theorem node_2565 : Excluded a [8,7,6,1] :=
  branch_excluded a [8,7,6,1] (by decide)
    (fin9_cases _
      node_2566
      (invalid_excluded a [8,7,6,1,1] (by decide +kernel))
      node_2582
      node_2583
      (invalid_excluded a [8,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,8] (by decide +kernel)))

theorem node_2588 : Excluded a [8,7,6,2,0] :=
  predecessor_excluded a [8,7,6,2,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2590 : Excluded a [8,7,6,2,1,0] :=
  source_excluded a [8,7,6,2,1,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2592 : Excluded a [8,7,6,2,1,3,0] :=
  source_excluded a [8,7,6,2,1,3,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_2593 : Excluded a [8,7,6,2,1,3,4] :=
  predecessor_excluded a [8,7,6,2,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2595 : Excluded a [8,7,6,2,1,3,5,0] :=
  source_excluded a [8,7,6,2,1,3,5,0] 7 1 0 (by decide) (by decide +kernel)

def b_2597 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 5
  | 7 => 4
  | 8 => 0
  | _ => 0

def cert_2597 : LosingRegion (edgeOf a b_2597) 0 :=
  losingMask a b_2597 0 1212485025626086957911040
    (by decide +kernel) (by decide +kernel)

theorem node_2597 : Excluded a [8,7,6,2,1,3,5,4,0] :=
  losing_excluded a [8,7,6,2,1,3,5,4,0] (by decide) b_2597 (by decide +kernel) 1 0 2 cert_2597 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2597 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212485025626086957911040 1 2; decide +kernel)

theorem node_2596 : Excluded a [8,7,6,2,1,3,5,4] :=
  branch_excluded a [8,7,6,2,1,3,5,4] (by decide)
    (fin9_cases _
      node_2597
      (invalid_excluded a [8,7,6,2,1,3,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,4,8] (by decide +kernel)))

theorem node_2594 : Excluded a [8,7,6,2,1,3,5] :=
  branch_excluded a [8,7,6,2,1,3,5] (by decide)
    (fin9_cases _
      node_2595
      (invalid_excluded a [8,7,6,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,3] (by decide +kernel))
      node_2596
      (invalid_excluded a [8,7,6,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,5,8] (by decide +kernel)))

theorem node_2591 : Excluded a [8,7,6,2,1,3] :=
  branch_excluded a [8,7,6,2,1,3] (by decide)
    (fin9_cases _
      node_2592
      (invalid_excluded a [8,7,6,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,3] (by decide +kernel))
      node_2593
      node_2594
      (invalid_excluded a [8,7,6,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,3,8] (by decide +kernel)))

theorem node_2599 : Excluded a [8,7,6,2,1,4,0] :=
  source_excluded a [8,7,6,2,1,4,0] 2 1 6 (by decide) (by decide +kernel)

theorem node_2601 : Excluded a [8,7,6,2,1,4,3,0] :=
  source_excluded a [8,7,6,2,1,4,3,0] 7 1 0 (by decide) (by decide +kernel)

def b_2603 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 2
  | 4 => 1
  | 5 => 4
  | 6 => 3
  | 7 => 5
  | 8 => 0
  | _ => 0

def cert_2603 : LosingRegion (edgeOf a b_2603) 0 :=
  losingMask a b_2603 0 1212482722034877557902336
    (by decide +kernel) (by decide +kernel)

theorem node_2603 : Excluded a [8,7,6,2,1,4,3,5,0] :=
  losing_excluded a [8,7,6,2,1,4,3,5,0] (by decide) b_2603 (by decide +kernel) 1 0 2 cert_2603 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2603 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212482722034877557902336 1 2; decide +kernel)

theorem node_2602 : Excluded a [8,7,6,2,1,4,3,5] :=
  branch_excluded a [8,7,6,2,1,4,3,5] (by decide)
    (fin9_cases _
      node_2603
      (invalid_excluded a [8,7,6,2,1,4,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,5,8] (by decide +kernel)))

theorem node_2600 : Excluded a [8,7,6,2,1,4,3] :=
  branch_excluded a [8,7,6,2,1,4,3] (by decide)
    (fin9_cases _
      node_2601
      (invalid_excluded a [8,7,6,2,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,4] (by decide +kernel))
      node_2602
      (invalid_excluded a [8,7,6,2,1,4,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,3,8] (by decide +kernel)))

theorem node_2604 : Excluded a [8,7,6,2,1,4,5] :=
  predecessor_excluded a [8,7,6,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2598 : Excluded a [8,7,6,2,1,4] :=
  branch_excluded a [8,7,6,2,1,4] (by decide)
    (fin9_cases _
      node_2599
      (invalid_excluded a [8,7,6,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,2] (by decide +kernel))
      node_2600
      (invalid_excluded a [8,7,6,2,1,4,4] (by decide +kernel))
      node_2604
      (invalid_excluded a [8,7,6,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,8] (by decide +kernel)))

theorem node_2589 : Excluded a [8,7,6,2,1] :=
  branch_excluded a [8,7,6,2,1] (by decide)
    (fin9_cases _
      node_2590
      (invalid_excluded a [8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,2] (by decide +kernel))
      node_2591
      node_2598
      (invalid_excluded a [8,7,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,8] (by decide +kernel)))

theorem node_2606 : Excluded a [8,7,6,2,3,0] :=
  source_excluded a [8,7,6,2,3,0] 2 1 5 (by decide) (by decide +kernel)

theorem node_2607 : Excluded a [8,7,6,2,3,1] :=
  predecessor_excluded a [8,7,6,2,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_2608 : Excluded a [8,7,6,2,3,4] :=
  predecessor_excluded a [8,7,6,2,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2605 : Excluded a [8,7,6,2,3] :=
  branch_excluded a [8,7,6,2,3] (by decide)
    (fin9_cases _
      node_2606
      node_2607
      (invalid_excluded a [8,7,6,2,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,3,3] (by decide +kernel))
      node_2608
      (invalid_excluded a [8,7,6,2,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,3,8] (by decide +kernel)))

theorem node_2587 : Excluded a [8,7,6,2] :=
  branch_excluded a [8,7,6,2] (by decide)
    (fin9_cases _
      node_2588
      node_2589
      (invalid_excluded a [8,7,6,2,2] (by decide +kernel))
      node_2605
      (invalid_excluded a [8,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,8] (by decide +kernel)))

theorem node_2609 : Excluded a [8,7,6,5] :=
  source_excluded a [8,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2557 : Excluded a [8,7,6] :=
  branch_excluded a [8,7,6] (by decide)
    (fin9_cases _
      node_2558
      node_2565
      node_2587
      (invalid_excluded a [8,7,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,4] (by decide +kernel))
      node_2609
      (invalid_excluded a [8,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,8] (by decide +kernel)))

theorem node_2452 : Excluded a [8,7] :=
  branch_excluded a [8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0] (by decide +kernel))
      node_2453
      (invalid_excluded a [8,7,2] (by decide +kernel))
      node_2454
      node_2493
      node_2520
      node_2557
      (invalid_excluded a [8,7,7] (by decide +kernel))
      (invalid_excluded a [8,7,8] (by decide +kernel)))

theorem node_2176 : Excluded a [8] :=
  branch_excluded a [8] (by decide)
    (fin9_cases _
      node_2177
      (invalid_excluded a [8,1] (by decide +kernel))
      (invalid_excluded a [8,2] (by decide +kernel))
      node_2178
      node_2179
      node_2261
      node_2324
      node_2452
      (invalid_excluded a [8,8] (by decide +kernel)))

theorem node_1 : Excluded a [] :=
  branch_excluded a [] (by decide)
    (fin9_cases _
      (invalid_excluded a [0] (by decide +kernel))
      (invalid_excluded a [1] (by decide +kernel))
      node_2
      node_3
      node_431
      node_816
      node_1265
      node_1724
      node_2176)

theorem every_second_factor_blocked (b : Assignment 9) (valid : Valid a b) : Blocked a b :=
  node_1 b valid (by intro i h; simp at h)

theorem primary_loopless : ∀ i : Fin 9, a i ≠ i := by decide +kernel

#print axioms every_second_factor_blocked
end Delivery.FiniteExclusion.Cycle3x6
