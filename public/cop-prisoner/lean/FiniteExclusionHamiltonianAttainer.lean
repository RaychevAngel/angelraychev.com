import FiniteExclusionThirtyNineHamiltonianBase
import SparseWitness9
namespace Delivery.FiniteExclusion.HamiltonianAttainer
open Extremal
def second (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 0
  | 2 => 8
  | 3 => 7
  | 4 => 3
  | 5 => 2
  | 6 => 1
  | 7 => 6
  | 8 => 5
  | _ => 0

def toCanonical (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 3
  | 4 => 7
  | 5 => 6
  | 6 => 2
  | 7 => 8
  | 8 => 5
  | _ => 0

def fromCanonical (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 3
  | 4 => 2
  | 5 => 8
  | 6 => 5
  | 7 => 4
  | 8 => 7
  | _ => 0


def witnessIso : GraphRelabeling.Iso SparseWitness9.edge (edgeOf Thirty9Minimum.a second) where
  toFun := toCanonical
  invFun := fromCanonical
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  edge_iff := by decide +kernel

theorem valid : Valid Thirty9Minimum.a second := by
  unfold Valid
  decide +kernel

theorem exact_score : score (edgeOf Thirty9Minimum.a second) = 30 := by
  rw [←GraphRelabeling.score_eq witnessIso]
  exact SparseWitness9.exact_score

#print axioms exact_score
end Delivery.FiniteExclusion.HamiltonianAttainer
