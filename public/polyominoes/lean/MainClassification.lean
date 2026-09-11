import LClassification
import LHalfPlaneUnequal
import TClassification
import TupleNormalization

namespace PolyominoFormal

/-- Complete classification of sorted two-arm L shapes, including all
degenerate bars. Every obstruction input is an already proved theorem. -/
theorem sorted_L_classified (a b : Nat) (hab : b≤a) :
    Classified a b 0 0 (classifyL a b) :=
  sorted_L_classified_of_unequal
    (fun a b hlt hb ha => LHalfPlaneUnequal.no_halfplane a b ha hb hlt) a b hab

/-- The complete eight-capability Golomb profile of every four-arm tuple.
Arms count added cells; copies may use every lattice D4 orientation.
The underlying tiling predicates quantify over arbitrary exact tilings. -/
theorem all_tuples_classified (a b c d : Nat) :
    Classified a b c d (classifyTuple a b c d) :=
  all_tuples_of_families sorted_L_classified normalized_T_classified a b c d

#print axioms sorted_L_classified
#print axioms all_tuples_classified
end PolyominoFormal
