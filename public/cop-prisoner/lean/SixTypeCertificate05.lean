import SixTypeObjective05Transfer
import SixTypeObjective05Delivery0
import SixTypeObjective05Delivery1
import SixTypeObjective05Delivery2
import SixTypeObjective05Delivery3
import SixTypeObjective05Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate05
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern05.pattern := by
  constructor
  · exact ⟨SixTypeObjective05Transfer.data, SixTypeObjective05Transfer.checked, SixTypeObjective05Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective05Delivery0.data, SixTypeObjective05Delivery0.checked, SixTypeObjective05Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective05Delivery1.data, SixTypeObjective05Delivery1.checked, SixTypeObjective05Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective05Delivery2.data, SixTypeObjective05Delivery2.checked, SixTypeObjective05Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective05Delivery3.data, SixTypeObjective05Delivery3.checked, SixTypeObjective05Delivery3.initial_states⟩
    · simp [SixTypePattern05.pattern] at present
    · exact ⟨SixTypeObjective05Delivery5.data, SixTypeObjective05Delivery5.checked, SixTypeObjective05Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate05
