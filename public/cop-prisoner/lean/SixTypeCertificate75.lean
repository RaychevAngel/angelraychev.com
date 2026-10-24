import SixTypeObjective75Transfer
import SixTypeObjective75Delivery0
import SixTypeObjective75Delivery1
import SixTypeObjective75Delivery2
import SixTypeObjective75Delivery3
import SixTypeObjective75Delivery4
import SixTypeObjective75Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate75
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern75.pattern := by
  constructor
  · exact ⟨SixTypeObjective75Transfer.data, SixTypeObjective75Transfer.checked, SixTypeObjective75Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective75Delivery0.data, SixTypeObjective75Delivery0.checked, SixTypeObjective75Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective75Delivery1.data, SixTypeObjective75Delivery1.checked, SixTypeObjective75Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective75Delivery2.data, SixTypeObjective75Delivery2.checked, SixTypeObjective75Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective75Delivery3.data, SixTypeObjective75Delivery3.checked, SixTypeObjective75Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective75Delivery4.data, SixTypeObjective75Delivery4.checked, SixTypeObjective75Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective75Delivery5.data, SixTypeObjective75Delivery5.checked, SixTypeObjective75Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate75
