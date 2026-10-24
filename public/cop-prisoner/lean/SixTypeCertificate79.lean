import SixTypeObjective79Transfer
import SixTypeObjective79Delivery0
import SixTypeObjective79Delivery1
import SixTypeObjective79Delivery2
import SixTypeObjective79Delivery3
import SixTypeObjective79Delivery4
import SixTypeObjective79Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate79
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern79.pattern := by
  constructor
  · exact ⟨SixTypeObjective79Transfer.data, SixTypeObjective79Transfer.checked, SixTypeObjective79Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective79Delivery0.data, SixTypeObjective79Delivery0.checked, SixTypeObjective79Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective79Delivery1.data, SixTypeObjective79Delivery1.checked, SixTypeObjective79Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective79Delivery2.data, SixTypeObjective79Delivery2.checked, SixTypeObjective79Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective79Delivery3.data, SixTypeObjective79Delivery3.checked, SixTypeObjective79Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective79Delivery4.data, SixTypeObjective79Delivery4.checked, SixTypeObjective79Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective79Delivery5.data, SixTypeObjective79Delivery5.checked, SixTypeObjective79Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate79
