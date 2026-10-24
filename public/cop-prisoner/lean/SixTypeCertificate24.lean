import SixTypeObjective24Transfer
import SixTypeObjective24Delivery0
import SixTypeObjective24Delivery1
import SixTypeObjective24Delivery2
import SixTypeObjective24Delivery3
import SixTypeObjective24Delivery4
import SixTypeObjective24Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate24
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern24.pattern := by
  constructor
  · exact ⟨SixTypeObjective24Transfer.data, SixTypeObjective24Transfer.checked, SixTypeObjective24Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective24Delivery0.data, SixTypeObjective24Delivery0.checked, SixTypeObjective24Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective24Delivery1.data, SixTypeObjective24Delivery1.checked, SixTypeObjective24Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective24Delivery2.data, SixTypeObjective24Delivery2.checked, SixTypeObjective24Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective24Delivery3.data, SixTypeObjective24Delivery3.checked, SixTypeObjective24Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective24Delivery4.data, SixTypeObjective24Delivery4.checked, SixTypeObjective24Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective24Delivery5.data, SixTypeObjective24Delivery5.checked, SixTypeObjective24Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate24
