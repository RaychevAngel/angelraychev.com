import SixTypeObjective21Transfer
import SixTypeObjective21Delivery0
import SixTypeObjective21Delivery1
import SixTypeObjective21Delivery2
import SixTypeObjective21Delivery3
import SixTypeObjective21Delivery4
import SixTypeObjective21Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate21
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern21.pattern := by
  constructor
  · exact ⟨SixTypeObjective21Transfer.data, SixTypeObjective21Transfer.checked, SixTypeObjective21Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective21Delivery0.data, SixTypeObjective21Delivery0.checked, SixTypeObjective21Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective21Delivery1.data, SixTypeObjective21Delivery1.checked, SixTypeObjective21Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective21Delivery2.data, SixTypeObjective21Delivery2.checked, SixTypeObjective21Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective21Delivery3.data, SixTypeObjective21Delivery3.checked, SixTypeObjective21Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective21Delivery4.data, SixTypeObjective21Delivery4.checked, SixTypeObjective21Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective21Delivery5.data, SixTypeObjective21Delivery5.checked, SixTypeObjective21Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate21
