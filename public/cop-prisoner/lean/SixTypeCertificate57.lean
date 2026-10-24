import SixTypeObjective57Transfer
import SixTypeObjective57Delivery0
import SixTypeObjective57Delivery1
import SixTypeObjective57Delivery2
import SixTypeObjective57Delivery3
import SixTypeObjective57Delivery4
import SixTypeObjective57Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate57
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern57.pattern := by
  constructor
  · exact ⟨SixTypeObjective57Transfer.data, SixTypeObjective57Transfer.checked, SixTypeObjective57Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective57Delivery0.data, SixTypeObjective57Delivery0.checked, SixTypeObjective57Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective57Delivery1.data, SixTypeObjective57Delivery1.checked, SixTypeObjective57Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective57Delivery2.data, SixTypeObjective57Delivery2.checked, SixTypeObjective57Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective57Delivery3.data, SixTypeObjective57Delivery3.checked, SixTypeObjective57Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective57Delivery4.data, SixTypeObjective57Delivery4.checked, SixTypeObjective57Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective57Delivery5.data, SixTypeObjective57Delivery5.checked, SixTypeObjective57Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate57
