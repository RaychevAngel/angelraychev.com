import SixTypeObjective67Transfer
import SixTypeObjective67Delivery0
import SixTypeObjective67Delivery1
import SixTypeObjective67Delivery2
import SixTypeObjective67Delivery3
import SixTypeObjective67Delivery4
import SixTypeObjective67Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate67
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern67.pattern := by
  constructor
  · exact ⟨SixTypeObjective67Transfer.data, SixTypeObjective67Transfer.checked, SixTypeObjective67Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective67Delivery0.data, SixTypeObjective67Delivery0.checked, SixTypeObjective67Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective67Delivery1.data, SixTypeObjective67Delivery1.checked, SixTypeObjective67Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective67Delivery2.data, SixTypeObjective67Delivery2.checked, SixTypeObjective67Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective67Delivery3.data, SixTypeObjective67Delivery3.checked, SixTypeObjective67Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective67Delivery4.data, SixTypeObjective67Delivery4.checked, SixTypeObjective67Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective67Delivery5.data, SixTypeObjective67Delivery5.checked, SixTypeObjective67Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate67
