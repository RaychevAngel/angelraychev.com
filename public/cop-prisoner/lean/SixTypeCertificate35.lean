import SixTypeObjective35Transfer
import SixTypeObjective35Delivery0
import SixTypeObjective35Delivery1
import SixTypeObjective35Delivery2
import SixTypeObjective35Delivery3
import SixTypeObjective35Delivery4
import SixTypeObjective35Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate35
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern35.pattern := by
  constructor
  · exact ⟨SixTypeObjective35Transfer.data, SixTypeObjective35Transfer.checked, SixTypeObjective35Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective35Delivery0.data, SixTypeObjective35Delivery0.checked, SixTypeObjective35Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective35Delivery1.data, SixTypeObjective35Delivery1.checked, SixTypeObjective35Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective35Delivery2.data, SixTypeObjective35Delivery2.checked, SixTypeObjective35Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective35Delivery3.data, SixTypeObjective35Delivery3.checked, SixTypeObjective35Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective35Delivery4.data, SixTypeObjective35Delivery4.checked, SixTypeObjective35Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective35Delivery5.data, SixTypeObjective35Delivery5.checked, SixTypeObjective35Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate35
