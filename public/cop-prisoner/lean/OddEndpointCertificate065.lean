import OddEndpointObjective065Transfer
import OddEndpointObjective065Delivery0
import OddEndpointObjective065Delivery1
import OddEndpointObjective065Delivery2
import OddEndpointObjective065Delivery3
import OddEndpointObjective065Delivery4
import OddEndpointObjective065Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate065
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern065
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective065Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective065Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective065Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective065Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective065Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective065Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective065Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate065
