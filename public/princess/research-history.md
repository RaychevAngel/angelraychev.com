# Mathematical research history and current proof boundaries

## Original work

Angel Ivanov Raychev's path research took place between October 2019 and
March 2020. Two Bulgarian conference manuscripts preserve the results.
The joint student manuscript is cited under Angel Raychev and Dimitar Rusev;
the spring manuscript is cited under Angel Raychev. The combined manuscript
acknowledges Rusev's writing of the preliminary monotonicity section, by
agreement, and thanks Dimitar Dimitrov for his mentorship.

The present investigation reconstructed the intended path formula, restored
the missing single-probe restriction in a printed statement, and recovered
the exceptional residue case. The new indexed strategy compresses the earlier
construction cases. These are reconstructions of the author's earlier result,
with new proof organization, not a reassignment of its original credit.

## September 2026 investigation

Work developed with substantial assistance from Astra 6 through the Codex
harness. The full working log and original documents are preserved locally;
this public record summarizes the mathematics and its evidence.

- Reconstructed and independently attacked the complete path theorem.
- Proved a complete two-row formula by projecting each initial-color cohort
  to a closed-neighborhood path process.
- Proved all-budget three-row and four-row formulas. Critical low-expansion
  states require either a history bit or a relaxation allowing free holding;
  unrestricted interleaving is included in the lower arguments.
- Proved an abstract theorem compressing entire strategies, with unchanged
  daily budgets, and concrete odd-path and square-fiber applications.
- Derived explicit minimum open-neighborhood profiles for all odd rectangles.
  The correct tie order fills the shorter coordinate first within a layer.
- Proved isoperimetric nesting on every odd-sided box in every dimension.
  A linear neighborhood-cost identity and a terminal-coordinate exchange
  lemma complete an induction on dimension. Two independent proof reviews
  checked the arbitrary-dimensional argument.
- Proved the five-row, three-probe formula `T=10n−20` for every `n≥5`.
  The even case uses a finite symbolic column automaton with arbitrary
  empty/full pumping lengths; it is not a finite-length extrapolation.
- Classified every budget on the 3×3×3 box, including exact time. The entire
  table has a Lean proof using arbitrary-support neighborhood bounds and
  concrete physical schedules.
- Proved a height strategy for arbitrary bipartite cylinders. Together with
  the cube obstruction it gives exactly five probes for every 3×3×n box,
  `n≥3`. For odd lengths, five probes take exactly `18n−36` days,
  proved by an independently checked interval-insertion certificate.
- Proved every budget on even-length five-row boards. A history-dependent
  potential, a separate four-probe equality obstruction, and three finite
  high-budget checks complete the endpoint cases.
- Proved `T=2wn−C(w)` at the minimum budget for widths 3,5,…,15 and every
  odd length at least the width. Exact rational certificates extend to
  unbounded lengths by a proved interval-insertion theorem.
- Proved eventual periodic affine capture time for every fixed feasible
  budget and every fixed all-odd cross-section in arbitrary dimension.
  An explicit threshold and finite base computations determine the entire
  later sequence. The minimum-budget case is eventually linear.
- Derived an exact transfer recurrence for neighborhood profiles on cylinders
  of either parity, from compatible transverse profiles. This is not a
  proof of compatible global minimizers or exact capture time on even cylinders.

- The final bounded attack resolved `T₅(3×3×4)=36`. Transverse compression
  gives eight counts; two independent exhaustive implementations agree,
  and the36-day schedule replays on actual rooms. This is a finite
  computer-assisted theorem, not a new complete Lean classification.

## Failed approaches and corrections worth retaining

1. Open-neighborhood parity nesting fails on even rectangles. A classical
   closed-neighborhood grid theorem cannot simply be quoted for that claim.
2. Using one fixed sweep orientation for both cohorts can lose a day:
   the 3×6 board with five probes needs four days, whereas that restriction
   can take five. Independent orientations repair the construction.
3. Applying the square diagonal compression unchanged to unequal rectangles
   can enlarge the neighborhood and worsen minimum time.
4. Row-interval restrictions fail for some partial starting states. A six-room
   partial state on 3×5 with four probes can require a hole in a surviving row
   to attain the optimum. Full-board normal forms need their own proof.
5. A reversed reflection instruction in an early manuscript paragraph was
   corrected against the verified path construction: on an even path the
   second cohort is reflected when its starting inspection day is odd.
6. A polynomial fitted to the first four minimum-budget width constants
   fails at larger widths. Exact certificates replace that extrapolation.
7. A middle plateau alone does not prove stable endpoint behavior. The
   cylinder theorem requires explicit corner tables and separate empty-set
   treatment; the two parity groups also require their own contraction cuts.
8. Abstract dual profiles alone do not justify finishing one cohort before
   working on the other. A general serial-strategy theorem is still open here.

## Verification boundary

The complete physical path, two-row, and 3×3×3 classifications are verified
in Lean 4.33.1. The public source-specific receipt records the current
module count, hashes, and fresh single-worker build. The abstract compression
theorem and generic bipartite profile duality are also checked. Selected
five-row scalar potentials, row-deficit implications, four-probe equality
lemmas, and finite high-budget bounds are checked; their complete geometry
and the potential for budgets at least five remain ordinary proofs.

The remaining uniform theorems currently have ordinary mathematical proofs
and independent reviews. Exact algorithms are distinguished from closed
formulas. Finite experiments are recorded as evidence, never as proofs of
unbounded parameter claims.

Literature credit includes Britnell–Wildon, Kamenetsky's 2018 OEIS conjectures,
Abramovskaya–Fomin–Golovach–Pilipczuk, Körner–Wei, Bolkema–Groothuis, and the
classical grid isoperimetric literature. New derivations in this investigation
do not by themselves establish priority over all previous literature.

## Remaining target

Resolve arbitrary even-sided boxes outside the completed families, simplify
the exact recurrences into useful formulas where possible, and extend the
formal proof coverage. The current manuscript is a research draft; it has
not been submitted to arXiv.
