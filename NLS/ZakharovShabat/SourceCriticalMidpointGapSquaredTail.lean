import NLS.ZakharovShabat.CriticalMidpointGapSquared
import NLS.ZakharovShabat.SourcePeriodicGapSummability

/-!
# The distant-index part of Lemma 10.10 in source coordinates

Lemma 8.6 gives a locally uniform squared-gap coefficient for distant
critical roots. Pulling its canonical-potential neighborhood back to
the coefficient-pair source space gives the tail required by Lemma 10.10.
The finite central indices are a separate step.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one source neighborhood, all sufficiently distant critical
roots have midpoint offset equal to the squared periodic gap times a
uniformly bounded `ℓp` coefficient sequence. -/
theorem exists_local_sourceCriticalMidpointGapSquaredTail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 0 < N ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∃ K : ℝ, 0 ≤ K ∧
          ∀ ψ ∈ V, ∃ a : Coeff p, ‖a‖ ≤ K ∧
            ∀ n : ℤ, N < n.natAbs →
              canonicalCriticalPoints hp hp1
                  (periodOnePotential ψ) (periodOnePotential_mem ψ) n -
                canonicalPeriodicMidpoint hp hp1
                  (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
                (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * a n := by
  obtain ⟨N,hN,U,hUopen,_,hφU,_,K,hK,h⟩ :=
    exists_uniform_canonicalCriticalPoints_midpoint_gap_sq hp hp1
      (periodOnePotential φ)
  let V : Set (CoeffPair p) := periodOnePotential ⁻¹' U
  refine ⟨N,hN,V,hUopen.preimage (periodOnePotential (p := p)).continuous,
    hφU,K,hK,?_⟩
  intro ψ hψ
  obtain ⟨a,ha,he⟩ := h (periodOnePotential ψ) hψ (periodOnePotential_mem ψ)
  refine ⟨a,ha,?_⟩
  intro n hn
  simpa only [sourcePeriodicGapDisplacement_apply] using he n hn

/-- A collapsed distant source gap has its critical root at the
midpoint, including for complex source potentials in the neighborhood. -/
theorem exists_local_sourceCritical_eq_midpoint_of_zeroGap_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 0 < N ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∀ ψ ∈ V, ∀ n : ℤ, N < n.natAbs →
          sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
            canonicalCriticalPoints hp hp1
                (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
              canonicalPeriodicMidpoint hp hp1
                (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  obtain ⟨N,hN,V,hVopen,hφV,K,hK,h⟩ :=
    exists_local_sourceCriticalMidpointGapSquaredTail hp hp1 φ
  refine ⟨N,hN,V,hVopen,hφV,?_⟩
  intro ψ hψ n hn hgap
  obtain ⟨a,_,ha⟩ := h ψ hψ
  have he := ha n hn
  rw [hgap] at he
  exact sub_eq_zero.mp (by simpa using he)

end NLS.ZakharovShabat
