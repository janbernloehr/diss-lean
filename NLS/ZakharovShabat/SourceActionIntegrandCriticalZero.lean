import NLS.ZakharovShabat.SourceLemma11_1
import NLS.ZakharovShabat.CanonicalCriticalInterlacing
import NLS.ZakharovShabat.RealGapDiscriminantLevels

/-!
# The critical-point zero in the recentered real action integrand

The integrand displayed in the proof of Lemma 11.1 vanishes at the
canonical critical point, strictly inside any open real gap. Its square-root
denominator is positive there. This corrects the proof's pointwise strictness
claim without changing the already proved strict positivity of the action.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real integrand in the second displayed action formula on printed p.61,
before the positive outer factor 2/pi. -/
def sourceRecenteredRealActionIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^(n+1) *
    (x-(canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) *
    (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x : ℂ)).re /
    Real.sqrt ((canonicalDiscriminant hp (periodOnePotential ψ) (x : ℂ)).re^2-4)

/-- The recentering factor vanishes at the actual critical coordinate. -/
@[simp] theorem sourceRecenteredRealActionIntegrand_at_critical
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    sourceRecenteredRealActionIntegrand hp hp1 ψ n
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re = 0 := by
  simp only [sourceRecenteredRealActionIntegrand,sub_self,mul_zero,zero_mul,zero_div]

/-- The displayed denominator is strictly positive throughout an open real gap. -/
theorem sourceRecenteredRealActionIntegrand_denominator_pos
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    0 < Real.sqrt ((canonicalDiscriminant hp (periodOnePotential ψ) (x : ℂ)).re^2-4) := by
  have hreal' := isRealType_periodOnePotential ψ hreal
  have hgt := two_lt_norm_discriminant_of_mem_canonicalGap_interior
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) hreal' n x hx
  have hsq := norm_canonicalDiscriminant_sq_of_realType
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) hreal' x
  apply Real.sqrt_pos.mpr
  nlinarith

/-- Every open real gap has an interior zero of the literal integrand, with a
strictly positive denominator; this is not an endpoint or a totalized quotient. -/
theorem sourceRecenteredRealActionIntegrand_has_interior_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    ∃ x : ℝ, x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re ∧
      0 < Real.sqrt ((canonicalDiscriminant hp (periodOnePotential ψ) (x : ℂ)).re^2-4) ∧
      sourceRecenteredRealActionIntegrand hp hp1 ψ n x = 0 := by
  have hc := canonicalCriticalPoints_between_of_open_gap hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n hopen
  exact ⟨_,hc,sourceRecenteredRealActionIntegrand_denominator_pos hp hp1 ψ hreal n _ hc,
    sourceRecenteredRealActionIntegrand_at_critical hp hp1 ψ n⟩

/-- The pointwise strict-positivity sentence in the proof of Lemma 11.1 fails
on every open real gap, although the action itself is strictly positive. -/
theorem not_sourceRecenteredRealActionIntegrand_pos_everywhere
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    ¬∀ x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re,
        0 < sourceRecenteredRealActionIntegrand hp hp1 ψ n x := by
  obtain ⟨x,hx,_,hz⟩ := sourceRecenteredRealActionIntegrand_has_interior_zero hp hp1 ψ hreal n hopen
  intro h
  have hpos := h x hx
  rw [hz] at hpos
  exact lt_irrefl 0 hpos

/-- The action remains strictly positive while the displayed integrand has an
interior zero. The existing Lemma 11.1 domain and action are unchanged. -/
theorem SourceLemma11_1Data.action_pos_and_recenteredIntegrand_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    0 < (sourceIndexedAction hp hp1 n ψ).re ∧
      sourceRecenteredRealActionIntegrand hp hp1 ψ n
        (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re = 0 := by
  refine ⟨H.action_pos_of_real_gap_ne_zero ψ hreal n ?_,
    sourceRecenteredRealActionIntegrand_at_critical hp hp1 ψ n⟩
  intro hg
  have he := sub_eq_zero.mp hg
  have hre := congrArg Complex.re he
  exact (ne_of_lt hopen) hre.symm

end NLS.ZakharovShabat
