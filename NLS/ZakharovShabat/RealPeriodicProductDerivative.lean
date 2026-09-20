import NLS.ZakharovShabat.RealCentralDerivative
import NLS.ZakharovShabat.CanonicalPeriodicProduct
import NLS.ComplexAnalysis.NonvanishingLocallyUniformLimit
import NLS.ComplexAnalysis.AnalyticZeroCount

/-!
# Reality of critical points of the full canonical product

The full product has a spectral zero and is nonzero at i, so its derivative
is nontrivial. Locally uniform convergence of central polynomial derivatives
and Gauss–Lucas exclude every nonreal critical point of the limit.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full canonical product of a real-type potential has a nontrivial derivative. -/
theorem exists_canonicalPeriodic_derivative_ne_zero_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : IsRealType φ) : ∃ z : ℂ, deriv (canonicalPeriodicProduct hp φ) z ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_cutoff_positive_central_multiplicity hp φ
  obtain ⟨a, ha, _⟩ := hN N le_rfl
  have ha0 : canonicalPeriodicProduct hp φ a = 0 :=
    (canonicalPeriodicProduct_eq_zero_iff hp hp1 φ a).mpr ((mem_centralPeriodicSpectrum hp φ N a).mp ha).1
  have hi0 : canonicalPeriodicProduct hp φ I ≠ 0 := by
    intro hi
    have him := periodicSpectrum_im_eq_zero_of_realType hp φ hφ I
      ((canonicalPeriodicProduct_eq_zero_iff hp hp1 φ I).mp hi)
    norm_num at him
  by_contra! h
  have he := is_const_of_deriv_eq_zero
    (fun z => (analyticOnNhd_canonicalPeriodicProduct hp hp1 φ z (mem_univ z)).differentiableAt) h a I
  exact hi0 (he.symm.trans ha0)

/-- The derivative of the full canonical product has finite order everywhere for real-type potentials. -/
theorem analyticOrderAt_canonicalPeriodic_derivative_ne_top_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : IsRealType φ) (z : ℂ) :
    analyticOrderAt (deriv (canonicalPeriodicProduct hp φ)) z ≠ ⊤ := by
  obtain ⟨a, ha⟩ := exists_canonicalPeriodic_derivative_ne_zero_of_realType hp hp1 φ hφ
  exact NLS.ComplexAnalysis.analyticOrderAt_ne_top_on_connected isPreconnected_univ
    (analyticOnNhd_canonicalPeriodicProduct hp hp1 φ).deriv (mem_univ a) ha (mem_univ z)

/-- No nonreal parameter is a critical point of the full canonical product of a real-type potential. -/
theorem deriv_canonicalPeriodic_ne_zero_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : IsRealType φ) {z : ℂ} (hz : z.im ≠ 0) :
    deriv (canonicalPeriodicProduct hp φ) z ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_cutoff_real_normalizedCentral_derivative hp φ hφ
  let F (n : ℕ) := deriv (normalizedCentralPeriodicPolynomial hp φ (n+N))
  have hconv : TendstoLocallyUniformlyOn F (deriv (canonicalPeriodicProduct hp φ)) atTop univ := by
    intro u hu x hx
    obtain ⟨t, ht, h⟩ := tendstoLocallyUniformlyOn_deriv_canonicalPeriodicProduct hp hp1 φ u hu x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually h⟩
  apply NLS.ComplexAnalysis.limit_ne_zero_on_open_of_finite_order F _
    (U := {w : ℂ | w.im ≠ 0}) (isOpen_ne.preimage continuous_im) hz
  · intro n w
    exact ((analyticOnNhd_normalizedCentralPeriodicPolynomial hp φ (n+N)).deriv w (mem_univ w)).differentiableAt
  · intro n w hw
    exact hN (n+N) (by omega) w hw
  · exact (analyticOnNhd_canonicalPeriodicProduct hp hp1 φ).deriv.mono (subset_univ _)
  · exact analyticOrderAt_canonicalPeriodic_derivative_ne_top_of_realType hp hp1 φ hφ z
  · exact hconv.mono (subset_univ _)

end NLS.ZakharovShabat
