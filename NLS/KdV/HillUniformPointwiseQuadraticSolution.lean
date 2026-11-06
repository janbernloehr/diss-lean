import NLS.KdV.HillBoundedAnalyticQuadraticSolutions
import NLS.KdV.HillActiveRegularAnnulus

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The original quadratic primitive construction has a geometric cutoff
chosen before the numerator, active gap and numerical bound. -/
theorem exists_hillRegularGap_uniform_pointwise_quadratic_solution (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ U : Set (Coeff 2), IsOpen U →
      U ⊆ ball (0 : Coeff 2) B → ∀ G : ℂ × Coeff 2 → ℂ,
      ∀ k : ℕ, N≤k → ∀ C : ℝ, 0≤C →
      HillRegularGapAnalyticChart h0q h0r G U k C →
      ∃ H : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ H (ball (hillRealGapCenter 0 h0q h0r k : ℂ)
          (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4) ×ˢ U) ∧
        (∀ p ∈ U, ∀ E ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
          (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4),
          hillLocalGapPolynomial 0 h0q h0r k p E*deriv (fun z => H (z,p)) E+
            (E-hillLocalGapMidpoint 0 h0q h0r k p)*H (E,p)=hillComplexRegularGapNumerator h0q h0r G k (E,p)) ∧
        ∀ p ∈ U, ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4),
          ‖H (E,p)‖ ≤ 36*Real.pi*C/(k : ℝ)^3 := by
  obtain ⟨Nq,hNq,hquadratic⟩ := exists_hillFreeGap_bounded_complex_quadratic_root_chart h0q h0r B
  refine ⟨Nq,hNq,?_⟩
  intro U hU hUB G k hk C hC hchart
  have hkq : Nq≤k := hk
  have hk1 : 1 ≤ k := hNq.trans hkq
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let K := closedBall c R \ ball c (R/2)
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  obtain ⟨hg,hD,hdata⟩ := hchart
  have hhalf (E : ℂ) (hE : E ∈ K) : R/2 ≤ ‖E-c‖ := by
    have hh : ¬dist E c < R/2 := hE.2
    rw [dist_eq_norm] at hh
    exact le_of_not_gt hh
  have hQ : AnalyticOnNhd ℂ (hillFreeGapQuadraticRoot h0q h0r k) (K ×ˢ U) :=
    (hquadratic k hkq).1.mono (fun t ht => ⟨hhalf t.1 ht.1,hUB ht.2⟩)
  have hQn (p : Coeff 2) (hp : p ∈ U) (E : ℂ) (hE : E ∈ K) : hillFreeGapQuadraticRoot h0q h0r k (E,p)≠0 :=
    ((hquadratic k hkq).2 p (hUB hp) E (hhalf E hE)).2.1
  have hQsq (p : Coeff 2) (hp : p ∈ U) (E : ℂ) (hE : E ∈ K) :
      hillFreeGapQuadraticRoot h0q h0r k (E,p)^2=
        quadraticRootPolynomial (hillLocalGapMidpoint 0 h0q h0r k p) (hillLocalGapSquare 0 h0q h0r k p/4) E := by
    exact ((hquadratic k hkq).2 p (hUB hp) E (hhalf E hE)).1
  have hQlower (p : Coeff 2) (hp : p ∈ U) (E : ℂ) (hE : E ∈ sphere c (3*R/4)) :
      R/4 ≤ ‖hillFreeGapQuadraticRoot h0q h0r k (E,p)‖ := by
    have hd : ‖E-c‖=3*R/4 := by simpa only [mem_sphere,dist_eq_norm] using hE
    have hh := ((hquadratic k hkq).2 p (hUB hp) E (by linarith)).2.2.1
    rw [hd] at hh
    linarith
  obtain ⟨H,hH,heq,hbound⟩ := exists_bounded_analytic_parametric_quadratic_solution_of_zero_period
    (hillComplexRegularGapNumerator h0q h0r G k) (hillFreeGapQuadraticRoot h0q h0r k)
    (hillLocalGapMidpoint 0 h0q h0r k) (fun p => hillLocalGapSquare 0 h0q h0r k p/4)
    c (R/2) (3*R/4) R (R/4) (R/4) (8*C/(k : ℝ)^3)
    (by linarith) (by positivity) (by positivity) (by positivity) (by linarith) (by linarith)
    U hU hg hQ hQn hQsq (fun p hp => (hdata p hp).2.2.1) hQlower (fun p hp => (hdata p hp).2.2.2.2)
  refine ⟨H,hH,heq,?_⟩
  intro p hp E hE
  apply (hbound p hp E hE).trans_eq
  field_simp
  ring

end NLS.KdV
