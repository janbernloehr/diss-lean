import NLS.KdV.HillComplexRootProductMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexRegularGapNumerator (G : ℂ × Coeff 2 → ℂ) (k : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  -I*G t/hillFilledFreeGapRoot h0q h0r k t

def hillComplexRegularGapDensity (G : ℂ × Coeff 2 → ℂ) (k : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  hillComplexRegularGapNumerator h0q h0r G k t/hillFreeGapQuadraticRoot h0q h0r k t

theorem exists_hillComplexRegularGapDensity_analytic_zero_periods
    (G : ℂ × Coeff 2 → ℂ) (U : Set (Coeff 2)) (B : ℝ)
    (hUB : U ⊆ ball (0 : Coeff 2) B) (hG : AnalyticOnNhd ℂ G (univ ×ˢ U)) (N0 : ℕ)
    (hzero : ∀ p ∈ U, ∀ k : ℕ, N0 ≤ k →
      (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))=0) :
    ∃ N : ℕ, 1 ≤ N ∧ N0 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      AnalyticOnNhd ℂ (hillComplexRegularGapNumerator h0q h0r G k)
        (closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ×ˢ U) ∧
      AnalyticOnNhd ℂ (hillComplexRegularGapDensity h0q h0r G k)
        ((closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) \
          ball (hillRealGapCenter 0 h0q h0r k : ℂ)
            ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/2)) ×ˢ U) ∧
      ∀ p ∈ U,
        (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          hillComplexRegularGapDensity h0q h0r G k (E,p)=(-I)*(G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))) ∧
        (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          hillComplexRegularGapDensity h0q h0r G k (E,p))=0 ∧
        (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/2),
          hillComplexRegularGapDensity h0q h0r G k (E,p))=0 := by
  obtain ⟨Nq,hNq,hquadratic⟩ := exists_hillFreeGap_bounded_complex_quadratic_root_chart h0q h0r B
  obtain ⟨Nr,hNr,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r B
  obtain ⟨Nm,hNm,hmatch⟩ := exists_hillFreeGap_bounded_complex_root_product_matching h0q h0r B
  refine ⟨max (max N0 Nq) (max Nr Nm),hNq.trans ((le_max_right _ _).trans (le_max_left _ _)),
    (le_max_left _ _).trans (le_max_left _ _),?_⟩
  intro k hk
  have hk0 : N0 ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hkq : Nq ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have hkr : Nr ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkm : Nm ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := hNq.trans hkq
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let K := closedBall c R \ ball c (R/2)
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hhalf (E : ℂ) (hE : E ∈ K) : R/2 ≤ ‖E-c‖ := by
    have hh : ¬dist E c < R/2 := hE.2
    rw [dist_eq_norm] at hh
    exact le_of_not_gt hh
  have hg : AnalyticOnNhd ℂ (hillComplexRegularGapNumerator h0q h0r G k) (closedBall c R ×ˢ U) := by
    intro t ht
    exact (analyticAt_const.mul (hG t ⟨mem_univ _,ht.2⟩)).div
      ((hroot k hkr).1 t ⟨ht.1,hUB ht.2⟩) (((hroot k hkr).2 t.2 (hUB ht.2) t.1 ht.1).2.1)
  have hD : AnalyticOnNhd ℂ (hillComplexRegularGapDensity h0q h0r G k) (K ×ˢ U) := by
    intro t ht
    exact (hg t ⟨ht.1.1,ht.2⟩).div ((hquadratic k hkq).1 t ⟨hhalf t.1 ht.1,hUB ht.2⟩)
      (((hquadratic k hkq).2 t.2 (hUB ht.2) t.1 (hhalf t.1 ht.1)).2.1)
  refine ⟨hg,hD,?_⟩
  intro p hp
  have hpoint (E : ℂ) (hE : E ∈ sphere c R) : hillComplexRegularGapDensity h0q h0r G k (E,p)=
      (-I)*(G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)) := by
    rw [← (hmatch p (hUB hp) k hkm E hE).2]
    dsimp only [hillComplexRegularGapDensity,hillComplexRegularGapNumerator]
    ring
  have houter : (∮ E in C(c,R), hillComplexRegularGapDensity h0q h0r G k (E,p))=0 := by
    have he : (∮ E in C(c,R), hillComplexRegularGapDensity h0q h0r G k (E,p))=
        (-I)*(∮ E in C(c,R), G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)) := by
      rw [← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr hR.le
      exact hpoint
    rw [he,hzero p hp k hk0,mul_zero]
  have hslice : AnalyticOnNhd ℂ (fun E => hillComplexRegularGapDensity h0q h0r G k (E,p)) K := by
    intro E hE
    exact (hD (E,p) ⟨hE,hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
  have he := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable (c := c) (r := R/2) (R := R)
    (by positivity) (by linarith) (s := (∅ : Set ℂ)) countable_empty hslice.continuousOn (by
      intro E hE
      exact (hslice E ⟨ball_subset_closedBall hE.1.1,fun hh => hE.1.2 (ball_subset_closedBall hh)⟩).differentiableAt)
  exact ⟨hpoint,houter,he.symm.trans houter⟩

end NLS.KdV
