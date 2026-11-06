import NLS.KdV.HillComplexRegularDensity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillComplexRegularGapDensity_uniform_contour_bounds
    (G : ℂ × Coeff 2 → ℂ) (U : Set (Coeff 2)) (B : ℝ)
    (hUB : U ⊆ ball (0 : Coeff 2) B) (hG : AnalyticOnNhd ℂ G (univ ×ˢ U))
    (N0 : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p ∈ U, ∀ k : ℕ, N0 ≤ k → ∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖ ≤ C/(k : ℝ)^3) :
    ∃ N : ℕ, 1 ≤ N ∧ N0 ≤ N ∧ ∀ k : ℕ, N ≤ k → ∀ p ∈ U,
      (∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ‖hillComplexRegularGapNumerator h0q h0r G k (E,p)‖ ≤
          2*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)*C/(k : ℝ)^3) ∧
      ∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4),
        ‖hillComplexRegularGapDensity h0q h0r G k (E,p)‖ ≤ 8*C/(k : ℝ)^3 := by
  obtain ⟨Nq,hNq,hquadratic⟩ := exists_hillFreeGap_bounded_complex_quadratic_root_chart h0q h0r B
  obtain ⟨Nr,hNr,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r B
  obtain ⟨Nm,hNm,hmatch⟩ := exists_hillFreeGap_bounded_complex_root_product_matching h0q h0r B
  refine ⟨max (max N0 Nq) (max Nr Nm),hNq.trans ((le_max_right _ _).trans (le_max_left _ _)),
    (le_max_left _ _).trans (le_max_left _ _),?_⟩
  intro k hk p hp
  have hk0 : N0 ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hkq : Nq ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have hkr : Nr ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkm : Nm ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := hNq.trans hkq
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let g : ℂ → ℂ := fun E => hillComplexRegularGapNumerator h0q h0r G k (E,p)
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hg : AnalyticOnNhd ℂ g (closedBall c R) := by
    intro E hE
    have hGj := (hG (E,p) ⟨mem_univ _,hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
    have hRj := ((hroot k hkr).1 (E,p) ⟨hE,hUB hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
    exact (analyticAt_const.mul hGj).div hRj (((hroot k hkr).2 p (hUB hp) E hE).2.1)
  have houter (E : ℂ) (hE : E ∈ sphere c R) : ‖g E‖ ≤ 2*R*C/(k : ℝ)^3 := by
    have hd : ‖E-c‖=R := by simpa only [mem_sphere,dist_eq_norm] using hE
    have hl : R/2 ≤ ‖E-c‖ := by linarith
    obtain ⟨_,hQn,_,hQb⟩ := (hquadratic k hkq).2 p (hUB hp) E hl
    have hRn := ((hroot k hkr).2 p (hUB hp) E (sphere_subset_closedBall hE)).2.1
    have hid : g E=(-I)*(G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))*hillFreeGapQuadraticRoot h0q h0r k (E,p) := by
      rw [← (hmatch p (hUB hp) k hkm E hE).2]
      dsimp only [g,hillComplexRegularGapNumerator]
      field_simp
    rw [hid,norm_mul,norm_mul,norm_neg,norm_I,one_mul]
    have h := mul_le_mul (hbound p hp k hk0 E hE) hQb (norm_nonneg _) (by positivity : 0 ≤ C/(k : ℝ)^3)
    rw [hd] at h
    exact h.trans_eq (by ring)
  have hdisc (E : ℂ) (hE : E ∈ closedBall c R) : ‖g E‖ ≤ 2*R*C/(k : ℝ)^3 := by
    have hdc : DiffContOnCl ℂ g (ball c R) :=
      DiffContOnCl.mk_ball (hg.differentiableOn.mono ball_subset_closedBall) hg.continuousOn
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
    · intro w hw
      rw [frontier_ball c hR.ne'] at hw
      exact houter w hw
    · rw [closure_ball c hR.ne']
      exact hE
  refine ⟨hdisc,?_⟩
  intro E hE
  have hd : ‖E-c‖=3*R/4 := by simpa only [mem_sphere,dist_eq_norm] using hE
  have hl : R/2 ≤ ‖E-c‖ := by linarith
  have hEK : E ∈ closedBall c R := by rw [mem_closedBall,dist_eq_norm,hd];linarith
  have hQlow : R/4 ≤ ‖hillFreeGapQuadraticRoot h0q h0r k (E,p)‖ := by
    have hh := ((hquadratic k hkq).2 p (hUB hp) E hl).2.2.1
    rw [hd] at hh
    linarith
  change ‖g E/hillFreeGapQuadraticRoot h0q h0r k (E,p)‖ ≤ _
  rw [norm_div]
  calc
    _ ≤ (2*R*C/(k : ℝ)^3)/(R/4) := div_le_div₀ (by positivity) (hdisc E hEK) (by positivity) hQlow
    _ = _ := by field_simp;ring

end NLS.KdV
