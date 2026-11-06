import NLS.KdV.HillCommonRegularAnnulusChart
import NLS.KdV.HillUniformNormalizedPeriodContours

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The annulus cutoff is chosen before the numerator and before the
set of active gaps, so omitting an arbitrary own index costs no cutoff. -/
theorem exists_hillRegularGapDensity_uniform_active_zero_periods
    (U : Set (Coeff 2)) (B : ℝ) (hUB : U ⊆ ball (0 : Coeff 2) B) :
    ∃ N : ℕ, 1≤N ∧ ∀ G : ℂ × Coeff 2 → ℂ,
      AnalyticOnNhd ℂ G (univ ×ˢ U) → ∀ P : ℕ → Prop,
      (∀ p∈U, ∀ k : ℕ, 1≤k → P k →
        (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
          hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))=0) →
      ∀ k : ℕ, N≤k → P k →
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
  refine ⟨max (max 1 Nq) (max Nr Nm),hNq.trans ((le_max_right _ _).trans (le_max_left _ _)),
    ?_⟩
  intro G hG P hzero k hk hPk
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
    rw [he,hzero p hp k hk1 hPk,mul_zero]
  have hslice : AnalyticOnNhd ℂ (fun E => hillComplexRegularGapDensity h0q h0r G k (E,p)) K := by
    intro E hE
    exact (hD (E,p) ⟨hE,hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
  have he := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable (c := c) (r := R/2) (R := R)
    (by positivity) (by linarith) (s := (∅ : Set ℂ)) countable_empty hslice.continuousOn (by
      intro E hE
      exact (hslice E ⟨ball_subset_closedBall hE.1.1,fun hh => hE.1.2 (ball_subset_closedBall hh)⟩).differentiableAt)
  exact ⟨hpoint,houter,he.symm.trans houter⟩

/-- Variable gap majorants pass through the original maximum-principle
annulus bounds; the geometry is independent of the active gaps and numerator. -/
theorem exists_hillRegularGapDensity_uniform_active_contour_bounds
    (U : Set (Coeff 2)) (B : ℝ) (hUB : U ⊆ ball (0 : Coeff 2) B) :
    ∃ N : ℕ, 1≤N ∧ ∀ G : ℂ × Coeff 2 → ℂ,
      AnalyticOnNhd ℂ G (univ ×ˢ U) → ∀ b : ℕ → ℝ, (∀ k, 0≤b k) →
      ∀ P : ℕ → Prop,
      (∀ p∈U, ∀ k : ℕ, 1≤k → P k → ∀ E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤b k) →
      ∀ k : ℕ, N≤k → P k → ∀ p∈U,
      (∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ‖hillComplexRegularGapNumerator h0q h0r G k (E,p)‖ ≤
          2*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)*b k) ∧
      ∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4),
        ‖hillComplexRegularGapDensity h0q h0r G k (E,p)‖ ≤ 8*b k := by
  obtain ⟨Nq,hNq,hquadratic⟩ := exists_hillFreeGap_bounded_complex_quadratic_root_chart h0q h0r B
  obtain ⟨Nr,hNr,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r B
  obtain ⟨Nm,hNm,hmatch⟩ := exists_hillFreeGap_bounded_complex_root_product_matching h0q h0r B
  refine ⟨max (max 1 Nq) (max Nr Nm),hNq.trans ((le_max_right _ _).trans (le_max_left _ _)),
    ?_⟩
  intro G hG b hb P hbound k hk hPk p hp
  have hC := hb k
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
  have houter (E : ℂ) (hE : E ∈ sphere c R) : ‖g E‖ ≤ 2*R*b k := by
    have hd : ‖E-c‖=R := by simpa only [mem_sphere,dist_eq_norm] using hE
    have hl : R/2 ≤ ‖E-c‖ := by linarith
    obtain ⟨_,hQn,_,hQb⟩ := (hquadratic k hkq).2 p (hUB hp) E hl
    have hRn := ((hroot k hkr).2 p (hUB hp) E (sphere_subset_closedBall hE)).2.1
    have hid : g E=(-I)*(G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))*hillFreeGapQuadraticRoot h0q h0r k (E,p) := by
      rw [← (hmatch p (hUB hp) k hkm E hE).2]
      dsimp only [g,hillComplexRegularGapNumerator]
      field_simp
    rw [hid,norm_mul,norm_mul,norm_neg,norm_I,one_mul]
    have h := mul_le_mul (hbound p hp k hk1 hPk E hE) hQb (norm_nonneg _) (by positivity : 0 ≤ b k)
    rw [hd] at h
    exact h.trans_eq (by ring)
  have hdisc (E : ℂ) (hE : E ∈ closedBall c R) : ‖g E‖ ≤ 2*R*b k := by
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
    _ ≤ (2*R*b k)/(R/4) := div_le_div₀ (by positivity) (hdisc E hEK) (by positivity) hQlow
    _ = _ := by field_simp;ring

end NLS.KdV
