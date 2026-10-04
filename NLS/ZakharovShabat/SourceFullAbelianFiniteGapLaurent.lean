import NLS.ZakharovShabat.SourceFullAbelianFiniteGapInversion

/-! # Convergent Laurent expansion of the actual finite-gap primitive

The normalized analytic inversion remainder yields a convergent series
in positive powers of `1/z`. All primitive indices share its coefficients.
Identification of these coefficients with the NLS Hamiltonians is not
asserted here.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- A genuinely convergent Laurent series, with the exact leading term
and no extra constant, for the canonical finite-gap primitive. -/
theorem exists_sourceFullAbelian_finiteGap_laurent
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ a : ℕ → ℂ, ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
      HasSum (fun k : ℕ => a k/z^(k+1))
        (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨R,hR,r,hr,_,A,hA,hA0,he⟩ := exists_sourceFullAbelian_finiteGap_inversion_remainder_all_indices C φ hφ hf
  obtain ⟨a,ε,hε,hs⟩ := exists_hasSum_positive_powers A r hr hA hA0
  let T := max R ε⁻¹+1
  have hRT : R < T := by dsimp [T]; linarith [le_max_left R ε⁻¹]
  have hεT : ε⁻¹ < T := by dsimp [T]; linarith [le_max_right R ε⁻¹]
  refine ⟨T,hR.trans hRT,a,?_⟩
  intro n z hz
  have hzpos := (hR.trans hRT).trans hz
  have hzin : ‖z⁻¹‖ < ε := by
    rw [norm_inv]
    exact (inv_lt_comm₀ hzpos hε).mpr (hεT.trans hz)
  have hval : sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n = A z⁻¹ := by
    rw [he n z (hRT.trans hz)]
    ring
  rw [hval]
  simpa only [div_eq_mul_inv,inv_pow] using hs z⁻¹ hzin

/-- The normalized remainder tends to zero in every direction at infinity. -/
theorem sourceFullAbelian_finiteGap_remainder_tendsto_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    Tendsto (fun z : ℂ => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n)
      (Bornology.cobounded ℂ) (𝓝 0) := by
  obtain ⟨R,_,r,hr,_,A,hA,hA0,he⟩ := exists_sourceFullAbelian_finiteGap_inversion_remainder_all_indices C φ hφ hf
  have ht := (hA 0 (mem_ball_self hr)).continuousAt.tendsto.comp tendsto_inv₀_cobounded
  rw [hA0] at ht
  apply ht.congr'
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
  dsimp only [Function.comp_def]
  rw [he n z hz]
  ring

/-- One ambient source neighborhood supports the convergent Laurent
expansion at every real finite-gap source, without a supplied chart. -/
theorem exists_sourceFullAbelian_finiteGap_laurent_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 →
        ∃ R : ℝ, 0 < R ∧ ∃ a : ℕ → ℂ, ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
          HasSum (fun k : ℕ => a k/z^(k+1))
            (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨W,hW,hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hf
  obtain ⟨C,hC⟩ := hfamilies φ
  exact exists_sourceFullAbelian_finiteGap_laurent C φ
    (by rw [hC]; exact mem_ball_self C.discs.sourceRadius_pos) hf

end NLS.ZakharovShabat
