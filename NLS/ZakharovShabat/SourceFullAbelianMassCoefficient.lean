import NLS.ZakharovShabat.SourceFullAbelianFiniteGapLaurent
import NLS.ZakharovShabat.SourceFiniteGapMassExponent

/-! # Mass in the canonical finite-gap inversion remainder

The physical mass coefficient of the Floquet logarithmic derivative
integrates to the first coefficient of the actual normalized primitive.
The already-proved vanishing remainder fixes the integration constant.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem exists_sourceFullAbelian_finiteGap_mass_inversion
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧ r⁻¹ < R ∧ ∃ A : ℂ → ℂ,
      AnalyticOnNhd ℂ A (ball 0 r) ∧ A 0 = 0 ∧ deriv A 0 = I*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k))/2 ∧
      ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
        sourceFullAbelianPrimitive hp hp1 W n (z,φ.val) = -I*z+I*(Real.pi : ℂ)*n+A z⁻¹ := by
  obtain ⟨E⟩ := C.charts φ.val hφ
  obtain ⟨T,hT,hsub⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  obtain ⟨r,hr,h,hh,hh0,he⟩ := exists_sourceFiniteGap_coefficient_mass_remainder hp hp1 φ hf
  let R := max T r⁻¹+1
  have hTR : T < R := by dsimp [R]; linarith [le_max_left T r⁻¹]
  have hrR : r⁻¹ < R := by dsimp [R]; linarith [le_max_right T r⁻¹]
  have hR := hT.trans hTR
  have hd (z : ℂ) (hz : R < ‖z‖) :
      HasDerivAt (fun w => sourceFullAbelianPrimitive hp hp1 W 0 (w,φ.val))
        (-I+z⁻¹^2*h z⁻¹) z := by
    rw [← he z (hrR.trans hz)]
    exact sourceFullAbelianPrimitive_real_hasDerivAt φ E 0 z (hsub (hTR.trans hz))
  obtain ⟨A,hA,hA0,hAd,c,hrep⟩ := exists_exterior_inversion_remainder _ h R r hR hr hrR hh hd
  have ht := sourceFullAbelian_finiteGap_remainder_tendsto_zero C φ hφ hf 0
  simp only [Int.cast_zero,mul_zero,sub_zero] at ht
  have hAl : Tendsto (fun z : ℂ => A z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa only [hA0,Function.comp_def] using (hA 0 (mem_ball_self hr)).continuousAt.tendsto.comp tendsto_inv₀_cobounded
  have hconst : Tendsto (fun _ : ℂ => c) (Bornology.cobounded ℂ) (𝓝 0) := by
    have hdiff := ht.sub hAl
    simp only [sub_zero] at hdiff
    apply hdiff.congr'
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
    rw [hrep z hz]
    ring
  have hc0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  have hder : deriv A 0 = I*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k))/2 := by
    rw [(hAd 0 (mem_ball_self hr)).deriv,hh0]
    ring
  refine ⟨R,hR,r,hr,hrR,A,hA,hA0,hder,?_⟩
  intro n z hz
  rw [sourceFullAbelianPrimitive_index_shift E n z (hsub (hTR.trans hz)),hrep z hz,hc0]
  ring

/-- A genuinely convergent Laurent series, with the exact leading term
and first coefficient equal to `i` times half the physical mass. -/
theorem exists_sourceFullAbelian_finiteGap_mass_laurent
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ a : ℕ → ℂ, a 0 = I*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k))/2 ∧ ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
      HasSum (fun k : ℕ => a k/z^(k+1))
        (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨R,hR,r,hr,_,A,hA,hA0,hder,he⟩ := exists_sourceFullAbelian_finiteGap_mass_inversion C φ hφ hf
  obtain ⟨a,ha,ε,hε,hs⟩ := exists_hasSum_positive_powers_with_first A r hr hA hA0
  let T := max R ε⁻¹+1
  have hRT : R < T := by dsimp [T]; linarith [le_max_left R ε⁻¹]
  have hεT : ε⁻¹ < T := by dsimp [T]; linarith [le_max_right R ε⁻¹]
  refine ⟨T,hR.trans hRT,a,ha.trans hder,?_⟩
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

/-- The actual normalized primitive recovers the original mass in every
direction at infinity, for every signed normalization index. -/
theorem sourceFullAbelian_finiteGap_mass_tendsto
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    Tendsto (fun z : ℂ => z*(sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n))
      (Bornology.cobounded ℂ) (𝓝 (I*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k))/2)) := by
  obtain ⟨R,_,r,hr,_,A,hA,hA0,hder,he⟩ := exists_sourceFullAbelian_finiteGap_mass_inversion C φ hφ hf
  have ht := tendsto_mul_inversion_remainder A r hr hA hA0
  rw [hder] at ht
  apply ht.congr'
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
  rw [he n z hz]
  ring

/-- In the Hilbert source normalization the first Laurent coefficient is
`i` times one quarter of the square of the pair norm. -/
theorem exists_sourceFullAbelian_finiteGap_norm_laurent
    {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W) (φ : realTypeSourceSubmodule 2)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ R : ℝ, 0 < R ∧ ∃ a : ℕ → ℂ, a 0 = I*(‖φ.val‖^2 : ℝ)/4 ∧
      ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
        HasSum (fun k : ℕ => a k/z^(k+1))
          (sourceFullAbelianPrimitive (by simp) (by norm_num) W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨R,hR,a,ha,hs⟩ := exists_sourceFullAbelian_finiteGap_mass_laurent C φ hφ hf
  refine ⟨R,hR,a,?_,hs⟩
  have hm := sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property
  change (∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) = _ at hm
  rw [ha,hm,ofReal_div,ofReal_ofNat]
  ring

/-- One ambient neighborhood supports the mass-calibrated convergent series
at every real finite-gap source. -/
theorem exists_sourceFullAbelian_finiteGap_mass_laurent_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 →
        ∃ R : ℝ, 0 < R ∧ ∃ a : ℕ → ℂ,
          a 0 = I*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k))/2 ∧
          ∀ (n : ℤ) (z : ℂ), R < ‖z‖ → HasSum (fun k : ℕ => a k/z^(k+1))
            (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨W,hW,hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hf
  obtain ⟨C,hC⟩ := hfamilies φ
  exact exists_sourceFullAbelian_finiteGap_mass_laurent C φ
    (by rw [hC]; exact mem_ball_self C.discs.sourceRadius_pos) hf

end NLS.ZakharovShabat
