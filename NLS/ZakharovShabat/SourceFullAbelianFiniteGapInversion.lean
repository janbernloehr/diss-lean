import NLS.ZakharovShabat.SourcePeriodicEndpointAtInfinity
import NLS.ComplexAnalysis.ExteriorInversionRemainder

/-! # The normalized analytic inversion remainder of the finite-gap primitive

Integrating the exterior derivative leaves a constant. Actual collapsed
tail endpoint values, together with their finite-exponent displacement
decay, force that constant to vanish.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The zero-index primitive has an analytic inversion remainder with
zero constant term, fixed by its actual spectral normalization. -/
theorem exists_sourceFullAbelian_finiteGap_inversion_remainder
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧ r⁻¹ < R ∧ ∃ A : ℂ → ℂ,
      AnalyticOnNhd ℂ A (ball 0 r) ∧ A 0 = 0 ∧
      ∀ z : ℂ, R < ‖z‖ → sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val) = -I*z+A z⁻¹ := by
  obtain ⟨E⟩ := C.charts φ.val hφ
  obtain ⟨R,hR,r,hr,hrR,h,hh,hF⟩ := exists_sourceFullAbelianPrimitive_finiteGap_quadratic_derivative φ E hf
  obtain ⟨A,hA,hA0,_,c,heq⟩ := exists_exterior_inversion_remainder
    (fun z => sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)) h R r hR hr hrR hh (hF 0).2
  let l : ℤ → ℂ := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)
  have hl := tendsto_sourcePeriodicLeft_norm_atTop hp hp1 φ.val
  have hi : Tendsto (fun n : ℤ => (l n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hl)
  have hAl : Tendsto (fun n : ℤ => A (l n)⁻¹) atTop (𝓝 0) := by
    simpa only [hA0,Function.comp_def] using! (hA 0 (mem_ball_self hr)).continuousAt.tendsto.comp hi
  have hdisp := (tendsto_sourcePeriodicLeft_sub_free_atTop hp hp1 φ.val).const_mul (-I)
  have ht : Tendsto (fun n : ℤ => -I*(l n-(Real.pi : ℂ)*n)+A (l n)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using hdisp.add hAl
  have hclosed : ∀ᶠ n : ℤ in atTop,
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
    have hfin : {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0}.Finite := hf
    filter_upwards [atTop_le_cofinite hfin.compl_mem_cofinite] with n hn
    exact not_not.mp hn
  have hconst : Tendsto (fun _ : ℤ => -c) atTop (𝓝 (0:ℂ)) := by
    apply ht.congr'
    filter_upwards [hclosed,hl.eventually (eventually_gt_atTop R)] with n hn hln
    have hend := C.fullPrimitive_collapsed_endpoint_value n 0 φ.val hφ hn (l n) (by simp [l])
    have he := heq (l n) hln
    simp only [Int.cast_zero,zero_sub,mul_neg] at hend
    rw [hend] at he
    linear_combination -he
  have hc0 : c = 0 := neg_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hconst)
  refine ⟨R,hR,r,hr,hrR,A,hA,hA0,?_⟩
  intro z hz
  simpa only [hc0,add_zero] using heq z hz

/-- All normalization indices share one analytic remainder. Only the
prescribed constant `i*pi*n` depends on the index. -/
theorem exists_sourceFullAbelian_finiteGap_inversion_remainder_all_indices
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧ r⁻¹ < R ∧ ∃ A : ℂ → ℂ,
      AnalyticOnNhd ℂ A (ball 0 r) ∧ A 0 = 0 ∧
      ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
        sourceFullAbelianPrimitive hp hp1 W n (z,φ.val) = -I*z+I*(Real.pi : ℂ)*n+A z⁻¹ := by
  obtain ⟨R,hR,r,hr,hrR,A,hA,hA0,he⟩ := exists_sourceFullAbelian_finiteGap_inversion_remainder C φ hφ hf
  obtain ⟨T,_,hT⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  obtain ⟨E⟩ := C.charts φ.val hφ
  refine ⟨max R T,hR.trans_le (le_max_left _ _),r,hr,hrR.trans_le (le_max_left _ _),A,hA,hA0,?_⟩
  intro n z hz
  rw [sourceFullAbelianPrimitive_index_shift E n z (hT ((le_max_right _ _).trans_lt hz)),
    he z ((le_max_left _ _).trans_lt hz)]
  ring

end NLS.ZakharovShabat
