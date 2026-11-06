import NLS.ZakharovShabat.SourceFiniteGapMassDivergence

/-! # Mass divergence for arbitrary Hilbert approximants

The original Hilbert mass is the first component's Fourier energy. Any
Hilbert-source approximation to a non-Hilbert real source must therefore
have mass tending to positive infinity. No spectral or smoothness
restriction on the approximants is required.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceHilbertMass_real_eq_norm_fst (φ : realTypeSourceSubmodule 2) :
    (sourceHilbertMass φ.val).re = ‖φ.val.fst‖^2 := by
  have h := congrArg Complex.re (sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property)
  change (sourceHilbertMass φ.val).re = ‖φ‖^2/2 at h
  rw [h,realTypeSource_norm_sq_eq_two_mul_fst]
  ring

theorem sum_fst_sq_le_sourceHilbertMass_real (φ : realTypeSourceSubmodule 2) (S : Finset ℤ) :
    ∑ n ∈ S, ‖φ.val.fst n‖^2 ≤ (sourceHilbertMass φ.val).re := by
  rw [sourceHilbertMass_real_eq_norm_fst]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) φ.val.fst S

/-- Arbitrary convergent Hilbert approximants outside the Hilbert locus have
unbounded original physical mass, including smooth real scalar cutoffs. -/
theorem tendsto_sourceHilbertMass_real_atTop (h2p : 2 ≤ p)
    {ι : Type*} {l : Filter ι} (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p) (ψ : ι → realTypeSourceSubmodule 2)
    (hψ : Tendsto (fun j => realTypeSourceExponentInclusion h2p (ψ j)) l (𝓝 φ)) :
    Tendsto (fun j => (sourceHilbertMass (ψ j).val).re) l atTop := by
  have hn : ¬ Summable (fun n : ℤ => ‖φ.val.fst n‖^2) :=
    fun h => hφ ((mem_sourceHilbertLocus_iff h2p φ).mpr h)
  apply tendsto_atTop.mpr
  intro b
  have hex : ∃ S : Finset ℤ, b < ∑ n ∈ S, ‖φ.val.fst n‖^2 := by
    by_contra h
    push Not at h
    exact hn (summable_of_sum_le (fun _ => sq_nonneg _) h)
  obtain ⟨S,hS⟩ := hex
  have hc (n : ℤ) : Continuous (fun ξ : realTypeSourceSubmodule p => ξ.val.fst n) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp
      ((CoeffPair.toMax p).continuous.fst.comp continuous_subtype_val)
  have ht : Tendsto (fun j => ∑ n ∈ S, ‖(ψ j).val.fst n‖^2) l
      (𝓝 (∑ n ∈ S, ‖φ.val.fst n‖^2)) :=
    tendsto_finsetSum S (fun n _ => ((hc n).continuousAt.tendsto.comp hψ).norm.pow 2)
  filter_upwards [ht.eventually (lt_mem_nhds hS)] with j hj
  exact hj.le.trans (sum_fst_sq_le_sourceHilbertMass_real (ψ j) S)

end NLS.ZakharovShabat
