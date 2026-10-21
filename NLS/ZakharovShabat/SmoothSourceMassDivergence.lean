import NLS.ZakharovShabat.SmoothNLSDataDensity
import NLS.ZakharovShabat.SmoothClassicalNLSAgreement
import NLS.SequenceSpaces.PairExponentIdentity

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The mass of actual smooth data is its first Fourier component's Hilbert energy. -/
theorem SmoothNLSData.mass_eq_fst_norm_sq (f : SmoothNLSData) :
    classicalNLSMass f.value = ‖(f.source 2).val.fst‖^2 := by
  have hm : classicalNLSMass f.value = (sourceHilbertMass (f.source 2).val).re := by
    rw [← sourceOrdinaryMass_smoothPeriodOneHilbertSource f.value f.smooth f.periodic]
    simp only [SmoothNLSData.source,smoothPeriodOneSourceAt_two,
      sourceOrdinaryMass,sourceOrdinaryComplexMass,CoeffPair.exponentInclusion_refl]
  rw [hm]
  have h := congrArg Complex.re
    (sourceHilbertMass_eq_half_norm_sq_of_realType (f.source 2).val (f.source 2).property)
  change (sourceHilbertMass (f.source 2).val).re = ‖f.source 2‖^2/2 at h
  rw [h,realTypeSource_norm_sq_eq_two_mul_fst]
  ring

/-- Every finite Fourier energy sum at any source exponent is bounded by physical mass. -/
theorem SmoothNLSData.sum_fst_sq_le_mass (f : SmoothNLSData) (S : Finset ℤ) :
    ∑ n ∈ S, ‖(f.source p).val.fst n‖^2 ≤ classicalNLSMass f.value := by
  rw [f.mass_eq_fst_norm_sq]
  have h := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (f.source 2).val.fst S
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,SmoothNLSData.source,
    smoothPeriodOneSourceAt_fst] using h

/-- Any smooth approximation of a non-Hilbert source has mass tending to infinity. -/
theorem tendsto_smoothNLSData_mass_atTop (h2p : 2 ≤ p)
    {ι : Type*} {l : Filter ι} (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p) (f : ι → SmoothNLSData)
    (hf : Tendsto (fun j => (f j).source p) l (𝓝 φ)) :
    Tendsto (fun j => classicalNLSMass (f j).value) l atTop := by
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
  have ht : Tendsto (fun j => ∑ n ∈ S, ‖((f j).source p).val.fst n‖^2) l
      (𝓝 (∑ n ∈ S, ‖φ.val.fst n‖^2)) :=
    tendsto_finsetSum S (fun n _ => ((hc n).continuousAt.tendsto.comp hf).norm.pow 2)
  filter_upwards [ht.eventually (lt_mem_nhds hS)] with j hj
  exact hj.le.trans ((f j).sum_fst_sq_le_mass S)

end NLS.ZakharovShabat
