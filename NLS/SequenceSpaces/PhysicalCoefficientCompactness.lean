import NLS.SequenceSpaces.PhysicalHilbertQuadratic
import NLS.SequenceSpaces.CoefficientCompactness

/-! Bounded physical Fourier Hilbert sequences admit physical
coefficientwise limits. Convergence of the true weighted squared norm
upgrades coefficientwise convergence to strong norm convergence. -/
noncomputable section
open Set Filter Topology
namespace NLS.WeightedCoeff

theorem exists_fourierRealZero_coefficientwise_subseq (w : Weight)
    (a : ℕ → fourierRealZeroSubmodule w 2)
    (hb : Bornology.IsBounded (range a)) :
    ∃ b : fourierRealZeroSubmodule w 2, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ n : ℤ, Tendsto (fun k => (a (σ k)).val.val.val n) atTop (𝓝 (b.val.val.val n)) := by
  have hA : Bornology.IsBounded (range (fun k => fourierRealZeroWeightedCoefficients w (a k))) := by
    obtain ⟨C,hC⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C,?_⟩
    rintro _ ⟨k,rfl⟩
    rw [norm_fourierRealZeroWeightedCoefficients]
    exact hC _ ⟨k,rfl⟩
  obtain ⟨c,σ,hσ,ht⟩ := Coeff.exists_coefficientwise_tendsto_subseq_of_bounded
    (fun k => fourierRealZeroWeightedCoefficients w (a k)) hA
  let b := (weightIsometry w 2).symm c
  have hraw (n : ℤ) : Tendsto (fun k => (a (σ k)).val.val.val n) atTop (𝓝 (b.val n)) := by
    have he (k : ℕ) : (a (σ k)).val.val.val n=
        fourierRealZeroWeightedCoefficients w (a (σ k)) n/(w n:ℂ) := by
      rw [fourierRealZeroWeightedCoefficients_apply,mul_div_cancel_left₀ _ (w.complex_ne_zero n)]
    simp_rw [he]
    exact (ht n).div_const (w n:ℂ)
  have hb0 : b.val 0=0 := by
    have hz : Tendsto (fun k => (a (σ k)).val.val.val 0) atTop (𝓝 (0:ℂ)) := by
      have he : (fun k => (a (σ k)).val.val.val 0)=(fun _ : ℕ => (0:ℂ)) :=
        funext (fun k => (a (σ k)).val.property)
      rw [he]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hraw 0) hz
  let b0 : zeroModeSubmodule w 2 := ⟨b,hb0⟩
  have hbreal : b0 ∈ fourierRealZeroSubmodule w 2 := by
    intro n
    have hc := Complex.continuous_conj.continuousAt.tendsto.comp (hraw n)
    have he : (fun k => (a (σ k)).val.val.val (-n))=
        (fun k => (starRingEnd ℂ) ((a (σ k)).val.val.val n)) := funext (fun k => (a (σ k)).property n)
    change Tendsto (fun k => (starRingEnd ℂ) ((a (σ k)).val.val.val n)) atTop
      (𝓝 ((starRingEnd ℂ) (b.val n))) at hc
    rw [← he] at hc
    exact tendsto_nhds_unique (hraw (-n)) hc
  exact ⟨⟨b0,hbreal⟩,σ,hσ,hraw⟩

theorem tendsto_fourierRealZero_of_coefficientwise_of_norm_sq (w : Weight)
    {α : Type*} {l : Filter α} (a : α → fourierRealZeroSubmodule w 2)
    (b : fourierRealZeroSubmodule w 2)
    (ht : ∀ n : ℤ, Tendsto (fun k => (a k).val.val.val n) l (𝓝 (b.val.val.val n)))
    (hn : Tendsto (fun k => ‖a k‖^2) l (𝓝 (‖b‖^2))) : Tendsto a l (𝓝 b) := by
  have hcoeff (n : ℤ) : Tendsto (fun k => fourierRealZeroWeightedCoefficients w (a k) n) l
      (𝓝 (fourierRealZeroWeightedCoefficients w b n)) := by
    simp_rw [fourierRealZeroWeightedCoefficients_apply]
    exact (ht n).const_mul (w n:ℂ)
  have hnorm : Tendsto (fun k => ‖fourierRealZeroWeightedCoefficients w (a k)‖^2) l
      (𝓝 (‖fourierRealZeroWeightedCoefficients w b‖^2)) := by
    simpa only [norm_fourierRealZeroWeightedCoefficients] using hn
  have hstrong := Coeff.tendsto_of_coefficientwise_of_norm_sq _ _ hcoeff hnorm
  apply tendsto_subtype_rng.mpr
  apply tendsto_subtype_rng.mpr
  have hbck := (weightIsometry w 2).symm.continuous.continuousAt.tendsto.comp hstrong
  change Tendsto (fun k => (weightIsometry w 2).symm ((weightIsometry w 2) (a k).val.val)) l
    (𝓝 ((weightIsometry w 2).symm ((weightIsometry w 2) b.val.val))) at hbck
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hbck

end NLS.WeightedCoeff
