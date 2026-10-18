import NLS.ZakharovShabat.SourceBirkhoffHmComplexSpectralTerminalAnalytic
import NLS.ZakharovShabat.SourceBirkhoffFourierErrorReduction

/-! # Analytic reduction of the remaining higher-order Fourier errors

Analytic h^(m+1) realizations of the two literal spectral errors imply an analytic realization of the original rectangular Birkhoff-minus-Fourier error. The sharp spectral-error hypotheses remain explicit; full one-smoothing is not asserted.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- Analytic stronger-target realizations of the two literal spectral errors suffice for the actual Fourier remainder at every positive integer order. -/
theorem exists_local_higherSobolevBirkhoffFourier_analytic_of_spectral_errors
    (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m)
    (U : Set (SobolevSource m)) (hU : IsOpen U) (haU : a.val ∈ U)
    (A B : SobolevSource m → WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2)
    (hAa : AnalyticOnNhd ℂ A U) (hBa : AnalyticOnNhd ℂ B U)
    (hA : ∀ b ∈ U, ∀ n, (A b).val n = sourceEtaMidpointFourierError (by simp) (by norm_num) (higherSobolevSourceInclusion m b) n)
    (hB : ∀ b ∈ U, ∀ n, (B b).val n = sourceEtaSineFourierError (by simp) (by norm_num) (higherSobolevSourceInclusion m b) n) :
    ∃ V : Set (SobolevSource m), IsOpen V ∧ a.val ∈ V ∧ V ⊆ U ∧
      ∃ E : SobolevSource m → WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2,
        AnalyticOnNhd ℂ E V ∧ ∀ b ∈ V, ∀ n,
          (E b).1.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).1 n-
            (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).1 n ∧
          (E b).2.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).2 n-
            (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).2 n := by
  obtain ⟨Va,hVa,haVa,M,hM,hang⟩ := D.exists_local_higherSobolevBirkhoffSpectralTerminal_analytic m hm a
  let L := higherSobolevSourceInclusion m
  let V := U ∩ (Va ∩ L ⁻¹' W)
  have hV : IsOpen V := hU.inter (hVa.inter (D.source_open.preimage L.continuous))
  let u := higherSobolevBirkhoffSpectralTerminalError m s 1
  let v := higherSobolevBirkhoffSpectralTerminalError m s (-1)
  let X (b : SobolevSource m) := ((1:ℂ)/(Real.sqrt 8:ℂ)) • (u b+v b-(4:ℂ) • A b)
  let Y (b : SobolevSource m) := ((1:ℂ)/((Real.sqrt 8:ℂ)*I)) • (u b-v b-(4*I) • B b)
  let E (b : SobolevSource m) := (X b,Y b)
  have hu : AnalyticOnNhd ℂ u Va := by simpa only [Complex.ofReal_one] using (hang 1 (Or.inl rfl)).1
  have hv : AnalyticOnNhd ℂ v Va := by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using (hang (-1) (Or.inr rfl)).1
  refine ⟨V,hV,⟨haU,haVa,D.real_subset a.property⟩,(fun b hb => hb.1),E,?_,?_⟩
  · intro b hb
    have hX : AnalyticAt ℂ X b := by
      dsimp only [X]
      exact (((hu b hb.2.1).add (hv b hb.2.1)).sub
        ((hAa b hb.1).const_smul (c := (4:ℂ)))).const_smul (c := (1:ℂ)/(Real.sqrt 8:ℂ))
    have hY : AnalyticAt ℂ Y b := by
      dsimp only [Y]
      exact (((hu b hb.2.1).sub (hv b hb.2.1)).sub
        ((hBa b hb.1).const_smul (c := (4*I:ℂ)))).const_smul (c := (1:ℂ)/((Real.sqrt 8:ℂ)*I))
    exact hX.prod hY
  · intro b hb n
    have huc := ((hang 1 (Or.inl rfl)).2 b hb.2.1).2 n
    have hvc := ((hang (-1) (Or.inr rfl)).2 b hb.2.1).2 n
    simp only [Complex.ofReal_one,Complex.ofReal_neg] at huc hvc
    have he := sourceBirkhoff_fourier_error_decomposition (by simp) (by norm_num) (L b) s n
    rw [(D.coordinates (L b) hb.2.2 n).1,(D.coordinates (L b) hb.2.2 n).2]
    constructor
    · rw [he.1]
      simp only [E,X,u,v,WeightedCoeff.smul_val,WeightedCoeff.sub_val,WeightedCoeff.add_val,huc,hvc,hA b hb.1]
      ring
    · rw [he.2]
      simp only [E,Y,u,v,WeightedCoeff.smul_val,WeightedCoeff.sub_val,huc,hvc,hB b hb.1]
      ring

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
