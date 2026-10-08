import NLS.ZakharovShabat.M1CentralGapEstimate
import NLS.ZakharovShabat.FiniteGapHeight

/-! # Central gaps for complex potentials of spectral height at most one -/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- The complex central block has the source horizontal width plus four per gap. -/
theorem M1_canonicalGap_central_sq_le_of_height_one (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (hh : ∀ z ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ), |z.im| ≤ 1)
    (N : ℕ) (hpos : 0 < N) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) :
    (∑ n ∈ Finset.Ioo (-(N:ℤ)) N,
      ‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖^2) ≤
      ((2*(N:ℝ)-1)*Real.pi)^2+4*(2*(N:ℝ)-1) := by
  let ξ := canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven
  let η := canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven
  let b := ((N:ℝ)-1/2)*Real.pi
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hpos
  have hb : 0 ≤ b := mul_nonneg (by linarith) Real.pi_pos.le
  have hs := canonicalPeriodicEndpoints_spec (by simp) (by norm_num : (1:ENNReal) < 2)
    (weightedBaseToPair w φ) heven
  have hbound (n : ℤ) (hn : n ∈ Finset.Ioo (-(N:ℤ)) N) :
      -b ≤ (ξ n).re ∧ (ξ n).re ≤ (η n).re ∧ (η n).re ≤ b := by
    have hn' := Finset.mem_Ioo.mp hn
    have h := M1_canonicalEndpoints_central_re w hw φ heven N hN n (by omega)
    exact ⟨(abs_le.mp h.1).1,NLS.ComplexAnalysis.re_le_of_complexLexLE (hs.2.1 n),
      (abs_le.mp h.2).2⟩
  have hheight (n : ℤ) (_hn : n ∈ Finset.Ioo (-(N:ℤ)) N) :
      |(ξ n).im| ≤ 1 ∧ |(η n).im| ≤ 1 := by
    have h := canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num : (1:ENNReal) < 2)
      (weightedBaseToPair w φ) heven n
    exact ⟨hh _ h.1,hh _ h.2⟩
  have hpack := sum_gap_sq_le_of_height_one (Finset.Ioo (-(N:ℤ)) N) ξ η (-b) b
    (by linarith) hbound
    (fun i _ j _ hij => NLS.ComplexAnalysis.re_le_of_complexLexLE (hs.2.2 i j hij)) hheight
  have hcard : ((Finset.Ioo (-(N:ℤ)) N).card : ℝ) = 2*(N:ℝ)-1 := by
    have h := Int.card_Ioo_of_lt (-(N:ℤ)) (N:ℤ) (show -(N:ℤ) < N by omega)
    exact_mod_cast (show ((Finset.Ioo (-(N:ℤ)) N).card : ℤ) = 2*(N:ℤ)-1 by omega)
  change (∑ n ∈ Finset.Ioo (-(N:ℤ)) N, ‖η n-ξ n‖^2) ≤ _
  rw [hcard] at hpack
  convert hpack using 1
  dsimp [b]
  ring

end NLS.ZakharovShabat
