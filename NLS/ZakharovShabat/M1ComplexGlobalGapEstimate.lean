import NLS.ZakharovShabat.M1RealGlobalGapEstimate
import NLS.ZakharovShabat.M1ComplexCentralGap
import NLS.ZakharovShabat.SpectralStripNeighborhood

/-! # Proposition 25.5: the global bound near real potentials

A single weight-independent open neighborhood of the real L² potential
space has spectral height less than one. The extra imaginary contribution
costs at most 64 w[16 P²]² P², which fits inside the printed constant 265 π².
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- The source numerical budget also accommodates the finite imaginary contribution. -/
theorem gap_global_265_height_budget (q W : ℝ) (hq : 0 ≤ q) (hW : 1 ≤ W) :
    W^2*(256*Real.pi^2*q^2+64*q)+(18*q+(432/5)*q^2) ≤
      265*Real.pi^2*W^2*(1+q)*q := by
  have hW2 : 1 ≤ W^2 := by nlinarith
  have hpi : 432/5 ≤ 9*Real.pi^2 := by nlinarith [Real.pi_gt_d2]
  have hl : 64*W^2+18 ≤ 265*Real.pi^2*W^2 := by
    have hc : 82 ≤ 265*Real.pi^2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg W)]
  have hq' : 432/5 ≤ 9*Real.pi^2*W^2 :=
    hpi.trans (by nlinarith [mul_le_mul_of_nonneg_left hW2 (by positivity : 0 ≤ 9*Real.pi^2)])
  have h1 := mul_le_mul_of_nonneg_right hl hq
  have h2 := mul_le_mul_of_nonneg_right hq' (sq_nonneg q)
  nlinarith

/-- At the source cutoff, central complex gaps obey the horizontal-plus-height budget. -/
theorem M1_canonicalGap_central_budget_of_height_one (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (hh : ∀ z ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ), |z.im| ≤ 1) :
    let N := ⌊8*‖φ‖^2⌋₊
    (∑ n ∈ Finset.Ioo (-(N:ℤ)) N,
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ≤
      (w.realExtension (16*‖φ‖^2))^2*(256*Real.pi^2*‖φ‖^4+64*‖φ‖^2) := by
  dsimp only
  let N := ⌊8*‖φ‖^2⌋₊
  have hfloor : (N:ℝ) ≤ 8*‖φ‖^2 := Nat.floor_le (by positivity)
  have hN : 8*‖φ‖^2 ≤ 1+(N:ℝ) := by have h := Nat.lt_floor_add_one (8*‖φ‖^2); dsimp [N]; linarith
  change (∑ n ∈ Finset.Ioo (-(N:ℤ)) N, _) ≤ _
  by_cases hpos : 0 < N
  · have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hpos
    have hc := weighted_finite_gap_sq_le w (Finset.Ioo (-(N:ℤ)) N)
      (canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
      (16*‖φ‖^2) (((2*(N:ℝ)-1)*Real.pi)^2+4*(2*(N:ℝ)-1))
      (fun n hn => by
        have hn' := Finset.mem_Ioo.mp hn
        have hi : |2*n| ≤ 2*(N:ℤ)-2 := by apply abs_le.mpr; constructor <;> omega
        have hr : |((2*n:ℤ):ℝ)| ≤ 2*(N:ℝ)-2 := by exact_mod_cast hi
        linarith)
      (M1_canonicalGap_central_sq_le_of_height_one w hw φ heven hh N hpos hN)
    have hwidth : (2*(N:ℝ)-1)*Real.pi ≤ 16*‖φ‖^2*Real.pi := by
      apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
      linarith
    have hs := pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ 2*(N:ℝ)-1) Real.pi_pos.le) hwidth 2
    refine hc.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    nlinarith
  · have he : N = 0 := by omega
    simp only [he,Nat.cast_zero,neg_zero,Finset.Ioo_self,Finset.sum_empty]
    positivity

/-- The global estimate holds whenever the actual original spectrum has height at most one. -/
theorem M1_canonicalGap_global_summable_and_le_of_height_one (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (hh : ∀ z ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ), |z.im| ≤ 1) :
    Summable (fun n : ℤ =>
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ∧
    (∑' n : ℤ, (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ≤
      265*Real.pi^2*(w.realExtension (16*‖φ‖^2))^2*(1+‖φ‖^2)*‖φ‖^2 := by
  let N := ⌊8*‖φ‖^2⌋₊
  have hN : 8*‖φ‖^2 ≤ 1+(N:ℝ) := by have h := Nat.lt_floor_add_one (8*‖φ‖^2); dsimp [N]; linarith
  obtain ⟨hs,he⟩ := sum_eq_central_add_tail _ N
    (M1_canonicalGap_tail_summable_and_le w hw φ heven N hN).1
  refine ⟨hs,?_⟩
  rw [he]
  have ht := M1_canonicalGap_tail_quartic_le w hw φ heven N hN
  have hc := M1_canonicalGap_central_budget_of_height_one w hw φ heven hh
  have hb := gap_global_265_height_budget (‖φ‖^2) (w.realExtension (16*‖φ‖^2))
    (sq_nonneg _) (w.one_le_realExtension _)
  have hp : (‖φ‖^2)^2 = ‖φ‖^4 := by ring
  rw [hp] at hb
  exact (add_le_add hc ht).trans hb

/-- Proposition 25.5's global bound on a single open neighborhood of all real even potentials. -/
theorem M1_canonicalGap_global_summable_and_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (hφ : (⟨weightedBaseToPair w φ,heven⟩ : pairParitySubspace (p := 2) 0) ∈
      evenSpectralStripNeighborhood (by simp)) :
    Summable (fun n : ℤ =>
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ∧
    (∑' n : ℤ, (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ≤
      265*Real.pi^2*(w.realExtension (16*‖φ‖^2))^2*(1+‖φ‖^2)*‖φ‖^2 :=
  M1_canonicalGap_global_summable_and_le_of_height_one w hw φ heven
    (fun z hz => (abs_im_lt_one_of_mem_evenSpectralStripNeighborhood (by simp) _ hφ z hz).le)

/-- The same bound on the original source neighborhood, for every weighted realization. -/
theorem M1_source_canonicalGap_global_summable_and_le (ψ : CoeffPair 2)
    (hψ : ψ ∈ sourceSpectralStripNeighborhood (by simp))
    (w : SpectralWeight) (hw : w.HasLinearFactor) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ) :
    Summable (fun n : ℤ =>
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖)^2) ∧
    (∑' n : ℤ, (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖)^2) ≤
      265*Real.pi^2*(w.realExtension (16*‖φ‖^2))^2*(1+‖φ‖^2)*‖φ‖^2 := by
  have heven : weightedBaseToPair w φ ∈ pairParitySubspace 0 := hφ ▸ periodOnePotential_mem ψ
  have hm : (⟨weightedBaseToPair w φ,heven⟩ : pairParitySubspace (p := 2) 0) ∈
      evenSpectralStripNeighborhood (by simp) := by
    have he : (⟨weightedBaseToPair w φ,heven⟩ : pairParitySubspace (p := 2) 0) =
        ⟨periodOnePotential ψ,periodOnePotential_mem ψ⟩ := Subtype.ext hφ
    rw [he]
    exact hψ
  simpa only [hφ] using M1_canonicalGap_global_summable_and_le w hw φ heven hm

end NLS.ZakharovShabat
