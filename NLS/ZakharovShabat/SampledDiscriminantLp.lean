import NLS.ZakharovShabat.ParitySpectralPairLp
import NLS.ZakharovShabat.SmallCompleteDisplacements
import NLS.ZakharovShabat.DiscriminantExteriorDerivative
import NLS.SequenceSpaces.ParityInterleave

/-!
# Lemma 8.4: locally uniform sampled discriminant errors in lp

Matching each free center with its canonical parity product gives one lp
majorant throughout all half-pi discs. Cauchy supplies the derivative bound
on quarter-pi discs. Complete actual labels are needed only pointwise in the
potential; the common neighborhood and norm bound do not assume continuous
label choices.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common potential neighborhood supplies bounded lp majorants throughout every free disc. -/
theorem exists_uniform_discriminant_disc_majorants (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        ∃ A : Coeff p, ‖A‖ ≤ K ∧
          ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
            ‖canonicalDiscriminant hp ψ z-freeDiscriminant z‖ ≤ ‖A n‖ := by
  obtain ⟨N, _, V, ho, hc, hφ, h0, R, hR, hdata⟩ :=
    exists_uniform_small_completeDisplacements hp hp1 SpectralWeight.one (unitBaseEquiv.symm φ)
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨K, hK, hproducts⟩ := exists_uniform_parityProduct_majorants hp1 hp hR
  have he (ψ : PairSpace p) : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm ψ) = ψ := by
    rw [← unitBaseEquiv_eq, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨unitBaseEquiv.symm ⁻¹' V, ho.preimage unitBaseEquiv.symm.continuous,
    hc.linear_preimage (unitBaseEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).toLinearMap,
    hφ, by simpa only [mem_preimage, map_zero] using h0, 2*K, by positivity, ?_⟩
  intro ψ hψ heven
  obtain ⟨ξ, η, h, hξ, hη, _⟩ := hdata (unitBaseEquiv.symm ψ) hψ (by rw [he]; exact heven)
  obtain ⟨A, B, hA, hB, hevenBound, hoddBound⟩ := hproducts ξ η h.left_displacement h.right_displacement hξ hη
  have hcanon := h.canonicalParity_eq_products hp1
  rw [he] at hcanon
  refine ⟨Coeff.interleave A B, (Coeff.norm_interleave_le A B).trans (by linarith), ?_⟩
  intro n z hz
  have hn : n = 2*(n/2)+n%2 := by omega
  have hr : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases hr with hr | hr
  · have hn' : n = 2*(n/2) := by omega
    rw [hn', Coeff.interleave_even]
    have hv := hevenBound (n/2) z (by rw [← hn']; linarith [Real.pi_pos])
    rw [← hcanon.1, canonicalEven_eq_discriminant_sub_two] at hv
    simpa only [sub_sub_sub_cancel_right] using hv
  · have hn' : n = 2*(n/2)+1 := by omega
    rw [hn', Coeff.interleave_odd]
    have hv := hoddBound (n/2) z (by rw [← hn']; linarith [Real.pi_pos])
    rw [← hcanon.2, canonicalOdd_eq_discriminant_add_two_finite hp hp1 ψ heven] at hv
    simpa only [add_sub_add_right_eq_sub] using hv

/-- The same majorant bounds the trace and its derivative on the source quarter-pi discs. -/
theorem exists_uniform_discriminant_value_derivative_majorants (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        ∃ A : Coeff p, ‖A‖ ≤ K ∧ ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
          ‖canonicalDiscriminant hp ψ z-freeDiscriminant z‖ ≤ ‖A n‖ ∧
          ‖deriv (canonicalDiscriminant hp ψ) z+2*sin z‖ ≤ (4/Real.pi)*‖A n‖ := by
  obtain ⟨U, ho, hc, hφ, h0, K, hK, hb⟩ := exists_uniform_discriminant_disc_majorants hp hp1 φ
  refine ⟨U, ho, hc, hφ, h0, K, hK, fun ψ hψ heven => ?_⟩
  obtain ⟨A, hA, hv⟩ := hb ψ hψ heven
  refine ⟨A, hA, fun n z hz => ⟨hv n z (by linarith [Real.pi_pos]), ?_⟩⟩
  have hf : Differentiable ℂ (fun z => canonicalDiscriminant hp ψ z-freeDiscriminant z) := by
    intro z
    exact (analyticOnNhd_canonicalDiscriminant hp hp1 ψ heven z (mem_univ _)).differentiableAt.sub
      (hasDerivAt_freeDiscriminant z).differentiableAt
  have hd := NLS.ComplexAnalysis.norm_deriv_le_of_closedDisc_bound hf ((Real.pi : ℂ)*n)
    (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi/2) _ (hv n) hz
  rw [deriv_discriminant_error hp hp1 ψ heven] at hd
  convert hd using 1
  ring

/-- Lemma 8.4 with explicit uniform norms for the actual sampled error sequences. -/
theorem exists_uniform_sampled_discriminant_errors (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        ∀ z : ℤ → ℂ, (∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) →
          ∃ a b : Coeff p, ‖a‖ ≤ K ∧ ‖b‖ ≤ (4/Real.pi)*K ∧
            (∀ n, a n = canonicalDiscriminant hp ψ (z n)-2*cos (z n)) ∧
            (∀ n, b n = deriv (canonicalDiscriminant hp ψ) (z n)+2*sin (z n)) := by
  obtain ⟨U, ho, hc, hφ, h0, K, hK, hb⟩ := exists_uniform_discriminant_value_derivative_majorants hp hp1 φ
  refine ⟨U, ho, hc, hφ, h0, K, hK, fun ψ hψ heven z hz => ?_⟩
  obtain ⟨A, hA, hbound⟩ := hb ψ hψ heven
  have hv (n : ℤ) : ‖canonicalDiscriminant hp ψ (z n)-2*cos (z n)‖ ≤ ‖A n‖ :=
    (hbound n (z n) (hz n)).1
  let B : Coeff p := ((4/Real.pi : ℝ) : ℂ) • A
  have hd (n : ℤ) : ‖deriv (canonicalDiscriminant hp ψ) (z n)+2*sin (z n)‖ ≤ ‖B n‖ := by
    simpa only [B, lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)] using (hbound n (z n) (hz n)).2
  let a : Coeff p := ⟨_, (lp.memℓp A).mono' hv⟩
  let b : Coeff p := ⟨_, (lp.memℓp B).mono' hd⟩
  refine ⟨a, b, (lp.norm_mono (zero_lt_one.trans hp1).ne' hv).trans hA,
    (lp.norm_mono (zero_lt_one.trans hp1).ne' hd).trans ?_, fun _ => rfl, fun _ => rfl⟩
  change ‖((4/Real.pi : ℝ) : ℂ) • A‖ ≤ (4/Real.pi)*K
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)]
  exact mul_le_mul_of_nonneg_left hA (by positivity)

/-- The trace and derivative error sequences in Lemma 8.4 belong to the original finite lp space. -/
theorem memℓp_sampled_discriminant_errors (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    Memℓp (fun n => canonicalDiscriminant hp φ (z n)-2*cos (z n)) p ∧
      Memℓp (fun n => deriv (canonicalDiscriminant hp φ) (z n)+2*sin (z n)) p := by
  obtain ⟨_, _, _, hmem, _, _, _, h⟩ := exists_uniform_sampled_discriminant_errors hp hp1 φ
  obtain ⟨a, b, _, _, ha, hb⟩ := h φ hmem hφ z hz
  constructor
  · have h : Memℓp (fun n => a n) p := lp.memℓp a
    simpa only [ha] using h
  · have h : Memℓp (fun n => b n) p := lp.memℓp b
    simpa only [hb] using h

end NLS.ZakharovShabat
