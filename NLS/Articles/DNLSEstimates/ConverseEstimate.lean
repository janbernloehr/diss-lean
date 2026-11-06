import NLS.Articles.DNLSEstimates.ActionEstimates
import NLS.ZakharovShabat.SobolevHamiltonianThirdActionBound
import NLS.ZakharovShabat.SourceActionMomentComparison

/-!
# Lemma 16 with its mass-dependent remainder

The zero index needs a small-potential case: it need not satisfy the
strict central-index hypothesis of Proposition 12. For small H¹ norm its
entire gap lies in [-1/2,1/2], so the first action already dominates it.
Otherwise the central comparison with the third action has no added one
in its H¹ factor. This retains both printed action exponents in Lemma 16.
-/
noncomputable section
open Set NLS.ZakharovShabat
namespace NLS.Articles.DNLSEstimates

/-- Exact zero-index localization, including arbitrarily small potentials. -/
theorem zero_gap_localization
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈
      pairParitySubspace 0)
    (hn : 8*‖φ‖^2 ≤ 1) (ζ : ℝ)
    (hζ : ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair _ φ) heven 0).re
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair _ φ) heven 0).re) :
    |ζ| ≤ ‖φ‖^2 + Real.sqrt 2*‖φ‖ := by
  simpa [quadraticLocalizationRadius] using
    H1_gap_point_localization φ heven 0 (by simpa using hn) ζ hζ

/-- Outside the small zero-mode case the original central radius works
without an added one in its quadratic potential factor. -/
theorem central_gap_bound
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈
      pairParitySubspace 0)
    (n : ℤ) (hn : n = 0 ∨ 1+|(n : ℝ)| < 8*‖φ‖^2)
    (hP : 1/4 < ‖φ‖) (ζ : ℝ)
    (hζ : ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair _ φ) heven n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair _ φ) heven n).re) :
    |ζ| ≤ 8*Real.pi*‖φ‖^2 := by
  by_cases hc : 1+|(n : ℝ)| < 8*‖φ‖^2
  · exact H1_gap_point_central_bound φ heven n hc ζ hζ
  · have hn0 : n = 0 := hn.resolve_right hc
    subst n
    have hz := zero_gap_localization φ heven (by simpa using le_of_not_gt hc) ζ hζ
    have hs : Real.sqrt 2 ≤ 3/2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hmul := mul_le_mul_of_nonneg_right hs (norm_nonneg φ)
    have hsq : (3/2 : ℝ)*‖φ‖ ≤ 6*‖φ‖^2 := by nlinarith
    nlinarith [Real.pi_gt_three, sq_nonneg ‖φ‖]

/-- A gap bounded by B has the scaled third-action comparison. -/
theorem higherAction_le_third_of_gap_bound (ψ : realTypeSourceSubmodule 2)
    (n : ℤ) (m : ℕ) (hm : 1 ≤ m) (B : ℝ)
    (hB : ∀ ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n).re
      (canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n).re, |ζ| ≤ B) :
    4^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) ≤
      (2*B)^(2*(m-1))*(4*sourceRealHigherAction (by simp) (by norm_num) ψ n 2) := by
  have h := sourceRealHigherAction_even_level_le (by simp) (by norm_num)
    ψ n 1 (m-1) B hB
  rw [show 2*1+2*(m-1) = 2*m by omega] at h
  have hp : (4 : ℝ)^m = 4*2^(2*(m-1)) := by
    calc
      (4 : ℝ)^m = 4^((m-1)+1) :=
        congrArg (fun k => (4 : ℝ)^k) (by omega)
      _ = 4*(2 : ℝ)^(2*(m-1)) := by rw [pow_succ, pow_mul]; norm_num; ring
  calc
    _ ≤ 4^m*(B^(2*(m-1))*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*1)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [hp, mul_pow]; ring

/-- Pointwise comparison used in Lemma 16, with the small zero index
included in the first-action term rather than the central third-action term. -/
theorem higherAction_le_action_add_third (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ =
      periodOnePotential ψ.val) (n : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    4^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) ≤
      sourceWeightedActionTerm ψ m n +
      (16*Real.pi)^(2*(m-1))*‖φ‖^(4*(m-1))*
        (4*sourceRealHigherAction (by simp) (by norm_num) ψ n 2) := by
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈
      pairParitySubspace 0 := hφ ▸ periodOnePotential_mem ψ.val
  have hT := sourceRealHigherAction_even_nonneg (by simp) (by norm_num) ψ n 1
  by_cases hext : n ≠ 0 ∧ 8*‖φ‖^2 ≤ 1+|(n : ℝ)|
  · have h := (sourceRealHigherAction_H1_exterior_bounds ψ φ hφ n hext.1 hext.2 m).2
    rw [← norm_sourceRealAction] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have hc : n = 0 ∨ 1+|(n : ℝ)| < 8*‖φ‖^2 := by
      by_cases h0 : n = 0
      · exact Or.inl h0
      · exact Or.inr (lt_of_not_ge (fun h => hext ⟨h0,h⟩))
    by_cases hP : ‖φ‖ ≤ 1/4
    · have hsmall : 8*‖φ‖^2 ≤ 1 := by nlinarith [norm_nonneg φ]
      have hn0 : n = 0 := hc.resolve_right (by
        intro h
        nlinarith [abs_nonneg (n : ℝ)])
      subst n
      have hgap (ζ : ℝ) (hζ : ζ ∈ Icc
          (canonicalPeriodicLeft (by simp) (by norm_num)
            (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) 0).re
          (canonicalPeriodicRight (by simp) (by norm_num)
            (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) 0).re) : |ζ| ≤ 1/2 := by
        have hz := zero_gap_localization φ heven hsmall ζ (by simpa only [hφ] using hζ)
        have hs : Real.sqrt 2 ≤ 3/2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
        have hmul := mul_le_mul_of_nonneg_right hs (norm_nonneg φ)
        nlinarith [norm_nonneg φ]
      have h := sourceRealHigherAction_even_level_le (by simp) (by norm_num)
        ψ 0 0 m (1/2) hgap
      simp only [Nat.mul_zero, Nat.zero_add, sourceRealHigherAction_zero] at h
      have hscale := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (4 : ℝ)^m)
      have hp : (4 : ℝ)^m*(1/2)^(2*m) = 1 := by
        rw [pow_mul, ← mul_pow]; norm_num
      rw [← mul_assoc, hp, one_mul] at hscale
      have heq : sourceWeightedActionTerm ψ m 0 =
          (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property 0).re := by
        simp [sourceWeightedActionTerm, norm_sourceRealAction]
      rw [← heq] at hscale
      exact hscale.trans (le_add_of_nonneg_right (by positivity))
    · have h := higherAction_le_third_of_gap_bound ψ n m hm
        (8*Real.pi*‖φ‖^2) (fun ζ hζ => central_gap_bound φ heven n hc
          (lt_of_not_ge hP) ζ (by simpa only [hφ] using hζ))
      have hp : (2*(8*Real.pi*‖φ‖^2))^(2*(m-1)) =
          (16*Real.pi)^(2*(m-1))*‖φ‖^(4*(m-1)) := by
        rw [show (2 : ℝ)*(8*Real.pi*‖φ‖^2) = (16*Real.pi)*‖φ‖^2 by ring,
          mul_pow, ← pow_mul]
        congr 2
        omega
      rw [hp] at h
      exact h.trans (le_add_of_nonneg_left (by unfold sourceWeightedActionTerm; positivity))

/-- Summation retains the physical H¹ power without an added one. -/
theorem oddHamiltonian_le_actions_add_energy (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevOddHamiltonian m hm a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n) +
      (16*Real.pi)^(2*(m-1))*‖sourcePiSobolevCoordinates m 1 hm a.val‖^(4*(m-1))*
        (periodOneSobolevHamiltonian (higherSobolevToH1 m hm a.val)).re := by
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  let φ := normalizedWeightedPeriodOne (SpectralWeight.piSobolev 1 (by norm_num))
    (sourcePiSobolevCoordinates m 1 hm a.val)
  let C : ℝ := (16*Real.pi)^(2*(m-1))*‖sourcePiSobolevCoordinates m 1 hm a.val‖^(4*(m-1))
  have hJ := sourceRealHigherActions_summable m hm a
  have hW := sourceWeightedAction_summable_on_Hm m hm a
  have hT : Summable (fun n : ℤ => sourceRealHigherAction (by simp) (by norm_num) ψ n 2) := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using
      sourceH1_realThirdActions_summable (realHigherSobolevToH1 m hm a)
  have hpoint (n : ℤ) : 4^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) ≤
      sourceWeightedActionTerm ψ m n+C*(4*sourceRealHigherAction (by simp) (by norm_num) ψ n 2) := by
    simpa only [φ,C,norm_normalizedWeightedPeriodOne] using
      higherAction_le_action_add_third ψ φ
        (weightedBaseToPair_sourcePiSobolevOne m hm a.val) n m hm
  have hsum := (hJ.mul_left ((4 : ℝ)^m)).tsum_le_tsum hpoint
    (hW.add ((hT.mul_left 4).mul_left C))
  rw [tsum_mul_left, Summable.tsum_add hW ((hT.mul_left 4).mul_left C),
    tsum_mul_left, tsum_mul_left] at hsum
  have hh := congrArg Complex.re (sobolevOddHamiltonian_eq_real_action_sum m hm a)
  simp only [Complex.ofReal_re] at hh
  have ht := sourceH1_four_mul_sum_realThirdActions (realHigherSobolevToH1 m hm a)
  rw [sourceH1RealSource_realHigherSobolevToH1] at ht
  rw [← hh,ht] at hsum
  exact hsum

/-- The scalar conversion preserves separately the mass and weighted-action
powers of the paper, instead of replacing both by a larger weighted moment. -/
theorem lemma_sixteen_budget (m : ℕ) (hm : 1 ≤ m) (P M S : ℝ)
    (_hP : 0 ≤ P) (hM : 0 ≤ M) (hMS : M ≤ S)
    (hnorm : P^2 ≤ 3*(S+M^2)) :
    (16*Real.pi)^(2*(m-1))*P^(4*(m-1))*(S+2*M^2) ≤
      (64*Real.pi)^(2*m)*(1+M)^(2*m-1)*S^(2*m-1) := by
  have hS : 0 ≤ S := hM.trans hMS
  have hM2 : M^2 ≤ M*S := by nlinarith
  have hnorm' : P^2 ≤ 3*((1+M)*S) := by nlinarith
  have henergy : S+2*M^2 ≤ 2*((1+M)*S) := by nlinarith
  have hco : 2*(48*Real.pi)^(2*(m-1)) ≤ (64*Real.pi)^(2*m) := by
    have hpow : (48*Real.pi)^(2*(m-1)) ≤ (64*Real.pi)^(2*(m-1)) := by
      gcongr
      linarith [Real.pi_pos]
    calc
      _ ≤ (64*Real.pi)^2*(64*Real.pi)^(2*(m-1)) := by
        gcongr
        nlinarith [Real.pi_gt_three]
      _ = (64*Real.pi)^(2+2*(m-1)) := by rw [pow_add]
      _ = _ := by congr 1; omega
  calc
    _ = (16*Real.pi)^(2*(m-1))*(P^2)^(2*(m-1))*(S+2*M^2) := by
      rw [← pow_mul, show 2*(2*(m-1)) = 4*(m-1) by omega]
    _ ≤ (16*Real.pi)^(2*(m-1))*(3*((1+M)*S))^(2*(m-1))*(2*((1+M)*S)) := by
      gcongr
    _ = (2*(48*Real.pi)^(2*(m-1)))*(1+M)^(2*m-1)*S^(2*m-1) := by
      simp only [mul_pow]
      have hc : (16*Real.pi)^(2*(m-1))*3^(2*(m-1)) = (48*Real.pi)^(2*(m-1)) := by
        rw [← mul_pow]; congr 1; ring
      have he : 2*m-1 = 2*(m-1)+1 := by omega
      rw [he, pow_succ, pow_succ]
      linear_combination hc * (2*((1+M)^(2*(m-1))*S^(2*(m-1))*(1+M)*S))
    _ ≤ _ := by gcongr

/-- Lemma 16 with the literal printed mass and weighted-moment exponents,
on the full real H^m domain and for every m>=1. -/
theorem lemma_sixteen (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    (4 : ℝ)^m*(∑' n : ℤ,
      (sourceIndexedHigherAction (by simp) (by norm_num) n (2*m)
        (higherSobolevSourceInclusion m a.val)).re) ≤
      actionMoment ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m +
      (64*Real.pi)^(2*m)*
        (1+actionMoment ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0)^(2*m-1)*
        (actionMoment ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1)^(2*m-1) := by
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  let M := ∑' n : ℤ, sourceWeightedActionTerm ψ 0 n
  let S := ∑' n : ℤ, sourceWeightedActionTerm ψ 1 n
  have hM : 0 ≤ M := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  have hMS : M ≤ S := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using
      sourceH1_action_mass_le_weighted (realHigherSobolevToH1 m hm a)
  have hnorm : ‖sourcePiSobolevCoordinates m 1 hm a.val‖^2 ≤ 3*(S+M^2) := by
    have h := sourceH1_third_norm_sq_le_actions (realHigherSobolevToH1 m hm a)
    rw [sourceH1RealSource_realHigherSobolevToH1] at h
    change (1/3 : ℝ)*‖sourcePhysicalH1Coordinates (higherSobolevToH1 m hm a.val)‖^2 ≤ S+M^2 at h
    rw [sourcePhysicalH1Coordinates_higherSobolevToH1] at h
    change (1/3 : ℝ)*‖sourcePiSobolevCoordinates m 1 hm a.val‖^2 ≤ S+M^2 at h
    linarith
  have henergy : (periodOneSobolevHamiltonian (higherSobolevToH1 m hm a.val)).re ≤ S+2*M^2 := by
    have h := sourceH1_energy_le_weighted_actions (realHigherSobolevToH1 m hm a)
    rw [sourceH1RealSource_realHigherSobolevToH1] at h
    change (periodOneSobolevHamiltonian (higherSobolevToH1 m hm a.val)).re ≤ S+2*M^2 at h
    exact h
  have h := (oddHamiltonian_le_actions_add_energy m hm a).trans
    (add_le_add le_rfl (le_trans
      (mul_le_mul_of_nonneg_left henergy (by positivity))
      (lemma_sixteen_budget m hm _ M S (norm_nonneg _) hM hMS hnorm)))
  have hh := congrArg Complex.re (sobolevOddHamiltonian_eq_real_action_sum m hm a)
  simp only [Complex.ofReal_re] at hh
  rw [hh] at h
  change _ ≤ (∑' n : ℤ, sourceWeightedActionTerm ψ m n)+
    (64*Real.pi)^(2*m)*(1+M)^(2*m-1)*S^(2*m-1) at h
  simp only [actionMoment, sourceIndexedWeightedActionTerm_eq]
  convert h using 1
  congr 1
  apply tsum_congr
  intro n
  simpa only [Complex.ofReal_re] using
    congrArg Complex.re (sourceIndexedHigherAction_eq_real (by simp) (by norm_num) ψ n (2*m))

end NLS.Articles.DNLSEstimates
