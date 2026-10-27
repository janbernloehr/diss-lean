import NLS.ZakharovShabat.SourceLemma3_4

/-! # Radius dependence in the proof of Lemma 3.4

The two intermediate subsum estimates on printed p. 25 cannot hold with
a constant depending only on p. At p=2, single signed Fourier modes
already require additional inverse-radius factors. This does not refute
the main lemma, whose r⁻² estimate is proved in `SourceLemma3_4`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual first resolvent component in the source's signed Fourier basis.
The raw potential coefficient must be reflected at `-(l+m)`. -/
theorem sourceDoubleResolvent_signed_fst_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (φ f : CoeffPair p) (z : ℂ) (hz : z ∉ freeLattice) (l : ℤ) :
    (sourceDoubleResolvent hp φ z hz f).fst (-l) =
      ∑' m : ℤ, φ.fst (-(l+m))*f.snd m /
        ((z-(Real.pi : ℂ)*l)*(z-(Real.pi : ℂ)*m)) := by
  rw [sourceDoubleResolvent_fst_apply]
  apply tsum_congr
  intro m
  rw [show -l-m = -(l+m) by omega]
  simp only [Int.cast_neg, mul_neg, sub_eq_add_neg]

/-- A unit signed first potential mode, represented in the original pair space. -/
def lemma34ProofPotential (a : ℤ) : CoeffPair 2 :=
  WithLp.toLp 2 ((lp.single 2 (-a) 1 : Coeff 2), 0)

/-- The unit positive input mode used in both counterexamples. -/
def lemma34ProofInput : CoeffPair 2 :=
  WithLp.toLp 2 (0, (lp.single 2 1 1 : Coeff 2))

theorem lemma34ProofPotential_signed (a j : ℤ) :
    (lemma34ProofPotential a).fst (-j) = (lp.single 2 a 1 : Coeff 2) j := by
  simp [lemma34ProofPotential, lp.single_apply, Pi.single_apply]

theorem lemma34ProofPotential_norm (a : ℤ) : ‖lemma34ProofPotential a‖ = 1 := by
  simp [lemma34ProofPotential]

theorem lemma34ProofInput_norm : ‖lemma34ProofInput‖ = 1 := by
  simp [lemma34ProofInput]

/-- Every positive test radius admits a parameter in the required strip. -/
theorem lemma34ProofParameter_mem_strip {r : ℝ} (hr : 0 < r) :
    (Real.pi : ℂ) + r*Complex.I ∈ verticalStrip 1 r := by
  constructor
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero,
      Int.cast_one, mul_one, sub_self, abs_zero]
    positivity
  · simp [abs_of_pos hr]

/-- The near witness is an actual single-mode resolvent output. -/
theorem lemma34Proof_near_output (z : ℂ) (hz : z ∉ freeLattice) :
    (sourceDoubleResolvent (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (lemma34ProofPotential 2) z hz lemma34ProofInput).fst (-1) =
        1 / (z-(Real.pi : ℂ))^2 := by
  rw [show (-1 : ℤ) = -(1 : ℤ) by rfl, sourceDoubleResolvent_signed_fst_apply,
    tsum_eq_single (1 : ℤ)]
  · norm_num [lemma34ProofPotential, lemma34ProofInput, pow_two]
  · intro m hm
    simp [lemma34ProofInput, lp.single_apply, hm]

/-- For lambda=pi+i*r the actual near output coefficient has norm r⁻². -/
theorem lemma34Proof_near_output_norm {r : ℝ} (hr : 0 < r)
    (hz : (Real.pi : ℂ) + r*Complex.I ∉ freeLattice) :
    ‖(sourceDoubleResolvent (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (lemma34ProofPotential 2) ((Real.pi : ℂ) + r*Complex.I) hz
        lemma34ProofInput).fst (-1)‖ = 1/r^2 := by
  rw [lemma34Proof_near_output]
  simp [norm_pow, abs_of_pos hr]

/-- The original pair operator itself requires an r⁻² bound for this unit potential. -/
theorem lemma34Proof_near_operator_lower {r : ℝ} (hr : 0 < r)
    (hz : (Real.pi : ℂ) + r*Complex.I ∉ freeLattice) :
    1/r^2 ≤ ‖sourceDoubleResolvent (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (lemma34ProofPotential 2) ((Real.pi : ℂ) + r*Complex.I) hz‖ := by
  let T := sourceDoubleResolvent (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (lemma34ProofPotential 2) ((Real.pi : ℂ) + r*Complex.I) hz
  calc
    _ = ‖(T lemma34ProofInput).fst (-1)‖ := (lemma34Proof_near_output_norm hr hz).symm
    _ ≤ ‖(T lemma34ProofInput).fst‖ := lp.norm_apply_le_norm (by simp) _ _
    _ ≤ ‖T lemma34ProofInput‖ := WithLp.norm_fst_le _ _
    _ ≤ ‖T‖ * ‖lemma34ProofInput‖ := T.le_opNorm _
    _ = _ := by rw [lemma34ProofInput_norm, mul_one]

/-- The printed near set, using real half-widths for all signed indices. -/
def lemma34ProofNear (n l m : ℤ) : Prop :=
  |((m - n : ℤ) : ℝ)| ≤ |(n : ℝ)| / 2 ∧
    |((l - n : ℤ) : ℝ)| ≤ |(n : ℝ)| / 2

/-- The literal nonnegative double-sum summand in the signed convention.
Here `φ` is the printed first signed component, not its raw reflected sequence. -/
def lemma34ProofTerm {p : ℝ≥0∞} (φ f : Coeff p) (n : ℤ) (r : ℝ)
    (lm : ℤ × ℤ) : ℝ :=
  ‖φ (lm.1 + lm.2)‖ * ‖f lm.2‖ /
    ((r + |((n - lm.1 : ℤ) : ℝ)|) * (r + |((n - lm.2 : ℤ) : ℝ)|))

/-- The far subsum over the complement of the printed near set. -/
def lemma34ProofFarSum {p : ℝ≥0∞} (φ f : Coeff p) (n : ℤ) (r : ℝ) : ℝ := by
  classical
  exact ∑' lm : ℤ × ℤ, if ¬ lemma34ProofNear n lm.1 lm.2 then
    lemma34ProofTerm φ f n r lm else 0

/-- The near subsum from the proof, before either Hölder estimate. -/
def lemma34ProofNearSum {p : ℝ≥0∞} (φ f : Coeff p) (n : ℤ) (r : ℝ) : ℝ := by
  classical
  exact ∑' lm : ℤ × ℤ, if lemma34ProofNear n lm.1 lm.2 then
    lemma34ProofTerm φ f n r lm else 0

private theorem proofTerm_single_zero {p : ℝ≥0∞} (a b n : ℤ) (r : ℝ)
    (lm : ℤ × ℤ) (h : lm ≠ (a-b,b)) :
    lemma34ProofTerm (lp.single p a 1) (lp.single p b 1) n r lm = 0 := by
  by_cases hb : lm.2 = b
  · have ha : lm.1 + lm.2 ≠ a := by
      intro ha
      apply h
      ext <;> simp_all
      omega
    simp [lemma34ProofTerm, lp.single_apply, ha]
  · simp [lemma34ProofTerm, lp.single_apply, hb]

/-- With signed potential mode 1 and input mode 1, only (l,m)=(0,1) survives. -/
theorem lemma34ProofFarSum_single (r : ℝ) :
    lemma34ProofFarSum (lp.single 2 1 1) (lp.single 2 1 1) 1 r =
      1 / ((r+1)*r) := by
  rw [lemma34ProofFarSum, tsum_eq_single (0,1)]
  · norm_num [lemma34ProofNear, lemma34ProofTerm]
  · intro lm h
    have hz := proofTerm_single_zero (p := 2) 1 1 1 r lm (by simpa using h)
    simp only [hz, ite_self]

/-- With signed potential mode 2 and input mode 1, only (l,m)=(1,1) survives. -/
theorem lemma34ProofNearSum_single (r : ℝ) :
    lemma34ProofNearSum (lp.single 2 2 1) (lp.single 2 1 1) 1 r =
      1 / r^2 := by
  rw [lemma34ProofNearSum, tsum_eq_single (1,1)]
  · norm_num [lemma34ProofNear, lemma34ProofTerm, pow_two]
  · intro lm h
    have hz := proofTerm_single_zero (p := 2) 2 1 1 r lm (by simpa using h)
    simp only [hz, ite_self]

/-- The near witness's original scalar Fourier tail still has norm one. -/
theorem lemma34ProofNear_tail_norm :
    ‖Coeff.fourierTail 1 (lp.single 2 2 1 : Coeff 2)‖ = 1 := by
  norm_num [Coeff.fourierTail_single]

/-- A radius small enough to defeat either proposed constant. -/
private theorem exists_proof_counterexample_radius (C : ℝ) (hC : 0 ≤ C) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi / 4 ∧ r ≤ 1 ∧ C*r < 1/2 := by
  let r : ℝ := 1 / (4*(C+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have he : (4*(C+1))*r = 1 := by dsimp [r]; field_simp
  have hr4 : r ≤ 1/4 := by nlinarith
  refine ⟨r, hr, ?_, by linarith, ?_⟩
  · have hp := Real.one_le_pi_div_two
    linarith
  · nlinarith

/-- At p=2 the printed far estimate fails for every nonnegative constant,
even with two fixed unit scalar sequences and n=1. -/
theorem lemma3_4_proof_far_bound_false (C : ℝ) (hC : 0 ≤ C) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi / 4 ∧
      C / (r + |(1 : ℝ)|)^(1/(2 : ℝ)) *
          ‖(lp.single 2 1 1 : Coeff 2)‖ * ‖(lp.single 2 1 1 : Coeff 2)‖ <
        lemma34ProofFarSum (lp.single 2 1 1) (lp.single 2 1 1) 1 r := by
  obtain ⟨r,hr,hrπ,hr1,hCr⟩ := exists_proof_counterexample_radius C hC
  refine ⟨r,hr,hrπ,?_⟩
  rw [lemma34ProofFarSum_single]
  norm_num only [abs_one, lp.norm_single, norm_one, mul_one]
  have hs : 1 ≤ (r+1)^(1/(2 : ℝ)) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hdiv : C / (r+1)^(1/(2 : ℝ)) ≤ C :=
    div_le_self hC hs
  apply hdiv.trans_lt
  apply (lt_div_iff₀ (show 0 < (r+1)*r by positivity)).mpr
  have hCr0 : 0 ≤ C*r := mul_nonneg hC hr.le
  have hprod := mul_le_mul_of_nonneg_left (show r+1 ≤ 2 by linarith) hCr0
  nlinarith

/-- At p=2 the printed exponent 2/p is 1, while the near sum grows as r⁻². -/
theorem lemma3_4_proof_near_bound_false (C : ℝ) (hC : 0 ≤ C) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi / 4 ∧
      C / r^(2/(2 : ℝ)) * ‖Coeff.fourierTail 1 (lp.single 2 2 1 : Coeff 2)‖ *
          ‖(lp.single 2 1 1 : Coeff 2)‖ <
        lemma34ProofNearSum (lp.single 2 2 1) (lp.single 2 1 1) 1 r := by
  obtain ⟨r,hr,hrπ,_,hCr⟩ := exists_proof_counterexample_radius C hC
  refine ⟨r,hr,hrπ,?_⟩
  rw [lemma34ProofNearSum_single, lemma34ProofNear_tail_norm]
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one,
    lp.norm_single, norm_one, mul_one]
  apply (div_lt_div_iff₀ hr (sq_pos_of_pos hr)).mpr
  nlinarith [mul_pos (show 0 < 1-C*r by linarith) hr]

end NLS.ZakharovShabat
