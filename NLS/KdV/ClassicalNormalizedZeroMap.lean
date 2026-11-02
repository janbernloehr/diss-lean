import NLS.KdV.ClassicalCandidateResolvents

/-! # The actual sequence equation for normalized numerator zeros

Candidate frequencies vary in one Hilbert ball. The filled own-factor
resolvent gives a genuine analytic l2 equation on that entire ball times
the selected potential neighborhood.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillZeroCoefficients
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) : NLS.Coeff 2 :=
  (n : ℂ) • Q q (lp.single 2 (n : ℤ) 1)

def classicalHillZeroBracket (N : ℕ)
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  classicalHillZeroCoefficients Q n t.2 (n : ℤ)/(n : ℂ)+
    NLS.Coeff.dualPairing (classicalHillCandidateRow N n k t) (classicalHillZeroCoefficients Q n t.2)

def classicalHillZeroCoordinates (N : ℕ)
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (j : ℤ) : ℂ :=
  if hj : 0 < j then
    let k := positiveIntegerIndex j hj
    if k = n then t.1 j else
      ((classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)/
        (2*classicalHillCriticalFrequency N k t.2*(k : ℂ)))*classicalHillZeroCoefficients Q n t.2 j+
      t.1 j*(1+t.1 j/(2*classicalHillCriticalFrequency N k t.2))*classicalHillZeroBracket N Q n k t
  else t.1 j

def classicalHillZeroMap (N : ℕ)
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : NLS.Coeff 2 :=
  NLS.Coeff.ofFunctionOrZero 2 (classicalHillZeroCoordinates N Q n t)

theorem zeroCoefficients_analytic
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (V : Set (NLS.LinearVolterra.Curve ℂ)) (hQa : AnalyticOnNhd ℂ Q V) (n : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillZeroCoefficients Q n) V := by
  intro q hq
  apply (analyticAt_const (v := (n : ℂ))).smul
  simpa only [Function.comp_def] using!
    ((ContinuousLinearMap.apply ℂ (NLS.Coeff 2) (lp.single 2 (n : ℤ) 1)).analyticAt (Q q)).comp (f := Q) (hQa q hq)

theorem norm_zeroCoefficients_le
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hQ : ‖Q q‖ ≤ 2) :
    ‖classicalHillZeroCoefficients Q n q‖ ≤ 2*(n : ℝ) := by
  rw [classicalHillZeroCoefficients,norm_smul,Complex.norm_natCast]
  have he : ‖(lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2)‖ = 1 := by rw [lp.norm_single (by norm_num),norm_one]
  have hh := (Q q).le_opNorm (lp.single 2 (n : ℤ) 1)
  rw [he,mul_one] at hh
  nlinarith [show (0 : ℝ) ≤ n by positivity]

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem zeroBracket_analytic
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (n k : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillZeroBracket N Q n k) (classicalHillCandidateDomain V) := by
  intro t ht
  have hb := (zeroCoefficients_analytic Q V hQa n t.2 ht.2).comp
    (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.2) analyticAt_snd
  have hc := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp
    (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => classicalHillZeroCoefficients Q n s.2) hb
  have hr := (D.candidateRow_spec n k).2.2 t ht
  have hp := (NLS.Coeff.dualPairing (p := 2) (q := 2)).analyticAt_bilinear
    (classicalHillCandidateRow N n k t,classicalHillZeroCoefficients Q n t.2)
  have hs := hp.comp
    (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ =>
      (classicalHillCandidateRow N n k s,classicalHillZeroCoefficients Q n s.2)) (hr.prod hb)
  exact hc.div_const.add hs

theorem norm_zeroBracket_le
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2) (n k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    ‖classicalHillZeroBracket N Q n k t‖ ≤ 2*(n : ℝ)*(1+64*(1+(n : ℝ)^2)) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.property
  have hb := norm_zeroCoefficients_le Q n t.2 (hQ t.2 ht.2)
  have he := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (classicalHillZeroCoefficients Q n t.2) (n : ℤ)
  have hfirst : ‖classicalHillZeroCoefficients Q n t.2 (n : ℤ)/(n : ℂ)‖ ≤ 2*(n : ℝ) := by
    rw [norm_div,Complex.norm_natCast]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
    nlinarith
  have hs := NLS.Coeff.norm_dualPairing_le (classicalHillCandidateRow N n k t) (classicalHillZeroCoefficients Q n t.2)
  have hpair : ‖NLS.Coeff.dualPairing (classicalHillCandidateRow N n k t) (classicalHillZeroCoefficients Q n t.2)‖ ≤
      (64*(1+(n : ℝ)^2))*(2*(n : ℝ)) :=
    hs.trans (mul_le_mul ((D.candidateRow_spec n k).2.1 t ht) hb (norm_nonneg _) (by positivity))
  exact (norm_add_le _ _).trans (by nlinarith)

theorem zeroCoordinates_analytic
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (n : ℕ+) (j : ℤ) :
    AnalyticOnNhd ℂ (fun t => classicalHillZeroCoordinates N Q n t j) (classicalHillCandidateDomain V) := by
  by_cases hj : 0 < j
  · let k := positiveIntegerIndex j hj
    by_cases hkn : k = n
    · have heq : (fun t => classicalHillZeroCoordinates N Q n t j) = fun t => t.1 j := by
        funext t
        rw [classicalHillZeroCoordinates,dif_pos hj]
        change (if k = n then _ else _) = _
        rw [if_pos hkn]
      rw [heq]
      intro t _
      exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).analyticAt t.1).comp (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.1) analyticAt_fst
    · intro t ht
      have hx := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).analyticAt t.1).comp (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.1) analyticAt_fst
      have hxi := (D.critical_frequency_analytic k t.2 ht.2).comp (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.2) analyticAt_snd
      have hnq := (D.critical_analytic n t.2 ht.2).comp (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.2) analyticAt_snd
      have hb := (zeroCoefficients_analytic Q V hQa n t.2 ht.2).comp (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.2) analyticAt_snd
      have hbc := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).analyticAt _).comp (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => classicalHillZeroCoefficients Q n s.2) hb
      have h2xi : (2 : ℂ)*classicalHillCriticalFrequency N k t.2 ≠ 0 := mul_ne_zero (by norm_num) (D.critical_frequency_ne_zero k t.2 ht.2)
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
      have hmult := ((D.candidate_energy_analytic k t ht).sub hnq).div
        (((analyticAt_const (v := (2 : ℂ))).mul hxi).mul (analyticAt_const (v := (k : ℂ)))) (mul_ne_zero h2xi hk0)
      have hlocal := (analyticAt_const (v := (1 : ℂ))).add (hx.div ((analyticAt_const (v := (2 : ℂ))).mul hxi) h2xi)
      have hh := (hmult.mul hbc).add ((hx.mul hlocal).mul (D.zeroBracket_analytic Q hQa n k t ht))
      have heq : (fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => classicalHillZeroCoordinates N Q n s j) =
          fun s => ((classicalHillCandidateEnergy N k s-classicalHillUniformCriticalPoint N n s.2)/
            (2*classicalHillCriticalFrequency N k s.2*(k : ℂ)))*classicalHillZeroCoefficients Q n s.2 j+
            s.1 j*(1+s.1 j/(2*classicalHillCriticalFrequency N k s.2))*classicalHillZeroBracket N Q n k s := by
        funext s
        rw [classicalHillZeroCoordinates,dif_pos hj]
        change (if k = n then _ else _) = _
        rw [if_neg hkn]
      rw [heq]
      exact hh
  · have heq : (fun t => classicalHillZeroCoordinates N Q n t j) = fun t => t.1 j := by
      funext t
      rw [classicalHillZeroCoordinates,dif_neg hj]
    rw [heq]
    intro t _
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).analyticAt t.1).comp (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.1) analyticAt_fst

/-- The literal filled zero equation is genuinely l2-valued and jointly
Banach analytic on one candidate ball times the common source domain. -/
theorem zeroMap_spec
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2) (n : ℕ+) :
    (∀ t ∈ classicalHillCandidateDomain V, ∀ j : ℤ,
      classicalHillZeroMap N Q n t j = classicalHillZeroCoordinates N Q n t j) ∧
      AnalyticOnNhd ℂ (classicalHillZeroMap N Q n) (classicalHillCandidateDomain V) := by
  let B : ℝ := 2*(n : ℝ)*(1+64*(1+(n : ℝ)^2))
  let M : ℝ := 4*Real.pi*(1+(n : ℝ)^2)
  let C : ℝ := 1+M+2*B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hpoint (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) (j : ℤ) :
      ‖classicalHillZeroCoordinates N Q n t j‖ ≤ C*(‖classicalHillZeroCoefficients Q n t.2 j‖+‖t.1 j‖) := by
    unfold classicalHillZeroCoordinates
    by_cases hj : 0 < j
    · rw [dif_pos hj]
      let k := positiveIntegerIndex j hj
      by_cases hkn : k = n
      · rw [if_pos hkn]
        dsimp only [C]
        nlinarith [norm_nonneg (classicalHillZeroCoefficients Q n t.2 j),norm_nonneg (t.1 j)]
      · rw [if_neg hkn]
        have ha := D.norm_candidate_zero_multiplier_le n k t ht
        have hl := D.norm_candidate_zero_local_factor_le k t ht
        have hg := D.norm_zeroBracket_le Q hQ n k t ht
        have hkj : (k : ℤ) = j := positiveIntegerIndex_int j hj
        rw [hkj] at hl
        calc
          _ ≤ M*‖classicalHillZeroCoefficients Q n t.2 j‖+(‖t.1 j‖*2)*B := by
            apply (norm_add_le _ _).trans
            simp only [norm_mul]
            exact add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
              (mul_le_mul (mul_le_mul_of_nonneg_left hl (norm_nonneg _)) hg (norm_nonneg _) (by positivity))
          _ ≤ _ := by dsimp only [C]; nlinarith [norm_nonneg (classicalHillZeroCoefficients Q n t.2 j),norm_nonneg (t.1 j)]
    · rw [dif_neg hj]
      dsimp only [C]
      nlinarith [norm_nonneg (classicalHillZeroCoefficients Q n t.2 j),norm_nonneg (t.1 j)]
  have hmem (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :=
    NLS.Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound (classicalHillZeroCoordinates N Q n t)
      (classicalHillZeroCoefficients Q n t.2) t.1 C hC (hpoint t ht)
  have he (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) (j : ℤ) :
      classicalHillZeroMap N Q n t j = classicalHillZeroCoordinates N Q n t j :=
    NLS.Coeff.ofFunctionOrZero_apply_of_mem 2 _ (hmem t ht).1 j
  have hU : IsOpen (classicalHillCandidateDomain V) := isOpen_ball.prod D.isOpen
  have hcoord (j : ℤ) : AnalyticOnNhd ℂ (fun t => classicalHillZeroMap N Q n t j) (classicalHillCandidateDomain V) := by
    intro t ht
    exact (D.zeroCoordinates_analytic Q hQa n j t ht).congr (by
      filter_upwards [hU.mem_nhds ht] with s hs
      exact (he s hs j).symm)
  have hbound (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
      ‖classicalHillZeroMap N Q n t‖ ≤ C*(2*(n : ℝ)+Real.pi/16) := by
    have hb := (hmem t ht).2
    have hnorm := norm_zeroCoefficients_le Q n t.2 (hQ t.2 ht.2)
    have hx : ‖t.1‖ < Real.pi/16 := by simpa only [mem_ball,dist_zero_right] using ht.1
    exact hb.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  exact ⟨he,NLS.Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU hcoord _ hbound⟩

end ClassicalAllContourPeriodData
end NLS.KdV
