import NLS.ZakharovShabat.ClassicalSobolevRemainderInterpolation

/-! # The exponent choice in Corollary G.4 -/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Above the G.4 threshold there is a positive interpolation parameter giving ℓp decay. -/
theorem exists_fundamentalFourier_summability_parameter
    (p r : ℝ) (hp : 1 < p) (hr : 1+1/p < r) (hr2 : r ≤ 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ 1+ε ≤ r ∧
      1 < fundamentalFourierDecayExponent ε r*p := by
  have hp0 : 0 < p := by linarith
  have hdiv : 0 < 1/p := by positivity
  have hgap : 1 < (r-1)*p := by
    have h := (div_lt_iff₀ hp0).mp (show 1/p < r-1 by linarith)
    nlinarith
  let ε := ((r-1)*p-1)/(2*p)
  have he : ε*(2*p) = (r-1)*p-1 := div_mul_cancel₀ _ (by positivity : (2*p) ≠ 0)
  have he0 : 0 < ε := div_pos (by linarith) (by positivity)
  have he1 : ε < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
  have her : 1+ε ≤ r := by nlinarith
  refine ⟨ε,he0,he1,her,?_⟩
  unfold fundamentalFourierDecayExponent
  rw [div_mul_eq_mul_div,lt_div_iff₀ (by linarith : 0 < 1-ε)]
  nlinarith

/-- Every Fourier exponent above the threshold admits a smaller exponent at most two.
The target may be infinity. -/
theorem exists_fundamentalFourier_summability_exponents
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q) :
    ∃ r ε : ℝ, 0 < ε ∧ ε < 1 ∧ 1+ε ≤ r ∧ r ≤ 2 ∧
      ENNReal.ofReal r ≤ q ∧ 1 < fundamentalFourierDecayExponent ε r*p := by
  have hthreshold : 1+1/p < 2 := by
    have h := (div_lt_one (by linarith : 0 < p)).mpr hp
    linarith
  have hr : ∃ r : ℝ, 1+1/p < r ∧ r ≤ 2 ∧ ENNReal.ofReal r ≤ q := by
    by_cases hq2 : 2 ≤ q
    · exact ⟨2,hthreshold,le_rfl,by simpa using hq2⟩
    · have hqt : q ≠ ⊤ := ne_top_of_lt (lt_of_not_ge hq2)
      refine ⟨q.toReal,?_,?_,ENNReal.ofReal_toReal_le⟩
      · have h := (ENNReal.toReal_lt_toReal (by simp) hqt).mpr hq
        simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1+1/p)] using h
      · have h := (ENNReal.toReal_le_toReal hqt (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mpr
          (le_of_not_ge hq2)
        simpa using h
  obtain ⟨r,hr,hr2,hrq⟩ := hr
  obtain ⟨ε,he0,he1,her,hep⟩ := exists_fundamentalFourier_summability_parameter p r hp hr hr2
  exact ⟨r,ε,he0,he1,her,hr2,hrq,hep⟩

end NLS.ZakharovShabat
