import NLS.ZakharovShabat.AppendixDReciprocalBounds

/-! # Remark D.7: the quadratic remainder on every source disc

The signed-row square and the squared absolute row both lie in ell-(p/2).
A global product estimate therefore gives a stronger remainder than the
printed ell-(p/2) plus ell-(1+) statement, including 1 < p < 2.
-/
noncomputable section
open Set Metric
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The omitted relative product with its signed linear contribution removed. -/
def appendixDQuadraticRemainder (r : Coeff ⊤) (a : Coeff p) (n : ℤ) (z : ℂ) : ℂ :=
  appendixDRelativeProductError r a n z-∑' m, appendixDReciprocalTerm r a n z m

/-- The common half-exponent quasi-norm bound on two norm balls. -/
def appendixDQuadraticBound (hp1 : 1 < p) (hp : p ≠ ⊤) (c B A : ℝ) : ℝ :=
  let X := (appendixDSignedRowConstant hp1 hp c B*A)^2
  let Y := c^2*(A^2*squaredAbsoluteRowConstant hp1 hp)
  Real.exp ((c/2)*absoluteSampledRowConstant hp*A)/2*
    max (X+Y) ((X^((p/2).toReal)+Y^((p/2).toReal))^((p/2).toReal)⁻¹)

/-- One half-exponent majorant controls the remainder at all disc points simultaneously. -/
theorem exists_appendixDQuadraticMajorant (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c B A : ℝ} {N : ℕ}
    (hc : 0 < c) (hB : 0 ≤ B) (hr : ‖r‖ ≤ B) (ha : ‖a‖ ≤ A)
    (hsep : AppendixDReferenceSeparated r c N) :
    ∃ b : Coeff (p/2),
      (∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ refinedResonantDisk n,
        ‖appendixDQuadraticRemainder r a n z‖ ≤ ‖b n‖) ∧
      ‖b‖ ≤ appendixDQuadraticBound hp1 hp c B A := by
  have hA : 0 ≤ A := (norm_nonneg a).trans ha
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  have hhalf : 0 < (p/2).toReal := by simp only [ENNReal.toReal_div,ENNReal.toReal_ofNat]; positivity
  have hhalfne : p/2 ≠ 0 := (ENNReal.toReal_pos_iff.mp hhalf).1.ne'
  obtain ⟨L,hL,hLn⟩ := exists_appendixDSignedRowSup hp1 hp r a hc hB hr hsep
  obtain ⟨Q,hQ,hQn⟩ := exists_appendixDSquaredRowSup hp1 hp r a hc hsep
  let E := Real.exp ((c/2)*absoluteSampledRowConstant hp*A)/2
  let U := Coeff.magnitude (halfSquareCoeff L)
  let V := ((c^2:ℝ):ℂ) • Coeff.magnitude Q
  let b := (E:ℂ) • (U+V)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hb (n : ℤ) : ‖b n‖ = E*(‖L n‖^2+c^2*‖Q n‖) := by
    change ‖(E:ℂ)*(Coeff.magnitude (halfSquareCoeff L) n+
      ((c^2:ℝ):ℂ)*Coeff.magnitude Q n)‖ = _
    simp only [Coeff.magnitude_apply,halfSquareCoeff_apply,norm_pow,← Complex.ofReal_mul,
      ← Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ E*(‖L n‖^2+c^2*‖Q n‖))]
  refine ⟨b,?_,?_⟩
  · intro n hn z hz
    obtain ⟨hs,hS,_⟩ := appendixDReciprocalTerm_bounds hp r a hc hsep hn hz
    have heq : appendixDQuadraticRemainder r a n z =
        (∏' m, (1+appendixDReciprocalTerm r a n z m))-1-
          ∑' m, appendixDReciprocalTerm r a n z m := by
      rw [appendixDQuadraticRemainder,appendixDRelativeProductError_eq r a hc hsep hn hz]
      rfl
    rw [heq,hb]
    apply (NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_sub_tsum_le_global_signed
      (appendixDReciprocalTerm r a n z) hs).trans
    have hSA : (∑' m, ‖appendixDReciprocalTerm r a n z m‖) ≤
        (c/2)*absoluteSampledRowConstant hp*A := hS.trans
      (mul_le_mul_of_nonneg_left ha
        (mul_nonneg (by positivity) (absoluteSampledRowConstant_nonneg hp)))
    have hlinear := pow_le_pow_left₀ (norm_nonneg _) (hL n hn z hz) 2
    have hquadratic := hQ n hn z hz
    apply mul_le_mul (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hSA) (by norm_num))
      (add_le_add hlinear hquadratic) (by positivity) hE
  · have hC : 0 ≤ appendixDSignedRowConstant hp1 hp c B := by
      have hH := hilbertTransformBound_nonneg hp1 hp
      unfold appendixDSignedRowConstant
      positivity
    have hLnorm : ‖L‖ ≤ appendixDSignedRowConstant hp1 hp c B*A :=
      hLn.trans (mul_le_mul_of_nonneg_left ha hC)
    have hUn : ‖U‖ ≤ (appendixDSignedRowConstant hp1 hp c B*A)^2 := by
      rw [Coeff.norm_magnitude_quasi hhalfne]
      exact (norm_halfSquareCoeff_le hp L).trans
        (pow_le_pow_left₀ (norm_nonneg _) hLnorm 2)
    have hQnorm : ‖Q‖ ≤ A^2*squaredAbsoluteRowConstant hp1 hp := hQn.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ha 2) (by apply lp.norm_nonneg'))
    have hVn : ‖V‖ ≤ c^2*(A^2*squaredAbsoluteRowConstant hp1 hp) := by
      rw [lp.norm_const_smul hhalfne,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg c),
        Coeff.norm_magnitude_quasi hhalfne]
      exact mul_le_mul_of_nonneg_left hQnorm (sq_nonneg c)
    have hsum := Coeff.norm_add_le_uniform hhalf U V hUn hVn
    change ‖(E:ℂ) • (U+V)‖ ≤ _
    rw [lp.norm_const_smul hhalfne,Complex.norm_real,Real.norm_of_nonneg hE]
    exact mul_le_mul_of_nonneg_left hsum hE

/-- The literal supremum of the remainder norm over each disc, zero below the cutoff. -/
def appendixDQuadraticSup (r : Coeff ⊤) (a : Coeff p) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then
    sSup ((fun z => ‖appendixDQuadraticRemainder r a n z‖) '' refinedResonantDisk n)
  else 0

/-- The literal disc supremum is a half-exponent sequence with the same uniform bound. -/
theorem exists_appendixDQuadraticSup (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c B A : ℝ} {N : ℕ}
    (hc : 0 < c) (hB : 0 ≤ B) (hr : ‖r‖ ≤ B) (ha : ‖a‖ ≤ A)
    (hsep : AppendixDReferenceSeparated r c N) :
    ∃ b : Coeff (p/2),
      (∀ n, b n = ((appendixDQuadraticSup r a N n):ℂ)) ∧
      ‖b‖ ≤ appendixDQuadraticBound hp1 hp c B A := by
  classical
  obtain ⟨b,hb,hbn⟩ := exists_appendixDQuadraticMajorant hp1 hp r a hc hB hr ha hsep
  have hpoint (n : ℤ) : 0 ≤ appendixDQuadraticSup r a N n ∧
      appendixDQuadraticSup r a N n ≤ ‖b n‖ := by
    by_cases hn : N ≤ n.natAbs
    · have hcenter : (Real.pi:ℂ)*n ∈ refinedResonantDisk n := by
        simp only [refinedResonantDisk,mem_ball,dist_self]
        positivity
      have hne : ((fun z => ‖appendixDQuadraticRemainder r a n z‖) '' refinedResonantDisk n).Nonempty :=
        ⟨_,⟨_,hcenter,rfl⟩⟩
      have hupper : ∀ u ∈ ((fun z => ‖appendixDQuadraticRemainder r a n z‖) '' refinedResonantDisk n),
          u ≤ ‖b n‖ := by
        rintro u ⟨z,hz,rfl⟩
        exact hb n hn z hz
      simp only [appendixDQuadraticSup,if_pos hn]
      exact ⟨(norm_nonneg _).trans (le_csSup ⟨_,hupper⟩ ⟨_,hcenter,rfl⟩),csSup_le hne hupper⟩
    · simp only [appendixDQuadraticSup,if_neg hn]
      exact ⟨le_rfl,norm_nonneg _⟩
  have hdom (n : ℤ) : ‖((appendixDQuadraticSup r a N n):ℂ)‖ ≤ ‖b n‖ := by
    rw [Complex.norm_real,Real.norm_of_nonneg (hpoint n).1]
    exact (hpoint n).2
  let d : Coeff (p/2) := ⟨fun n => ((appendixDQuadraticSup r a N n):ℂ),(lp.memℓp b).mono' hdom⟩
  refine ⟨d,fun _ => rfl,?_⟩
  have hpPos : 0 < p := zero_lt_one.trans hp1
  exact (lp.norm_mono (ENNReal.div_ne_zero.mpr ⟨hpPos.ne',by norm_num⟩) hdom).trans hbn

end NLS.ZakharovShabat
