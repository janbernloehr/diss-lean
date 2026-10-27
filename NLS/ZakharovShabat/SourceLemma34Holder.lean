import NLS.ZakharovShabat.SourceLemma34Majorization
import Mathlib.Analysis.MeanInequalities

/-! # The Hölder steps in the proof of Lemma 3.4

The literal far and near sums satisfy the displayed Hölder bounds.
Their numerator moments use the original scalar norms with constant one.
The separately refuted uniform radius simplifications are not used.
-/

noncomputable section
open scoped ENNReal
open Classical
namespace NLS.ZakharovShabat

/-- The compact reciprocal power is exactly the product denominator in the source display. -/
theorem lemma34Holder_weight_eq (n l m : ℤ) {r : ℝ} (hr : 0 < r) (q : ℝ) :
    (((r+|((n-l : ℤ) : ℝ)|)*(r+|((n-m : ℤ) : ℝ)|))⁻¹)^q =
      1/((r+|((n-l : ℤ) : ℝ)|)^q*(r+|((n-m : ℤ) : ℝ)|)^q) := by
  rw [Real.inv_rpow (by positivity), Real.mul_rpow (by positivity) (by positivity), one_div]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed numerator's p-moment is summable on the whole integer product. -/
theorem summable_lemma34NumeratorMoment (hp : p ≠ ⊤) (φ f : Coeff p) :
    Summable (fun lm : ℤ × ℤ => (‖φ (lm.1+lm.2)‖*‖f lm.2‖)^p.toReal) := by
  have hpp : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have h := ((lp.memℓp φ).summable hpp).mul_of_nonneg ((lp.memℓp f).summable hpp)
    (fun _ => by positivity) (fun _ => by positivity)
  let e : (ℤ × ℤ) ≃ (ℤ × ℤ) :=
    { toFun := fun lm => (lm.1+lm.2,lm.2)
      invFun := fun lm => (lm.1-lm.2,lm.2)
      left_inv := by intro lm; ext <;> simp
      right_inv := by intro lm; ext <;> simp }
  apply (e.summable_iff.mpr h).congr
  intro lm
  change ‖φ (lm.1+lm.2)‖^p.toReal * ‖f lm.2‖^p.toReal = _
  exact (Real.mul_rpow (norm_nonneg _) (norm_nonneg _)).symm

/-- The full numerator moment factors into the two original scalar norms. -/
theorem lemma34NumeratorMoment_eq (hp : p ≠ ⊤) (φ f : Coeff p) :
    (∑' lm : ℤ × ℤ, (‖φ (lm.1+lm.2)‖*‖f lm.2‖)^p.toReal) =
      ‖φ‖^p.toReal * ‖f‖^p.toReal := by
  have hpp : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hφ := (lp.memℓp φ).summable hpp
  have hf := (lp.memℓp f).summable hpp
  have hprod := hφ.mul_of_nonneg hf (fun _ => by positivity) (fun _ => by positivity)
  let e : (ℤ × ℤ) ≃ (ℤ × ℤ) :=
    { toFun := fun lm => (lm.1+lm.2,lm.2)
      invFun := fun lm => (lm.1-lm.2,lm.2)
      left_inv := by intro lm; ext <;> simp
      right_inv := by intro lm; ext <;> simp }
  calc
    _ = ∑' lm : ℤ × ℤ, ‖φ (e lm).1‖^p.toReal * ‖f (e lm).2‖^p.toReal := by
      apply tsum_congr
      intro lm
      exact Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
    _ = ∑' lm : ℤ × ℤ, ‖φ lm.1‖^p.toReal * ‖f lm.2‖^p.toReal :=
      e.tsum_eq (fun lm : ℤ × ℤ => ‖φ lm.1‖^p.toReal * ‖f lm.2‖^p.toReal)
    _ = (∑' k : ℤ, ‖φ k‖^p.toReal) * (∑' k : ℤ, ‖f k‖^p.toReal) :=
      (hφ.tsum_mul_tsum hf hprod).symm
    _ = _ := by rw [← lp.norm_rpow_eq_tsum hpp, ← lp.norm_rpow_eq_tsum hpp]


/-- The printed Hölder step holds on every selected subset, before the false radius simplifications. -/
theorem lemma34_masked_holder (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ f : Coeff p) (n : ℤ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (S : Set (ℤ × ℤ)) :
    (∑' lm : ℤ × ℤ, if lm ∈ S then lemma34ProofTerm φ f n r lm else 0) ≤
      (∑' lm : ℤ × ℤ, if lm ∈ S then
        (((r+|((n-lm.1 : ℤ) : ℝ)|)*(r+|((n-lm.2 : ℤ) : ℝ)|))⁻¹)^p.conjExponent.toReal
        else 0)^(1/p.conjExponent.toReal) *
      (∑' lm : ℤ × ℤ, if lm ∈ S then
        (‖φ (lm.1+lm.2)‖*‖f lm.2‖)^p.toReal else 0)^(1/p.toReal) := by
  classical
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hqpos : 0 < p.conjExponent.toReal := hpq.symm.pos
  let a : Coeff p.conjExponent := ⟨_,sourceLemma34_reciprocal_memlp hp n hr hr1⟩
  have ha (k : ℤ) : ‖a k‖ = (r+|((n-k : ℤ) : ℝ)|)⁻¹ := by
    change ‖((r+|((n-k : ℤ) : ℝ)| : ℝ) : ℂ)⁻¹‖ = _
    simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < r+|((n-k : ℤ) : ℝ)|)]
  let W (lm : ℤ × ℤ) := ((r+|((n-lm.1 : ℤ) : ℝ)|)*(r+|((n-lm.2 : ℤ) : ℝ)|))⁻¹
  let B (lm : ℤ × ℤ) := ‖φ (lm.1+lm.2)‖*‖f lm.2‖
  have hw : Summable (fun lm : ℤ × ℤ => (W lm)^p.conjExponent.toReal) := by
    have h := ((lp.memℓp a).summable hqpos).mul_of_nonneg ((lp.memℓp a).summable hqpos)
      (fun _ => by positivity) (fun _ => by positivity)
    apply h.congr
    intro lm
    change ‖a lm.1‖^p.conjExponent.toReal * ‖a lm.2‖^p.conjExponent.toReal = _
    rw [ha,ha,← Real.mul_rpow (by positivity) (by positivity)]
    simp only [W,mul_inv]
  have hb : Summable (fun lm : ℤ × ℤ => (B lm)^p.toReal) := summable_lemma34NumeratorMoment hp φ f
  have hwm : Summable (fun lm : ℤ × ℤ => (if lm ∈ S then W lm else 0)^p.conjExponent.toReal) := by
    apply hw.of_nonneg_of_le
    · intro lm; positivity
    · intro lm
      split_ifs
      · exact le_rfl
      · rw [Real.zero_rpow hqpos.ne']
        exact Real.rpow_nonneg (by dsimp [W]; positivity) _
  have hbm : Summable (fun lm : ℤ × ℤ => (if lm ∈ S then B lm else 0)^p.toReal) := by
    apply hb.of_nonneg_of_le
    · intro lm; positivity
    · intro lm
      split_ifs
      · exact le_rfl
      · rw [Real.zero_rpow hpq.pos.ne']
        exact Real.rpow_nonneg (by dsimp [B]; positivity) _
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq.symm
    (f := fun lm : ℤ × ℤ => if lm ∈ S then W lm else 0)
    (g := fun lm : ℤ × ℤ => if lm ∈ S then B lm else 0)
    (fun lm => by dsimp [W]; split_ifs <;> positivity)
    (fun lm => by dsimp [B]; split_ifs <;> positivity) hwm hbm
  convert h using 1
  · apply tsum_congr
    intro lm
    split_ifs <;> simp [lemma34ProofTerm,W,B,div_eq_mul_inv,mul_comm]
  · congr 2 <;> congr 1 <;> funext lm <;> split_ifs <;>
      simp [W,B,Real.zero_rpow hpq.pos.ne',Real.zero_rpow hqpos.ne']

/-- Every selected numerator moment has the original norm product as an upper bound. -/
theorem lemma34MaskedNumeratorMoment_le (hp : p ≠ ⊤) (φ f : Coeff p)
    (S : Set (ℤ × ℤ)) :
    (∑' lm : ℤ × ℤ, if lm ∈ S then
      (‖φ (lm.1+lm.2)‖*‖f lm.2‖)^p.toReal else 0)^(1/p.toReal) ≤ ‖φ‖*‖f‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hs := summable_lemma34NumeratorMoment hp φ f
  have hle (lm : ℤ × ℤ) :
      (if lm ∈ S then (‖φ (lm.1+lm.2)‖*‖f lm.2‖)^p.toReal else 0) ≤
        (‖φ (lm.1+lm.2)‖*‖f lm.2‖)^p.toReal := by
    split_ifs <;> first | exact le_rfl | positivity
  have hm := hs.of_nonneg_of_le (fun lm => by split_ifs <;> positivity) hle
  have h := Real.rpow_le_rpow (tsum_nonneg (fun lm => by split_ifs <;> positivity))
    (hm.tsum_le_tsum hle hs) (by positivity : 0 ≤ 1/p.toReal)
  rw [lemma34NumeratorMoment_eq hp φ f,
    ← Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    ← Real.rpow_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    mul_one_div_cancel hp0.ne', Real.rpow_one] at h
  exact h

/-- Hölder with the selected reciprocal moment and the original scalar norms. -/
theorem lemma34_masked_holder_norm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ f : Coeff p) (n : ℤ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (S : Set (ℤ × ℤ)) :
    (∑' lm : ℤ × ℤ, if lm ∈ S then lemma34ProofTerm φ f n r lm else 0) ≤
      (∑' lm : ℤ × ℤ, if lm ∈ S then
        (((r+|((n-lm.1 : ℤ) : ℝ)|)*(r+|((n-lm.2 : ℤ) : ℝ)|))⁻¹)^p.conjExponent.toReal
        else 0)^(1/p.conjExponent.toReal) * (‖φ‖*‖f‖) := by
  exact (lemma34_masked_holder hp hp1 φ f n hr hr1 S).trans
    (mul_le_mul_of_nonneg_left (lemma34MaskedNumeratorMoment_le hp φ f S) (by positivity))

/-- The first printed Hölder display, for the exact far index set. -/
theorem lemma34ProofFarSum_le_holder (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ f : Coeff p) (n : ℤ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    lemma34ProofFarSum φ f n r ≤
      (∑' lm : ℤ × ℤ, if ¬ lemma34ProofNear n lm.1 lm.2 then
        (((r+|((n-lm.1 : ℤ) : ℝ)|)*(r+|((n-lm.2 : ℤ) : ℝ)|))⁻¹)^p.conjExponent.toReal
        else 0)^(1/p.conjExponent.toReal) * (‖φ‖*‖f‖) := by
  have h := lemma34_masked_holder_norm hp hp1 φ f n hr hr1
    {lm | ¬ lemma34ProofNear n lm.1 lm.2}
  convert h using 1
  · unfold lemma34ProofFarSum
    apply tsum_congr
    intro lm
    by_cases hn : lemma34ProofNear n lm.1 lm.2 <;> simp [hn]
  · congr 2
    congr 1
    funext lm
    by_cases hn : lemma34ProofNear n lm.1 lm.2 <;> simp [hn]


/-- The near Hölder display retains precisely the symmetric potential remainder. -/
theorem lemma34ProofNearSum_le_holder_tail (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ f : Coeff p) (n : ℤ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    lemma34ProofNearSum φ f n r ≤
      (∑' lm : ℤ × ℤ, if lemma34ProofNear n lm.1 lm.2 then
        (((r+|((n-lm.1 : ℤ) : ℝ)|)*(r+|((n-lm.2 : ℤ) : ℝ)|))⁻¹)^p.conjExponent.toReal
        else 0)^(1/p.conjExponent.toReal) * (‖Coeff.fourierTail n.natAbs φ‖*‖f‖) := by
  rw [← lemma34ProofNearSum_fourierTail φ f n r]
  exact lemma34_masked_holder_norm hp hp1 (Coeff.fourierTail n.natAbs φ) f n hr hr1
    {lm | lemma34ProofNear n lm.1 lm.2}

omit [Fact (1 ≤ p)] in
/-- The endpoint Hölder bound uses a uniform reciprocal weight on the selected set. -/
theorem lemma34MaskedSum_le_one (φ f : Coeff 1) (n : ℤ) {r C : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C) (S : Set (ℤ × ℤ))
    (hW : ∀ lm ∈ S,
      ((r+|((n-lm.1 : ℤ) : ℝ)|)*(r+|((n-lm.2 : ℤ) : ℝ)|))⁻¹ ≤ C) :
    (∑' lm : ℤ × ℤ, if lm ∈ S then lemma34ProofTerm φ f n r lm else 0) ≤
      C * (‖φ‖*‖f‖) := by
  have hs := summable_lemma34ProofTerm (by simp : (1 : ℝ≥0∞) ≠ ⊤) φ f n hr hr1
  have hm : Summable (fun lm : ℤ × ℤ => if lm ∈ S then lemma34ProofTerm φ f n r lm else 0) := by
    apply hs.of_nonneg_of_le
    · intro lm
      split_ifs
      · unfold lemma34ProofTerm; positivity
      · exact le_rfl
    · intro lm; split_ifs
      · exact le_rfl
      · unfold lemma34ProofTerm; positivity
  have hb : Summable (fun lm : ℤ × ℤ => ‖φ (lm.1+lm.2)‖*‖f lm.2‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      summable_lemma34NumeratorMoment (by simp : (1 : ℝ≥0∞) ≠ ⊤) φ f
  have hterm (lm : ℤ × ℤ) (hlm : lm ∈ S) :
      lemma34ProofTerm φ f n r lm ≤ C * (‖φ (lm.1+lm.2)‖*‖f lm.2‖) := by
    unfold lemma34ProofTerm
    rw [div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left (hW lm hlm)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (mul_comm _ _)
  have hle (lm : ℤ × ℤ) :
      (if lm ∈ S then lemma34ProofTerm φ f n r lm else 0) ≤
        C * (‖φ (lm.1+lm.2)‖*‖f lm.2‖) := by
    split_ifs with h
    · exact hterm lm h
    · positivity
  have h := hm.tsum_le_tsum hle (hb.mul_left C)
  have he : (∑' lm : ℤ × ℤ, ‖φ (lm.1+lm.2)‖*‖f lm.2‖) = ‖φ‖*‖f‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      lemma34NumeratorMoment_eq (by simp : (1 : ℝ≥0∞) ≠ ⊤) φ f
  rwa [tsum_mul_left, he] at h

omit [Fact (1 ≤ p)] in
/-- At p=1 the near estimate has the necessary inverse-square radius factor. -/
theorem lemma34ProofNearSum_le_one (φ f : Coeff 1) (n : ℤ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    lemma34ProofNearSum φ f n r ≤ (1/r^2) * (‖Coeff.fourierTail n.natAbs φ‖*‖f‖) := by
  rw [← lemma34ProofNearSum_fourierTail φ f n r]
  apply lemma34MaskedSum_le_one _ _ n hr hr1 (by positivity)
    {lm | lemma34ProofNear n lm.1 lm.2}
  intro lm _
  rw [one_div]
  apply inv_anti₀ (sq_pos_of_pos hr)
  have h := mul_le_mul
    (show r ≤ r+|((n-lm.1 : ℤ) : ℝ)| from le_add_of_nonneg_right (abs_nonneg _))
    (show r ≤ r+|((n-lm.2 : ℤ) : ℝ)| from le_add_of_nonneg_right (abs_nonneg _)) hr.le (by positivity)
  simpa only [pow_two] using h

omit [Fact (1 ≤ p)] in
/-- On the literal far set the endpoint reciprocal weight retains a factor 1/r. -/
theorem lemma34ProofFar_weight_le {n l m : ℤ} {r : ℝ} (hr : 0 < r)
    (hfar : ¬ lemma34ProofNear n l m) :
    ((r+|((n-l : ℤ) : ℝ)|)*(r+|((n-m : ℤ) : ℝ)|))⁻¹ ≤
      2/(r*(r+|(n : ℝ)|)) := by
  have hf := (not_lemma34ProofNear_iff n l m).mp hfar
  have hl : 0 ≤ |((n-l : ℤ) : ℝ)| := abs_nonneg _
  have hm : 0 ≤ |((n-m : ℤ) : ℝ)| := abs_nonneg _
  have hd : r*(r+|(n : ℝ)|)/2 ≤
      (r+|((n-l : ℤ) : ℝ)|)*(r+|((n-m : ℤ) : ℝ)|) := by
    have he (k : ℤ) : |((k-n : ℤ) : ℝ)| = |((n-k : ℤ) : ℝ)| := by
      push_cast
      exact abs_sub_comm _ _
    simp only [he] at hf
    rcases hf with hf | hf
    · nlinarith [mul_nonneg hr.le hl, mul_nonneg hl hm]
    · nlinarith [mul_nonneg hr.le hm, mul_nonneg hl hm]
  have hpos : 0 < r*(r+|(n : ℝ)|)/2 := by positivity
  calc
    _ ≤ (r*(r+|(n : ℝ)|)/2)⁻¹ := inv_anti₀ hpos hd
    _ = _ := by rw [inv_div]

omit [Fact (1 ≤ p)] in
/-- The p=1 far sum decays with the center and retains its inverse-radius factor. -/
theorem lemma34ProofFarSum_le_one (φ f : Coeff 1) (n : ℤ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    lemma34ProofFarSum φ f n r ≤ (2/(r*(r+|(n : ℝ)|))) * (‖φ‖*‖f‖) := by
  have h := lemma34MaskedSum_le_one φ f n hr hr1 (by positivity)
      {lm | ¬ lemma34ProofNear n lm.1 lm.2}
      (fun _ h => lemma34ProofFar_weight_le hr h)
  convert h using 1
  unfold lemma34ProofFarSum
  apply tsum_congr
  intro lm
  by_cases hn : lemma34ProofNear n lm.1 lm.2 <;> simp [hn]

end NLS.ZakharovShabat


