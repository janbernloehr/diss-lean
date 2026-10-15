import NLS.SequenceSpaces.FiniteInterpolation

/-!
# Sharp interpolation of finite kernel pairings

The entire finite power families give the geometric three-lines constant
B₀^(1-t) B₁^t. Normalization and bilinearity extend the estimate to arbitrary
finite inputs. All endpoint and intermediate exponents are finite and positive.
-/

noncomputable section
open scoped ENNReal
open Complex
namespace NLS.Coeff
/-- Normalized finite inputs satisfy the exact geometric endpoint bound. -/
theorem norm_kernelPair_interpolate_unit_sharp
    {p₀ p₁ q₀ q₁ r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)]
    (hp₀ : 0 < p₀.toReal) (hp₁ : 0 < p₁.toReal)
    (hq₀ : 0 < q₀.toReal) (hq₁ : 0 < q₁.toReal)
    (hr : 0 < r.toReal) (hs : 0 < s.toReal)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1-t)/p₀.toReal + t/p₁.toReal) = 1)
    (hst : s.toReal * ((1-t)/q₀.toReal + t/q₁.toReal) = 1)
    (K : ℤ → ℤ → ℂ) {B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ a b : ℤ →₀ ℂ, ‖kernelPair K a b‖ ≤
      B₀ * ‖ofFinsupp (p := p₀) a‖ * ‖ofFinsupp (p := q₀) b‖)
    (h₁ : ∀ a b : ℤ →₀ ℂ, ‖kernelPair K a b‖ ≤
      B₁ * ‖ofFinsupp (p := p₁) a‖ * ‖ofFinsupp (p := q₁) b‖)
    (a b : ℤ →₀ ℂ) (ha : ‖ofFinsupp (p := r) a‖ ≤ 1)
    (hb : ‖ofFinsupp (p := s) b‖ ≤ 1) : ‖kernelPair K a b‖ ≤ B₀ ^ (1-t) * B₁ ^ t := by
  let A := fun z => powerFamily a (interpolationWeight r.toReal p₀.toReal p₁.toReal z)
  let B := fun z => powerFamily b (interpolationWeight s.toReal q₀.toReal q₁.toReal z)
  let F := fun z => kernelPair K (A z) (B z)
  have hd : Differentiable ℂ F := differentiable_kernelPair_powerFamily K a b _ _ _ _ _ _
  have hbound : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ k ∈ a.support, ∑ n ∈ b.support, ‖K n k‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact norm_kernelPair_powerFamily_le K a b ha hb
      (interpolationWeight_re_pos hr hp₀ hp₁ hz.1 hz.2)
      (interpolationWeight_re_pos hs hq₀ hq₁ hz.1 hz.2)
  have he₀ (z : ℂ) (hz : z.re = 0) : ‖F z‖ ≤ B₀ := by
    have hA : ‖ofFinsupp (p := p₀) (A z)‖ ≤ 1 :=
      norm_powerFamily_le_one hp₀ hr a ha (by rw [interpolationWeight_re, hz]; ring)
    have hB : ‖ofFinsupp (p := q₀) (B z)‖ ≤ 1 :=
      norm_powerFamily_le_one hq₀ hs b hb (by rw [interpolationWeight_re, hz]; ring)
    exact (h₀ (A z) (B z)).trans (by
      calc
        _ ≤ B₀ * 1 * 1 := by gcongr; exact lp.norm_nonneg' _
        _ = B₀ := by ring)
  have he₁ (z : ℂ) (hz : z.re = 1) : ‖F z‖ ≤ B₁ := by
    have hA : ‖ofFinsupp (p := p₁) (A z)‖ ≤ 1 :=
      norm_powerFamily_le_one hp₁ hr a ha (by rw [interpolationWeight_re, hz]; ring)
    have hB : ‖ofFinsupp (p := q₁) (B z)‖ ≤ 1 :=
      norm_powerFamily_le_one hq₁ hs b hb (by rw [interpolationWeight_re, hz]; ring)
    exact (h₁ (A z) (B z)).trans (by
      calc
        _ ≤ B₁ * 1 * 1 := by gcongr; exact lp.norm_nonneg' _
        _ = B₁ := by ring)
  have hthree := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (z := (t : ℂ)) ⟨ht₀, ht₁⟩ hd.diffContOnCl hbound
    (fun z hz => he₀ z hz) (fun z hz => he₁ z hz)
  have ht : F (t : ℂ) = kernelPair K a b := by
    dsimp [F, A, B]
    rw [interpolationWeight_at hrt, interpolationWeight_at hst, powerFamily_one, powerFamily_one]
  rw [ht, ofReal_re] at hthree
  exact hthree


/-- Independent complex scalings factor out of the bilinear kernel pairing. -/
theorem kernelPair_smul (K : ℤ → ℤ → ℂ) (a b : ℤ →₀ ℂ) (c d : ℂ) :
    kernelPair K (c • a) (d • b) = c*d*kernelPair K a b := by
  unfold kernelPair
  rw [Finsupp.sum_smul_index (by intro k; simp)]
  have hi (k : ℤ) (x : ℂ) :
      (d • b).sum (fun n y => c*x*K n k*y) = b.sum (fun n y => c*x*K n k*(d*y)) :=
    Finsupp.sum_smul_index (by intro n; simp)
  simp_rw [hi]
  simp only [Finsupp.sum]
  simp_rw [show ∀ k n : ℤ, c*a k*K n k*(d*b n) = c*d*(a k*K n k*b n) by intro k n; ring]
  simp only [Finset.mul_sum]

/-- Sharp finite interpolation for arbitrary inputs, including zero inputs and bounds. -/
theorem norm_kernelPair_interpolate_sharp
    {p₀ p₁ q₀ q₁ r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)]
    (hp₀ : 0 < p₀.toReal) (hp₁ : 0 < p₁.toReal)
    (hq₀ : 0 < q₀.toReal) (hq₁ : 0 < q₁.toReal)
    (hr : 0 < r.toReal) (hs : 0 < s.toReal)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1-t)/p₀.toReal + t/p₁.toReal) = 1)
    (hst : s.toReal * ((1-t)/q₀.toReal + t/q₁.toReal) = 1)
    (K : ℤ → ℤ → ℂ) {B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ a b : ℤ →₀ ℂ, ‖kernelPair K a b‖ ≤
      B₀ * ‖ofFinsupp (p := p₀) a‖ * ‖ofFinsupp (p := q₀) b‖)
    (h₁ : ∀ a b : ℤ →₀ ℂ, ‖kernelPair K a b‖ ≤
      B₁ * ‖ofFinsupp (p := p₁) a‖ * ‖ofFinsupp (p := q₁) b‖)
    (a b : ℤ →₀ ℂ) :
    ‖kernelPair K a b‖ ≤ (B₀^(1-t)*B₁^t)*‖ofFinsupp (p := r) a‖*‖ofFinsupp (p := s) b‖ := by
  by_cases ha : a = 0
  · simp [ha,kernelPair]
  by_cases hb : b = 0
  · simp [hb,kernelPair]
  have han : 0 < ‖ofFinsupp (p := r) a‖ := by
    apply norm_pos_iff.mpr
    intro he
    apply ha
    apply Finsupp.ext
    intro n
    exact congrArg (fun x : Coeff r => x n) he
  have hbn : 0 < ‖ofFinsupp (p := s) b‖ := by
    apply norm_pos_iff.mpr
    intro he
    apply hb
    apply Finsupp.ext
    intro n
    exact congrArg (fun x : Coeff s => x n) he
  let c : ℂ := (‖ofFinsupp (p := r) a‖ : ℂ)⁻¹
  let d : ℂ := (‖ofFinsupp (p := s) b‖ : ℂ)⁻¹
  have hc : ‖c‖ = ‖ofFinsupp (p := r) a‖⁻¹ := by simp [c,norm_inv,Complex.norm_real]
  have hd : ‖d‖ = ‖ofFinsupp (p := s) b‖⁻¹ := by simp [d,norm_inv,Complex.norm_real]
  have hna : ‖ofFinsupp (p := r) (c • a)‖ ≤ 1 := by
    rw [map_smul,norm_smul,hc,inv_mul_cancel₀ han.ne']
  have hnb : ‖ofFinsupp (p := s) (d • b)‖ ≤ 1 := by
    rw [map_smul,norm_smul,hd,inv_mul_cancel₀ hbn.ne']
  have h := norm_kernelPair_interpolate_unit_sharp hp₀ hp₁ hq₀ hq₁ hr hs ht₀ ht₁ hrt hst
    K hB₀ hB₁ h₀ h₁ (c • a) (d • b) hna hnb
  rw [kernelPair_smul,norm_mul,norm_mul,hc,hd] at h
  have h' := mul_le_mul_of_nonneg_left h (mul_nonneg han.le hbn.le)
  have he : (‖ofFinsupp (p := r) a‖*‖ofFinsupp (p := s) b‖)*
      (‖ofFinsupp (p := r) a‖⁻¹*‖ofFinsupp (p := s) b‖⁻¹*‖kernelPair K a b‖) = ‖kernelPair K a b‖ := by
    field_simp
  rw [he] at h'
  nlinarith only [h']

end NLS.Coeff
