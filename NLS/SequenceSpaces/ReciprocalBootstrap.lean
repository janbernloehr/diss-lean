import NLS.SequenceSpaces.ReciprocalBootstrapStep
import NLS.SequenceSpaces.ReciprocalBootstrapExponents

/-! # Finite reciprocal-row bootstrapping to every exponent above one

A fixed ℓᵖ gap factor supplies a positive gain in reciprocal exponent.
The finite central part, the translated error and every iteration retain
bounds uniform over the entire parameter and row family. Products below
exponent one are embedded into ℓ¹ before Young's inequality is used.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p q₀ : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q₀)]

/-- One initial Banach exponent and the uniform reciprocal inequality imply
uniform bounds in every finite exponent above one, for the same scalar rows. -/
theorem exists_uniform_reciprocal_bootstrap {X : Type*}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq₀ : q₀ ≠ ⊤) (hq₀1 : 1 < q₀)
    (U : Set X) (g : X → Coeff p) (f : X → ℤ → ℤ → ℂ)
    (G A C : ℝ) (hG : 0 ≤ G) (hA : 0 ≤ A) (hC : 0 ≤ C) (K : ℕ)
    (hg : ∀ x ∈ U, ‖g x‖ ≤ G)
    (hinit : ∀ x ∈ U, ∀ n : ℤ, ∃ a : Coeff q₀, ‖a‖ ≤ A ∧ ∀ k, a k = f x n k)
    (hineq : ∀ x ∈ U, ∀ n k : ℤ, K ≤ k.natAbs → ‖f x n k‖ ≤ C*
      ((∑' m, ‖g x m*f x n m‖*‖NLS.Fourier.hilbertKernel (k-m)‖)+
        ‖g x k‖*‖NLS.Fourier.hilbertKernel (n-k)‖)) :
    ∀ t : ℝ≥0∞, t ≠ ⊤ → 1 < t → ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ U, ∀ n : ℤ, ∃ a : Coeff t, ‖a‖ ≤ M ∧ ∀ k, a k = f x n k := by
  intro t ht ht1
  let : Fact (1 ≤ t) := ⟨ht1.le⟩
  by_cases hqt : q₀ ≤ t
  · refine ⟨A,hA,?_⟩
    intro x hx n
    obtain ⟨a,ha,hak⟩ := hinit x hx n
    exact ⟨exponentInclusion hqt a,(norm_exponentInclusion_le hqt a).trans ha,hak⟩
  have htq : t < q₀ := lt_of_not_ge hqt
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hq₀r : 0 < q₀.toReal := ENNReal.toReal_pos (zero_lt_one.trans hq₀1).ne' hq₀
  have htr : 0 < t.toReal := ENNReal.toReal_pos (zero_lt_one.trans ht1).ne' ht
  have htr1 : 1 < t.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal (by simp) ht).mpr ht1
  let a₀ := q₀.toReal⁻¹
  let b := t.toReal⁻¹
  let d := p.toReal⁻¹/2
  have ha₀ : 0 < a₀ := inv_pos.mpr hq₀r
  have hb : 0 < b := inv_pos.mpr htr
  have hb1 : b < 1 := inv_lt_one_of_one_lt₀ htr1
  have hd : 0 < d := by dsimp [d]; positivity
  have hab : a₀ ≤ b := by
    have hreal := (ENNReal.toReal_lt_toReal ht hq₀).mpr htq
    simpa only [one_div,a₀,b] using one_div_le_one_div_of_le htr hreal.le
  let S : Set ℝ := {z | ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ U, ∀ n : ℤ,
    ∃ a : Coeff (ENNReal.ofReal z⁻¹), ‖a‖ ≤ M ∧ ∀ k, a k = f x n k}
  have hstart : a₀ ∈ S := by
    have he : ENNReal.ofReal a₀⁻¹ = q₀ := by simp only [a₀,inv_inv,ENNReal.ofReal_toReal hq₀]
    change ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ U, ∀ n : ℤ,
      ∃ a : Coeff (ENNReal.ofReal a₀⁻¹), ‖a‖ ≤ M ∧ ∀ k, a k = f x n k
    rw [he]
    exact ⟨A,hA,hinit⟩
  have hstep : ∀ z ∈ S, a₀ ≤ z → z < b → min b (z+d) ∈ S := by
    intro z hz haz hzb
    obtain ⟨M,hM,hrows⟩ := hz
    have hz0 : 0 < z := ha₀.trans_le haz
    have hz1 : z < 1 := hzb.trans hb1
    let y := min b (z+d)
    have hy0 : 0 < y := lt_min hb (by linarith)
    have hy1 : y < 1 := (min_le_left _ _).trans_lt hb1
    have hygain : y < p.toReal⁻¹+z := by
      have hyn : y ≤ z+d := min_le_right _ _
      dsimp only [d] at hyn
      linarith [inv_pos.mpr hpr]
    let q := ENNReal.ofReal z⁻¹
    let t' := ENNReal.ofReal y⁻¹
    have hq : q ≠ ⊤ := ENNReal.ofReal_ne_top
    have ht' : t' ≠ ⊤ := ENNReal.ofReal_ne_top
    have hq1 : 1 < q := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr ((one_lt_inv₀ hz0).mpr hz1)
    have ht'1 : 1 < t' := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr ((one_lt_inv₀ hy0).mpr hy1)
    let : Fact (1 ≤ q) := ⟨hq1.le⟩
    let : Fact (1 ≤ t') := ⟨ht'1.le⟩
    have hqi : q⁻¹ = ENNReal.ofReal z := by
      rw [← ENNReal.ofReal_inv_of_pos (inv_pos.mpr hz0),inv_inv]
    have hti : t'⁻¹ = ENNReal.ofReal y := by
      rw [← ENNReal.ofReal_inv_of_pos (inv_pos.mpr hy0),inv_inv]
    have hpi : p⁻¹ = ENNReal.ofReal p.toReal⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hpr,ENNReal.ofReal_toReal hp]
    have hgain : t'⁻¹ < p⁻¹+q⁻¹ := by
      rw [hti,hpi,hqi,← ENNReal.ofReal_add (inv_nonneg.mpr hpr.le) hz0.le]
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hygain
    obtain ⟨r,R,v,hr,hR1,hR,hrR,hv1,_,hH,hY⟩ :=
      NLS.exists_reciprocal_bootstrap_exponents (zero_lt_one.trans hp1) (zero_lt_one.trans hq1) hp ht'1 ht' hgain
    let : Fact (1 ≤ R) := ⟨hR1⟩
    let : Fact (1 ≤ v) := ⟨hv1.le⟩
    let : p.HolderTriple q r := hH
    let J := ‖NLS.Fourier.hilbertKernelCoeffs
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖
    have hJ : 0 ≤ J := lp.norm_nonneg' _
    let M' := (Finset.Icc (-(K:ℤ)) K).card*M+C*(G*M*‖NLS.Fourier.hilbertKernelCoeffs hv1‖+G*J)
    refine ⟨M',by dsimp only [M']; positivity,?_⟩
    intro x hx n
    obtain ⟨a,ha,hak⟩ := hrows x hx n
    obtain ⟨a',ha',hnorm⟩ := exists_reciprocal_bootstrap_step (r := r) (R := R) (t := t')
      hp hp1 hq hr hR hrR hY hv1 (g x) a n K C hC (by
        intro k hk
        simpa only [hak] using hineq x hx n k hk)
    refine ⟨a',hnorm.trans ?_,fun k => (ha' k).trans (hak k)⟩
    dsimp only [M']
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)
    · apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hg x hx) ha (norm_nonneg _) hG) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right (hg x hx) hJ
  have hfinal := NLS.mem_of_clipped_increment a₀ b d hab hd hstart hstep
  have he : ENNReal.ofReal b⁻¹ = t := by simp only [b,inv_inv,ENNReal.ofReal_toReal ht]
  change ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ U, ∀ n : ℤ,
    ∃ a : Coeff (ENNReal.ofReal b⁻¹), ‖a‖ ≤ M ∧ ∀ k, a k = f x n k at hfinal
  rw [he] at hfinal
  exact hfinal

end NLS.Coeff
