import NLS.SequenceSpaces.PositiveFlatBlocks

/-! # Total action has no continuous larger-exponent extension

Finite nonnegative blocks keep mass one while converging to zero in every
ell^q with q>1, including infinity. This is the introductory mass obstruction.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- A finite nonnegative block with total action one. -/
def positiveMassBlock (p : ℝ≥0∞) (N : ℕ) : Coeff p :=
  (((((N+1:ℕ):ℝ)⁻¹) : ℝ) : ℂ) • positiveUnitBlock p N

theorem norm_positiveMassBlock (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (N : ℕ) :
    ‖positiveMassBlock p N‖ = ((N+1:ℕ):ℝ)^(1/p.toReal-1) := by
  rw [positiveMassBlock, norm_smul, Complex.norm_of_nonneg (by positivity),
    norm_positiveUnitBlock p hp N, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity)]
  congr 1
  ring

theorem positiveMassBlock_exponent {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (N : ℕ) :
    exponentInclusion hpq (positiveMassBlock p N) = positiveMassBlock q N := by
  rw [positiveMassBlock, map_smul, positiveUnitBlock_exponent, positiveMassBlock]

theorem positiveMassBlock_mem_nonnegativeLocus (p : ℝ≥0∞) (N : ℕ) :
    positiveMassBlock p N ∈ nonnegativeLocus p := by
  intro n
  simp only [positiveMassBlock,positiveUnitBlock,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    lp.coeFn_sum,Finset.sum_apply,lp.single_apply,Pi.single_apply]
  constructor
  · simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero]
    have h : (∑ k ∈ Finset.range (N+1), if n = (k:ℤ) then (1:ℂ) else 0).im = 0 := by
      rw [Complex.im_sum]
      apply Finset.sum_eq_zero
      intro k _
      split_ifs <;> rfl
    rw [h,mul_zero]
  · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    apply mul_nonneg (by positivity)
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro k _
    split_ifs <;> norm_num

/-- The blocks have exactly unit mass, not merely a norm lower bound. -/
theorem tsum_positiveMassBlock (N : ℕ) : (∑' n : ℤ, positiveMassBlock 1 N n) = 1 := by
  let L := lp.tsumCLM ℂ ℤ ℂ
  have hs (k : ℤ) : L (lp.single 1 k (1:ℂ)) = 1 := by
    change (∑' n : ℤ, (lp.single 1 k (1:ℂ) : Coeff 1) n) = 1
    simp [lp.single_apply]
  change L (positiveMassBlock 1 N) = 1
  rw [positiveMassBlock, map_smul, positiveUnitBlock, map_sum]
  simp only [hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  push_cast
  exact inv_mul_cancel₀ (by exact_mod_cast (Nat.succ_ne_zero N))

/-- Unit-mass blocks converge to zero in every finite action exponent above one. -/
theorem tendsto_positiveMassBlock_finite {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (h1q : 1 < q) : Tendsto (positiveMassBlock q) atTop (𝓝 0) := by
  have hqR : 1 < q.toReal := by
    exact_mod_cast (ENNReal.toReal_lt_toReal (by norm_num) hq).mpr h1q
  have he : 0 < 1 - 1/q.toReal := by
    apply sub_pos.mpr
    exact (div_lt_one (by linarith : 0 < q.toReal)).mpr hqR
  have ht := (tendsto_rpow_neg_atTop he).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_positiveMassBlock q hq, neg_sub, Function.comp_def] using! ht

/-- The endpoint follows through the contractive inclusion of ell2 in ell-infinity. -/
theorem tendsto_positiveMassBlock {q : ℝ≥0∞} [Fact (1 ≤ q)] (h1q : 1 < q) :
    Tendsto (positiveMassBlock q) atTop (𝓝 0) := by
  by_cases hq : q = ⊤
  · subst q
    have h := (exponentInclusion (show (2:ℝ≥0∞) ≤ ⊤ from le_top)).continuous.continuousAt.tendsto.comp
      (tendsto_positiveMassBlock_finite (q := 2) (by simp) (by norm_num))
    simpa only [Function.comp_def, map_zero, positiveMassBlock_exponent] using h
  · exact tendsto_positiveMassBlock_finite hq h1q

/-- Total action has no continuous extension at zero even relative to the
nonnegative cone, for every larger exponent, including infinity. -/
theorem not_continuousWithinAt_mass_extension {q : ℝ≥0∞} [Fact (1 ≤ q)] (h1q : 1 < q)
    (G : Coeff q → ℂ) (U : Set (Coeff q)) (hU : U ∈ 𝓝 (0:Coeff q))
    (hagree : ∀ a : Coeff 1, a ∈ nonnegativeLocus 1 →
      exponentInclusion h1q.le a ∈ U →
      G (exponentInclusion h1q.le a) = ∑' n : ℤ, a n) :
    ¬ ContinuousWithinAt G (nonnegativeLocus q) 0 := by
  intro hG
  have ht := tendsto_positiveMassBlock h1q
  have hw : Tendsto (positiveMassBlock q) atTop (𝓝[nonnegativeLocus q] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall
      (positiveMassBlock_mem_nonnegativeLocus q)⟩
  have hzero : G 0 = 0 := by
    have h := hagree 0 (zero_mem_nonnegativeLocus 1) (by simpa using mem_of_mem_nhds hU)
    simpa using h
  have hlim : Tendsto (fun N => G (positiveMassBlock q N)) atTop (𝓝 0) := by
    simpa only [hzero, Function.comp_def] using hG.tendsto.comp hw
  have hone : ∀ᶠ N in atTop, G (positiveMassBlock q N) = 1 := by
    filter_upwards [ht.eventually hU] with N hNU
    have h := hagree (positiveMassBlock 1 N) (positiveMassBlock_mem_nonnegativeLocus 1 N)
      (by rw [positiveMassBlock_exponent]; exact hNU)
    simpa only [positiveMassBlock_exponent, tsum_positiveMassBlock] using h
  have heq : (fun _ : ℕ => (1 : ℂ)) =ᶠ[atTop] fun N => G (positiveMassBlock q N) := by
    filter_upwards [hone] with N hN
    exact hN.symm
  have hlim1 : Tendsto (fun N => G (positiveMassBlock q N)) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' heq
  exact zero_ne_one (tendsto_nhds_unique hlim hlim1)

end NLS.Coeff
