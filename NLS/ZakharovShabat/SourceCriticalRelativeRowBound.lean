import NLS.ZakharovShabat.SourceCriticalRelativeComparison
import NLS.Fourier.AbsoluteReciprocalYoungRows

/-! # Linear reciprocal-row bounds for the actual product differences

The exponential factor in the relative-product estimate is bounded by a
full displacement norm. The remaining factor retains its entire absolute
reciprocal row, so arbitrary Young exponents can be used in the root
bootstrap rather than collapsing that row to a scalar Hölder bound.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Separation bounds the relative-product error by the literal absolute Cauchy row. -/
theorem tsum_sourceRootRelativePerturbation_le_reciprocalRow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (a b : Coeff p) (z : ℂ)
    (d : ℝ) (hd : 0 < d)
    (hsep : ∀ m : ℤ, m ≠ k → d*|((m-k : ℤ) : ℝ)| ≤ ‖displacedRoots b m-z‖) :
    (∑' m, ‖sourceRootRelativePerturbation k a b z m‖) ≤
      d⁻¹*(∑' m, ‖(a-b) m‖*‖NLS.Fourier.hilbertKernel (k-m)‖) := by
  have hs := (NLS.Fourier.summable_absoluteSampledRow hp (a-b) k).mul_left d⁻¹
  have hu := (summable_sourceRootRelativePerturbation hp hp1 k a b z d hd hsep).1
  rw [← tsum_mul_left]
  apply hu.tsum_le_tsum _ hs
  intro m
  by_cases hm : m=k
  · simp only [sourceRootRelativePerturbation,if_pos hm,norm_zero]
    positivity
  have hmk : (m-k : ℤ) ≠ 0 := sub_ne_zero.mpr hm
  have hdist : 0 < d*|((m-k : ℤ) : ℝ)| := mul_pos hd (by exact_mod_cast abs_pos.mpr hmk)
  have hlat : ‖NLS.Fourier.hilbertKernel (k-m)‖ = |((m-k : ℤ) : ℝ)|⁻¹ := by
    rw [NLS.Fourier.hilbertKernel,norm_neg,norm_inv,Complex.norm_intCast]
    simp only [Int.cast_sub,abs_sub_comm]
  rw [sourceRootRelativePerturbation,if_neg hm,norm_div,hlat]
  change ‖(a-b) m‖/‖displacedRoots b m-z‖ ≤ _
  calc
    _ ≤ ‖(a-b) m‖/(d*|((m-k : ℤ) : ℝ)|) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hdist (hsep m hm)
    _ = _ := by rw [div_eq_mul_inv,mul_inv]; ring

/-- A norm bound controls only the exponential; the linear reciprocal row is retained. -/
theorem SourceIsolatingNeighborhoods.norm_quotient_sub_critical_le_reciprocalRow
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (k : ℤ) (a : Coeff p)
    (z : ℂ) (hz : z ∈ closure (D k)) (M L : ℝ)
    (hM : ‖sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ M)
    (hL : ‖a-sourceCriticalDisplacement hp hp1 ψ‖ ≤ L) :
    ‖sourceSingleRootQuotientJointProduct hp hp1 k (z,(a,ψ))-
      sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤
      (M*Real.exp (c*L*‖Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖)*c)*
          (∑' m, ‖(a-sourceCriticalDisplacement hp hp1 ψ) m‖*‖NLS.Fourier.hilbertKernel (k-m)‖) := by
  let b := sourceCriticalDisplacement hp hp1 ψ
  let S := ∑' m, ‖sourceRootRelativePerturbation k a b z m‖
  let κ := ‖Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖
  have hc : 0 < c := zero_lt_one.trans_le hD.one_le
  have hsep : ∀ m : ℤ, m ≠ k → c⁻¹*|((m-k : ℤ) : ℝ)| ≤ ‖displacedRoots b m-z‖ := by
    simpa only [b,sourceCriticalDisplacement,displacedRoots_canonicalCriticalDisplacement,sourceCriticalRoot] using
      hD.critical_relative_separation ψ hψ k z hz
  obtain ⟨_,hSb,hprod⟩ := hD.norm_quotient_sub_critical_le ψ hψ k a z hz
  have hSL : S ≤ c*L*κ := hSb.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hc.le) (lp.norm_nonneg' _))
  have hrow : S ≤ c*(∑' m, ‖(a-b) m‖*‖NLS.Fourier.hilbertKernel (k-m)‖) := by
    simpa only [inv_inv] using
      tsum_sourceRootRelativePerturbation_le_reciprocalRow hp hp1 k a b z c⁻¹ (inv_pos.mpr hc) hsep
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hfactor : ‖sourceCriticalDeletedQuotient hp hp1 k ψ z‖*Real.exp S ≤ M*Real.exp (c*L*κ) :=
    mul_le_mul hM (Real.exp_le_exp.mpr hSL) (Real.exp_nonneg _) hM0
  calc
    _ ≤ ‖sourceCriticalDeletedQuotient hp hp1 k ψ z‖*Real.exp S*S := hprod
    _ ≤ (M*Real.exp (c*L*κ))*(c*(∑' m, ‖(a-b) m‖*‖NLS.Fourier.hilbertKernel (k-m)‖)) :=
      mul_le_mul hfactor hrow (tsum_nonneg (fun _ => norm_nonneg _)) (mul_nonneg hM0 (Real.exp_nonneg _))
    _ = _ := by ring

/-- Every Young triple with kernel exponent above one gives the corresponding
sequence majorant for these actual product differences. -/
theorem SourceIsolatingNeighborhoods.norm_quotient_sub_critical_le_youngMajorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    {r t q : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ t)] [Fact (1 ≤ q)]
    (hY : YoungRelation r t q) (ht1 : 1 < t)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (k : ℤ) (a : Coeff p)
    (u : Coeff r) (hu : ∀ m, (a-sourceCriticalDisplacement hp hp1 ψ) m = u m)
    (z : ℂ) (hz : z ∈ closure (D k)) (M L : ℝ)
    (hM : ‖sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ M)
    (hL : ‖a-sourceCriticalDisplacement hp hp1 ψ‖ ≤ L) :
    ‖sourceSingleRootQuotientJointProduct hp hp1 k (z,(a,ψ))-
      sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤
      (M*Real.exp (c*L*‖Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖)*c)*
          ‖NLS.Fourier.absoluteReciprocalYoungMajorant hY ht1 u k‖ := by
  rw [NLS.Fourier.norm_absoluteReciprocalYoungMajorant_apply]
  simpa only [hu] using hD.norm_quotient_sub_critical_le_reciprocalRow ψ hψ k a z hz M L hM hL

end NLS.ZakharovShabat
