import NLS.ZakharovShabat.SourceSingleRootQuotientAbsolute
import NLS.ComplexAnalysis.RelativeProductComparison
import NLS.SequenceSpaces.Translation
import NLS.SequenceSpaces.PuncturedLattice

/-! # Quantitative comparison of actual deleted spectral products

The absolute relative perturbation is a Cauchy row in the difference
of the root displacements. Hölder gives a uniform bound under spectral
separation. The exact products then have a linear comparison estimate.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The unused factor is zero; every retained factor is a true relative root perturbation. -/
def sourceRootRelativePerturbation (k : ℤ) (a b : Coeff p) (z : ℂ) (m : ℤ) : ℂ :=
  if m=k then 0 else (a m-b m)/(displacedRoots b m-z)

/-- Pointwise separation gives a summable relative perturbation and an explicit Hölder bound. -/
theorem summable_sourceRootRelativePerturbation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (a b : Coeff p) (z : ℂ)
    (d : ℝ) (hd : 0 < d)
    (hsep : ∀ m : ℤ, m ≠ k → d*|((m-k : ℤ) : ℝ)| ≤ ‖displacedRoots b m-z‖) :
    Summable (fun m => ‖sourceRootRelativePerturbation k a b z m‖) ∧
      (∑' m, ‖sourceRootRelativePerturbation k a b z m‖) ≤
        d⁻¹*‖a-b‖*‖Coeff.puncturedLattice p.conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ := by
  have hq1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let : Fact (1 ≤ p.conjExponent) := ⟨hq1.le⟩
  let L := Coeff.shift k (Coeff.puncturedLattice p.conjExponent hq1)
  have hb := lp.tsum_mul_le_mul_norm (ENNReal.HolderConjugate.toReal_of_ne_top hp hq) (a-b) L
  have hs := hb.1.mul_left d⁻¹
  have hbound (m : ℤ) : ‖sourceRootRelativePerturbation k a b z m‖ ≤ d⁻¹*(‖(a-b) m‖*‖L m‖) := by
    by_cases hm : m=k
    · simp only [sourceRootRelativePerturbation,if_pos hm,norm_zero]
      positivity
    have hmk : (m-k : ℤ) ≠ 0 := sub_ne_zero.mpr hm
    have hlat : ‖L m‖ = |((m-k : ℤ) : ℝ)|⁻¹ := by
      simp only [L,Coeff.shift_apply,Coeff.puncturedLattice_apply,if_neg hmk,norm_inv,Complex.norm_intCast]
    have hdist : 0 < d*|((m-k : ℤ) : ℝ)| := mul_pos hd (by exact_mod_cast abs_pos.mpr hmk)
    rw [sourceRootRelativePerturbation,if_neg hm,norm_div,hlat]
    change ‖(a-b) m‖/‖displacedRoots b m-z‖ ≤ _
    calc
      _ ≤ ‖(a-b) m‖/(d*|((m-k : ℤ) : ℝ)|) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hdist (hsep m hm)
      _ = _ := by rw [div_eq_mul_inv,mul_inv]; ring
  have habs := hs.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  refine ⟨habs,(habs.tsum_le_tsum hbound hs).trans ?_⟩
  rw [tsum_mul_left]
  have hn : ‖L‖ = ‖Coeff.puncturedLattice p.conjExponent hq1‖ := Coeff.norm_shift _ _
  exact (mul_le_mul_of_nonneg_left hb.2 (inv_nonneg.mpr hd.le)).trans_eq (by rw [hn]; ring)

/-- The two actual quotient products satisfy the relative-factor comparison bound. -/
theorem norm_sourceSingleRootQuotient_sub_le_relative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (k : ℤ)
    (a b : Coeff p) (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ k)
    (d : ℝ) (hd : 0 < d)
    (hsep : ∀ m : ℤ, m ≠ k → d*|((m-k : ℤ) : ℝ)| ≤ ‖displacedRoots b m-z‖) :
    ‖sourceSingleRootQuotientJointProduct hp hp1 k (z,(a,ψ))-
      sourceSingleRootQuotientJointProduct hp hp1 k (z,(b,ψ))‖ ≤
      ‖sourceSingleRootQuotientJointProduct hp hp1 k (z,(b,ψ))‖ *
        Real.exp (∑' m, ‖sourceRootRelativePerturbation k a b z m‖) *
          (∑' m, ‖sourceRootRelativePerturbation k a b z m‖) := by
  have hsum := (summable_sourceRootRelativePerturbation hp hp1 k a b z d hd hsep).1
  apply NLS.ComplexAnalysis.norm_product_difference_le _ _ _ _ _
    (hasProd_sourceSingleRootQuotientFactor hp hp1 ψ a z k hz)
    (hasProd_sourceSingleRootQuotientFactor hp hp1 ψ b z k hz) hsum
  intro m
  by_cases hm : m=k
  · simp [sourceSingleRootQuotientFactor,sourceRootRelativePerturbation,hm]
  have hB : displacedRoots b m-z ≠ 0 := norm_pos_iff.mp
    ((mul_pos hd (by exact_mod_cast abs_pos.mpr (sub_ne_zero.mpr hm : m-k ≠ 0))).trans_le (hsep m hm))
  have hw := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z (hz m hm)
  simp only [sourceSingleRootQuotientFactor,sourceRootRelativePerturbation,if_neg hm]
  unfold displacedRoots at hB ⊢
  field_simp [hB,hw]
  ring
end NLS.ZakharovShabat
