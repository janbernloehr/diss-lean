import NLS.SequenceSpaces.UniformHolderConvolution
import NLS.SequenceSpaces.PuncturedLattice

/-! # Shared reciprocal majorants for varying coefficient rows

Choosing the powered-convolution exponent as the minimum of the output
exponent and the Holder conjugate makes the reciprocal kernel summable.
The resulting output majorant depends only on the fixed weight sequence,
not on the varying lp row.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- A single lr sequence bounds weighted reciprocal sums for every lp
row, with its norm appearing only as a scalar factor. -/
theorem exists_uniform_reciprocal_majorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hr : r ≠ ⊤) (hr1 : 1 < r) (g : Coeff r) :
    ∃ D : Coeff r,
      ‖D‖ ≤ ‖g‖*‖puncturedLattice (min r p.conjExponent)
        (lt_min hr1 ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))‖ ∧
      ∀ a : Coeff p, ∀ n : ℤ,
        Summable (fun j : ℤ => if j = n then 0 else ‖g j‖*‖a j‖/|((n-j:ℤ):ℝ)|) ∧
        (∑' j : ℤ, if j = n then 0 else ‖g j‖*‖a j‖/|((n-j:ℤ):ℝ)|) ≤ ‖a‖*‖D n‖ := by
  have hq1 : 1 < p.conjExponent := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hq : p.conjExponent ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let : Fact (1 ≤ p.conjExponent) := ⟨hq1.le⟩
  let t := min r p.conjExponent
  have ht : 1 < t := lt_min hr1 hq1
  let : Fact (1 ≤ t) := ⟨ht.le⟩
  let K := puncturedLattice t ht
  obtain ⟨D,hD,hrows⟩ := exists_uniform_holder_convolution_majorant
    (ENNReal.HolderConjugate.toReal_of_ne_top hp hq) hr (min_le_left _ _) (min_le_right _ _) g K
  refine ⟨D,hD,?_⟩
  intro a n
  have he (j : ℤ) : ‖a j‖*‖g j*K (n-j)‖ =
      if j = n then 0 else ‖g j‖*‖a j‖/|((n-j:ℤ):ℝ)| := by
    by_cases hj : j = n
    · subst j
      simp [K,puncturedLattice_apply]
    · have hnj : n-j ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
      simp only [K,puncturedLattice_apply,if_neg hj,if_neg hnj,norm_mul,norm_inv,
        Complex.norm_intCast,div_eq_mul_inv]
      ring
  obtain ⟨hS,hB⟩ := hrows a n
  exact ⟨hS.congr he,by simpa only [he] using hB⟩

end NLS.Coeff
