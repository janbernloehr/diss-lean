import NLS.SequenceSpaces.PeriodOneMassResolvent
import NLS.SequenceSpaces.BoundedScalarProducts

/-! Squaring an L2 displacement from a signed lattice loses precisely
one index weight. Constant energy translations retain that conclusion. -/
noncomputable section
open Complex
namespace NLS

/-- The signed index times the inverse bracket is uniformly bounded by one. -/
theorem norm_index_mul_inverseBracket_le_one (n : ℤ) :
    ‖(n:ℂ)*inverseBracketCoefficients n‖ ≤ 1 := by
  rw [norm_mul,Complex.norm_intCast,norm_inverseBracketCoefficients_apply,
    ← div_eq_mul_inv]
  exact (div_le_one (by positivity : 0 < 1+|(n:ℝ)|)).mpr (by linarith)

/-- Squared lattice coordinates with an L2 displacement have an
inverse-bracket weighted L2 energy displacement, including the central index. -/
theorem memlp_inverseBracket_squared_lattice_error (a c : ℂ) (d : Coeff 2) :
    Memℓp (fun n : ℤ => inverseBracketCoefficients n*
      ((a*n+d n)^2-c-(a*n)^2)) 2 := by
  have hf : Memℓp (fun n : ℤ => ((n:ℂ)*inverseBracketCoefficients n)*d n) 2 := by
    simpa only [smul_eq_mul] using memlp_smul_of_bounded_scalar
      (fun n : ℤ => (n:ℂ)*inverseBracketCoefficients n) (fun n => d n)
      (lp.memℓp d) 1 norm_index_mul_inverseBracket_le_one
  have hg : Memℓp (fun n : ℤ => inverseBracketCoefficients n*(d n*d n)) 2 := by
    simpa only [smul_eq_mul] using memlp_smul_of_bounded_vector
      (fun n : ℤ => inverseBracketCoefficients n) (fun n => d n*d n)
      (lp.memℓp inverseBracketCoefficients) (‖d‖*‖d‖) (fun n => by
        rw [norm_mul]
        exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) d n)
          (lp.norm_apply_le_norm (by norm_num) d n) (norm_nonneg _) (norm_nonneg _))
  have hm := ((hf.const_mul (2*a)).add hg).sub
    ((lp.memℓp inverseBracketCoefficients).const_mul c)
  convert! hm using 1
  funext n
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

end NLS
