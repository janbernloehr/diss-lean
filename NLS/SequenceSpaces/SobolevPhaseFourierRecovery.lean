import NLS.SequenceSpaces.SobolevPhaseDifferenceRemainder
import NLS.SequenceSpaces.SobolevDerivative

/-! # Recovering a root Fourier remainder from its phase

Two one-order smoother phase errors and a small inverse-index perturbation recover the original root Fourier expansion.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A phase Fourier expansion and an absorbable phase-difference error
recover the corresponding root Fourier expansion with one order of gain. -/
theorem exists_sobolev_phase_fourier_remainder
    (r : ℝ) (a : WeightedCoeff (Weight.sobolev r) p)
    (e k : WeightedCoeff (Weight.sobolev (r+1)) p) (u d : ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n, u n = e.val n-k.val n-I*a.val n)
    (hsmall : ∀ n, ‖u n+I*d n‖ ≤ (1/2:ℝ)*‖d n‖)
    (hdecay : ∀ n : ℤ, (1+|(n:ℝ)|)*‖u n+I*d n‖ ≤ C*‖d n‖) :
    ∃ f : WeightedCoeff (Weight.sobolev (r+1)) p,
      (∀ n, f.val n = d n-a.val n) ∧
      ‖f‖ ≤ (2*C)*(‖e‖+‖k‖+‖a‖)+‖e‖+‖k‖ := by
  let hle : r ≤ r+1 := by linarith
  let v : WeightedCoeff (Weight.sobolev r) p :=
    sobolevInclusion hle e-sobolevInclusion hle k-I • a
  have hv (n : ℤ) : v.val n = u n := by
    simp only [v,sub_val,sobolevInclusion_apply,smul_val,hu]
  have hvn : ‖v‖ ≤ ‖e‖+‖k‖+‖a‖ := by
    have h := norm_sub_le (sobolevInclusion hle e-sobolevInclusion hle k) (I • a)
    simp only [norm_smul,norm_I,one_mul] at h
    have h' := norm_sub_le (sobolevInclusion hle e) (sobolevInclusion hle k)
    linarith [norm_sobolevInclusion_le hle e,norm_sobolevInclusion_le hle k]
  obtain ⟨_,R,_,hR,_,hRn⟩ := exists_sobolev_phase_difference_remainder r v d C hC
    (fun n => by simpa only [hv] using hsmall n)
    (fun n => by simpa only [hv] using hdecay n)
  refine ⟨(-I) • R+I • (e-k),?_,?_⟩
  · intro n
    simp only [add_val,smul_val,sub_val,hR,hv,hu]
    ring_nf
    simp only [I_sq]
    ring
  · have h := norm_add_le ((-I) • R) (I • (e-k))
    simp only [norm_smul,norm_neg,norm_I,one_mul] at h
    have h' := (hRn.trans (mul_le_mul_of_nonneg_left hvn (by positivity)))
    linarith [norm_sub_le e k]

end NLS.WeightedCoeff
