import NLS.SequenceSpaces.SobolevDerivative
import NLS.SequenceSpaces.SobolevEmbedding

/-! # Weighted absolute summability from one additional Hilbert order -/
noncomputable section
namespace NLS.WeightedCoeff

/-- One extra weighted ℓ² derivative supplies weighted absolute summability
at any real order, including negative orders. -/
theorem memlp_sobolev_one_of_two_succ (s : ℝ) {a : ℤ → ℂ}
    (ha : Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*a n) 2) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*a n) 1 := by
  let b : WeightedCoeff (Weight.sobolev 1) 2 := ⟨fun n => (Weight.sobolev s n : ℂ)*a n,by
    change Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*((Weight.sobolev s n : ℂ)*a n)) 2
    convert ha using 1
    funext n
    rw [Weight.sobolev_add,Complex.ofReal_mul]
    ring⟩
  have h := lp.memℓp (sobolevToL1CLM 2 (by norm_num) b)
  convert h using 1
  funext n
  exact (sobolevToL1CLM_apply 2 (by norm_num) b n).symm

end NLS.WeightedCoeff
