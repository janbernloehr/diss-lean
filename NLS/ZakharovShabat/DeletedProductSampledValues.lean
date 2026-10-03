import NLS.ZakharovShabat.CanonicalDeletedProductLp
import NLS.ZakharovShabat.FreeSquaredSineBounds
import NLS.SequenceSpaces.FiniteExponentTail
import NLS.SequenceSpaces.PowerDecaySummability

/-! # Deleted periodic products at displaced samples

An arbitrary ℓp displacement from the free lattice gives an ℓp error
from one for the deleted periodic product. The samples need only approach
the free discs on the tail; the finite central block is unrestricted.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Sampling the actual remaining product along any ℓp perturbation of the
free lattice gives its full ℓp deviation from one. -/
theorem memlp_sampled_canonicalDeletedPeriodicProduct_sub_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (z : ℤ → ℂ) (hz : Memℓp (fun n => z n-(Real.pi : ℂ)*n) p) :
    Memℓp (fun n => canonicalDeletedPeriodicProduct hp hp1 φ heven n (z n)-1) p := by
  have hpr : 0 < p.toReal := by
    have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
    linarith
  let d : Coeff p := ⟨_,hz⟩
  obtain ⟨N,hN⟩ := Coeff.exists_natAbs_norm_lt hpr d (by positivity : 0 < Real.pi/4)
  obtain ⟨U,_,_,hφ,_,K,_,hmajorant⟩ := exists_uniform_canonicalDeletedPairError_majorants hp hp1 φ
  obtain ⟨A,_,hA,_⟩ := hmajorant φ hφ heven
  obtain ⟨C,hC,hfree⟩ := exists_freeSquaredSine_displacement_bounds (Real.pi/4)
  have hbound : Memℓp (fun n => ‖A n‖+C*‖d n‖) p := (lp.memℓp A).norm.add ((lp.memℓp d).norm.const_mul C)
  have hm := memlp_of_natAbs_eventual_bound p.toReal hpr
    (fun n => canonicalDeletedPeriodicProduct hp hp1 φ heven n (z n)-1)
    (fun n => ‖A n‖+C*‖d n‖) (by simpa only [ENNReal.ofReal_toReal hp] using hbound) N (by
      intro n hn
      have hd : ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 := (hN n hn).le
      have he : canonicalDeletedPeriodicProduct hp hp1 φ heven n (z n)-1 =
          canonicalDeletedPairError hp hp1 φ heven n (z n)+((freeSineQuotient n (z n))^2-1) := by
        unfold canonicalDeletedPairError
        ring
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (hA n (z n) (by linarith [Real.pi_pos])) (hfree n (z n) hd).1))
  simpa only [ENNReal.ofReal_toReal hp] using hm

end NLS.ZakharovShabat
