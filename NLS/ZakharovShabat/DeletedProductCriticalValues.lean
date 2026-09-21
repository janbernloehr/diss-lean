import NLS.ZakharovShabat.CanonicalDeletedProductLp
import NLS.ZakharovShabat.FreeSquaredSineBounds
import NLS.ZakharovShabat.UniformCanonicalCriticalPoints
import NLS.SequenceSpaces.FiniteModification

/-!
# Remaining-product values at canonical critical points

For all sufficiently distant indices, one common potential neighborhood
supplies bounded lp coefficients for `Gₙ(cₙ)-1` and `Gₙ′(cₙ)`. The finite
central indices are handled separately when asserting full lp membership.
No nonvanishing coefficient or inversion is asserted in this module.
-/

noncomputable section
open Set Complex Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The remaining product's deviation from one at its canonical critical point. -/
def canonicalDeletedCriticalValueError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) : ℂ :=
  canonicalDeletedPeriodicProduct hp hp1 φ heven n (canonicalCriticalPoints hp hp1 φ heven n)-1

/-- The remaining product's spectral derivative at its canonical critical point. -/
def canonicalDeletedCriticalDerivative (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) : ℂ :=
  deriv (canonicalDeletedPeriodicProduct hp hp1 φ heven n) (canonicalCriticalPoints hp hp1 φ heven n)

/-- The two remaining-product critical-value tails have locally uniform lp coefficient bounds. -/
theorem exists_uniform_deletedProduct_critical_coefficients (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0,
        ∃ a b : Coeff p, ‖a‖ ≤ K ∧ ‖b‖ ≤ K ∧ ∀ n : ℤ, N < n.natAbs →
          a n = canonicalDeletedCriticalValueError hp hp1 ψ heven n ∧
          b n = canonicalDeletedCriticalDerivative hp hp1 ψ heven n := by
  obtain ⟨N,hN,Uc,hoc,hcc,hφc,h0c,R,hR,hcrit⟩ := exists_uniform_canonicalCriticalPoints hp hp1 φ
  obtain ⟨Ue,hoe,hce,hφe,h0e,S,hS,herror⟩ := exists_uniform_canonicalDeletedPairError_majorants hp hp1 φ
  obtain ⟨C,hC,hfree⟩ := exists_freeSquaredSine_displacement_bounds (Real.pi/4)
  let T := 1+4/Real.pi
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have h1T : 1 ≤ T := le_add_of_nonneg_right (by positivity)
  have h4T : 4/Real.pi ≤ T := by dsimp [T]; linarith
  refine ⟨N,hN,Uc ∩ Ue,hoc.inter hoe,hcc.inter hce,⟨hφc,hφe⟩,⟨h0c,h0e⟩,
    T*S+C*R,by positivity,fun ψ hψ heven => ?_⟩
  obtain ⟨hl,hdnorm⟩ := hcrit ψ hψ.1 heven
  obtain ⟨A,hAnorm,hvalue,hderiv⟩ := herror ψ hψ.2 heven
  let d := canonicalCriticalDisplacement hp hp1 ψ heven
  let z : ℤ → ℂ := fun n => if N < n.natAbs then canonicalCriticalPoints hp hp1 ψ heven n else (Real.pi : ℂ)*n
  have hz (n : ℤ) : ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 := by
    by_cases hn : N < n.natAbs
    · have h := (hl.distant n hn).1
      exact (show ‖z n-(Real.pi : ℂ)*n‖ < Real.pi/4 by simpa only [z,if_pos hn,mem_ball,dist_eq_norm] using h).le
    · simp only [z,if_neg hn,sub_self,norm_zero]
      positivity
  have hdisp (n : ℤ) : ‖z n-(Real.pi : ℂ)*n‖ ≤ ‖d n‖ := by
    by_cases hn : N < n.natAbs
    · simp only [z,if_pos hn,d,canonicalCriticalDisplacement_apply,le_refl]
    · simp only [z,if_neg hn,sub_self,norm_zero]
      exact norm_nonneg _
  have hf (n : ℤ) : ‖(freeSineQuotient n (z n))^2-1‖ ≤ C*‖d n‖ ∧
      ‖deriv (fun w => (freeSineQuotient n w)^2) (z n)‖ ≤ C*‖d n‖ :=
    ⟨((hfree n (z n) (hz n)).1).trans (mul_le_mul_of_nonneg_left (hdisp n) hC),
      ((hfree n (z n) (hz n)).2).trans (mul_le_mul_of_nonneg_left (hdisp n) hC)⟩
  let B : Coeff p := (T : ℂ) • Coeff.magnitude A+(C : ℂ) • Coeff.magnitude d
  have hB (n : ℤ) : ‖B n‖ = T*‖A n‖+C*‖d n‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.magnitude_apply,
      ← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real]
    rw [Real.norm_of_nonneg (by positivity)]
  have hBnorm : ‖B‖ ≤ T*S+C*R := by
    apply (norm_add_le _ _).trans
    simp only [norm_smul,Coeff.norm_magnitude,Complex.norm_real,Real.norm_of_nonneg hT,Real.norm_of_nonneg hC]
    exact add_le_add (mul_le_mul_of_nonneg_left hAnorm hT) (mul_le_mul_of_nonneg_left hdnorm hC)
  have hv (n : ℤ) : ‖canonicalDeletedPeriodicProduct hp hp1 ψ heven n (z n)-1‖ ≤ ‖B n‖ := by
    have he : canonicalDeletedPeriodicProduct hp hp1 ψ heven n (z n)-1 =
        canonicalDeletedPairError hp hp1 ψ heven n (z n)+((freeSineQuotient n (z n))^2-1) := by
      rw [canonicalDeletedPairError]; ring
    rw [he,hB]
    apply (norm_add_le _ _).trans
    apply (add_le_add (hvalue n (z n) (by linarith [hz n,Real.pi_pos])) (hf n).1).trans
    exact add_le_add (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right h1T (norm_nonneg (A n)))) le_rfl
  have hd (n : ℤ) : ‖deriv (canonicalDeletedPeriodicProduct hp hp1 ψ heven n) (z n)‖ ≤ ‖B n‖ := by
    have he : deriv (canonicalDeletedPeriodicProduct hp hp1 ψ heven n) (z n) =
        deriv (canonicalDeletedPairError hp hp1 ψ heven n) (z n)+
          deriv (fun w => (freeSineQuotient n w)^2) (z n) := by
      rw [deriv_canonicalDeletedPairError]; ring
    rw [he,hB]
    apply (norm_add_le _ _).trans
    apply (add_le_add (hderiv n (z n) (hz n)) (hf n).2).trans
    exact add_le_add (mul_le_mul_of_nonneg_right h4T (norm_nonneg (A n))) le_rfl
  let a : Coeff p := ⟨_,(lp.memℓp B).mono' hv⟩
  let b : Coeff p := ⟨_,(lp.memℓp B).mono' hd⟩
  refine ⟨a,b,(lp.norm_mono (zero_lt_one.trans hp1).ne' hv).trans hBnorm,
    (lp.norm_mono (zero_lt_one.trans hp1).ne' hd).trans hBnorm,?_⟩
  intro n hn
  constructor
  · change canonicalDeletedPeriodicProduct hp hp1 ψ heven n (z n)-1 = _
    simp only [z,if_pos hn,canonicalDeletedCriticalValueError]
  · change deriv (canonicalDeletedPeriodicProduct hp hp1 ψ heven n) (z n) = _
    simp only [z,if_pos hn,canonicalDeletedCriticalDerivative]

/-- At each potential the actual remaining-product critical-value errors form a full lp sequence. -/
theorem memℓp_canonicalDeletedCriticalValueError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) : Memℓp (canonicalDeletedCriticalValueError hp hp1 φ heven) p := by
  obtain ⟨N,_,_,_,_,hφ,_,_,_,h⟩ := exists_uniform_deletedProduct_critical_coefficients hp hp1 φ
  obtain ⟨a,_,_,_,ha⟩ := h φ hφ heven
  apply NLS.memℓp_of_eq_outside_finset (lp.memℓp a) (Finset.Icc (-(N : ℤ)) N)
  intro n hn
  exact ((ha n (by simp only [Finset.mem_Icc] at hn; omega)).1).symm

/-- At each potential the actual remaining-product critical derivatives form a full lp sequence. -/
theorem memℓp_canonicalDeletedCriticalDerivative (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) : Memℓp (canonicalDeletedCriticalDerivative hp hp1 φ heven) p := by
  obtain ⟨N,_,_,_,_,hφ,_,_,_,h⟩ := exists_uniform_deletedProduct_critical_coefficients hp hp1 φ
  obtain ⟨_,b,_,_,hb⟩ := h φ hφ heven
  apply NLS.memℓp_of_eq_outside_finset (lp.memℓp b) (Finset.Icc (-(N : ℤ)) N)
  intro n hn
  exact ((hb n (by simp only [Finset.mem_Icc] at hn; omega)).2).symm

end NLS.ZakharovShabat
