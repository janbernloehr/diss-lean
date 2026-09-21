import NLS.ZakharovShabat.DeletedProductCriticalValues
import NLS.ZakharovShabat.CriticalMidpointOffset
import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.ExponentEmbedding

/-!
# The coefficient in the critical midpoint equation

The coefficient is twice the remaining-product value plus the midpoint
offset times its derivative. Its deviation from two has locally uniformly
bounded lp tail coefficients. This does not yet assert uniformly small
tails or a locally uniform nonvanishing threshold.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coefficient multiplying the critical-to-midpoint offset. -/
def canonicalCriticalOffsetCoefficient (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) : ℂ :=
  2*canonicalDeletedPeriodicProduct hp hp1 φ heven n (canonicalCriticalPoints hp hp1 φ heven n)+
    canonicalCriticalMidpointOffset hp hp1 φ heven n*canonicalDeletedCriticalDerivative hp hp1 φ heven n

/-- The coefficient error splits into the remaining-product value error and a bounded offset multiplier. -/
theorem canonicalCriticalOffsetCoefficient_sub_two (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) :
    canonicalCriticalOffsetCoefficient hp hp1 φ heven n-2 =
      2*canonicalDeletedCriticalValueError hp hp1 φ heven n+
        canonicalCriticalMidpointOffset hp hp1 φ heven n*canonicalDeletedCriticalDerivative hp hp1 φ heven n := by
  rw [canonicalCriticalOffsetCoefficient,canonicalDeletedCriticalValueError]
  ring

/-- The named coefficient gives exactly the squared-gap critical offset identity. -/
theorem canonicalCriticalOffsetCoefficient_identity (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) :
    canonicalCriticalOffsetCoefficient hp hp1 φ heven n*canonicalCriticalMidpointOffset hp hp1 φ heven n =
      (canonicalPeriodicGap hp hp1 φ heven n)^2*(canonicalDeletedCriticalDerivative hp hp1 φ heven n/4) := by
  simpa only [canonicalCriticalOffsetCoefficient,canonicalCriticalMidpointOffset_apply,canonicalDeletedCriticalDerivative]
    using canonicalCriticalPoints_midpoint_offset_identity hp hp1 φ heven n

/-- The coefficient minus two has bounded lp representatives on one common nearby tail. -/
theorem exists_uniform_criticalOffsetCoefficient_error (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0,
        ∃ a : Coeff p, ‖a‖ ≤ K ∧ ∀ n : ℤ, N < n.natAbs →
          a n = canonicalCriticalOffsetCoefficient hp hp1 ψ heven n-2 := by
  obtain ⟨N,hN,Uv,hov,hcv,hφv,h0v,S,hS,hvalues⟩ := exists_uniform_deletedProduct_critical_coefficients hp hp1 φ
  obtain ⟨Ud,hod,hcd,hφd,h0d,R,hR,hoffset⟩ := exists_uniform_canonicalCriticalMidpointOffset_bound hp hp1 φ
  refine ⟨N,hN,Uv ∩ Ud,hov.inter hod,hcv.inter hcd,⟨hφv,hφd⟩,⟨h0v,h0d⟩,
    2*S+R*S,by positivity,fun ψ hψ heven => ?_⟩
  obtain ⟨a,b,ha,hb,hab⟩ := hvalues ψ hψ.1 heven
  let d := canonicalCriticalMidpointOffset hp hp1 ψ heven
  let m : Coeff ⊤ := Coeff.exponentInclusion le_top d
  have hm : ‖m‖ ≤ R := (Coeff.norm_exponentInclusion_le le_top d).trans (hoffset ψ hψ.2 heven)
  refine ⟨(2 : ℂ) • a+Coeff.multiplier m b,?_,?_⟩
  · apply (norm_add_le _ _).trans
    rw [norm_smul,Complex.norm_ofNat]
    exact add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
      ((Coeff.norm_multiplier_le m b).trans (mul_le_mul hm hb (norm_nonneg b) hR))
  · intro n hn
    rw [canonicalCriticalOffsetCoefficient_sub_two]
    simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      Coeff.multiplier_apply,m,Coeff.exponentInclusion_apply,d,(hab n hn).1,(hab n hn).2]

/-- At a fixed potential the actual coefficient error belongs to lp over all signed indices. -/
theorem memℓp_canonicalCriticalOffsetCoefficient_sub_two (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) :
    Memℓp (fun n => canonicalCriticalOffsetCoefficient hp hp1 φ heven n-2) p := by
  obtain ⟨N,_,_,_,_,hφ,_,_,_,h⟩ := exists_uniform_criticalOffsetCoefficient_error hp hp1 φ
  obtain ⟨a,_,ha⟩ := h φ hφ heven
  apply NLS.memℓp_of_eq_outside_finset (lp.memℓp a) (Finset.Icc (-(N : ℤ)) N)
  intro n hn
  exact (ha n (by simp only [Finset.mem_Icc] at hn; omega)).symm

end NLS.ZakharovShabat
