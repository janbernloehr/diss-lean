import NLS.Articles.KdVPseudomeasures.OriginalHillL2NativeAnalytic
import NLS.Articles.KdVPseudomeasures.OriginalHillActionRotation
import NLS.KdV.HillNativeRealCoordinateDerivative
import NLS.KdV.HillNativeFiniteGap

/-! At an ACTUAL finite-gap source, its original spatial generator is an
EXACT FINITE weighted sum of the ACTUAL canonical-action Hamiltonian
fields. The original2*pi*n weights follow from actual spatial covariance
and the verified signed Gardner matrix, using the actual native Jacobian
injectivity. No momentum trace is assumed. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem fderiv_hillRealSignedMap_action_field (n : ℕ+) (q : HillRealMeanZeroSource) (k : ℤ) :
    ((fderiv ℝ hillRealSignedMap q) (hillRealActionHamiltonianVector n q)).val.val.val k=
      hillActionRotationRate n k*(hillRealSignedMap q).val.val.val k := by
  rw [fderiv_hillRealSignedMap_coordinate,hillRealActionHamiltonianVector_inclusion,
    hillRealNativeCoordinate_action_velocity,hillRealSignedMap_coordinate]

private theorem rate_pos (n m : ℕ+) :
    hillActionRotationRate n (m:ℤ)=if n=m then I else 0 := by
  have hp : (0:ℤ)<n := by exact_mod_cast n.pos
  have hq : (0:ℤ)<m := by exact_mod_cast m.pos
  have hneg : (m:ℤ) ≠ -(n:ℤ) := by omega
  by_cases he : n=m
  · subst m
    simp only [hillActionRotationRate,ite_true]
  · have hc : (m:ℤ) ≠ (n:ℤ) := by
      intro h
      exact he (PNat.coe_injective (Int.ofNat_inj.mp h)).symm
    simp only [hillActionRotationRate,if_neg hc,if_neg hneg,if_neg he]

private theorem rate_neg (n m : ℕ+) :
    hillActionRotationRate n (-(m:ℤ))=if n=m then -I else 0 := by
  have hp : (0:ℤ)<n := by exact_mod_cast n.pos
  have hq : (0:ℤ)<m := by exact_mod_cast m.pos
  have hpos : -(m:ℤ) ≠ (n:ℤ) := by omega
  by_cases he : n=m
  · subst m
    simp only [hillActionRotationRate,if_neg hpos,ite_true]
  · have hc : -(m:ℤ) ≠ -(n:ℤ) := by
      intro h
      exact he (PNat.coe_injective (Int.ofNat_inj.mp (neg_inj.mp h))).symm
    simp only [hillActionRotationRate,if_neg hpos,if_neg hc,if_neg he]

private theorem finite_rotation_sum_eq_spatial (s : Finset ℕ+) (a : HillRealSignedTarget)
    (ha : ∀ n : ℕ+, n ∉ s → a.val.val.val (n:ℤ)=0) (k : ℤ) :
    (∑ n ∈ s, ((2*Real.pi*(n:ℕ):ℝ):ℂ)*(hillActionRotationRate n k*a.val.val.val k))=
      I*((2*Real.pi*k:ℝ):ℂ)*a.val.val.val k := by
  by_cases hk : k=0
  · subst k
    rw [show a.val.val.val 0=0 from a.val.property]
    simp
  · by_cases hp : 0<k
    · let m : ℕ+ := ⟨k.toNat,by omega⟩
      have hm : (m:ℤ)=k := Int.toNat_of_nonneg hp.le
      rw [← hm]
      simp only [rate_pos,ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_eq']
      by_cases hs : m ∈ s
      · rw [if_pos hs]
        push_cast
        ring
      · rw [if_neg hs,ha m hs,mul_zero]
    · let m : ℕ+ := ⟨(-k).toNat,by omega⟩
      have hm : -(m:ℤ)=k := by
        have he : (m:ℤ)= -k := Int.toNat_of_nonneg (by omega)
        omega
      rw [← hm]
      simp only [rate_neg,ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_eq']
      by_cases hs : m ∈ s
      · rw [if_pos hs]
        push_cast
        ring
      · rw [if_neg hs,a.property,ha m hs,map_zero,mul_zero]

/-- Exact finite action-field decomposition of ANY existing source spatial
generator when the SAME actual native output has finite positive support. -/
theorem hillReal_spatialGenerator_eq_finite_action_fields
    (q v : HillRealMeanZeroSource)
    (hv : ∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k)
    (s : Finset ℕ+) (hs : ∀ n : ℕ+, n ∉ s → (hillRealSignedMap q).val.val.val (n:ℤ)=0) :
    v=∑ n ∈ s, (2*Real.pi*(n:ℕ)) • hillRealActionHamiltonianVector n q := by
  apply (hillPhysicalNativeJacobian_bijective q).1
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  let L : HillRealMeanZeroSource →L[ℝ] ℂ :=
    (WeightedCoeff.fourierRealZeroEvalCLM (Weight.signedSobolev (-1/2)) 2 k).comp (fderiv ℝ hillRealSignedMap q)
  have hsum : ((fderiv ℝ hillRealSignedMap q)
      (∑ n ∈ s, (2*Real.pi*(n:ℕ)) • hillRealActionHamiltonianVector n q)).val.val.val k=
      ∑ n ∈ s, ((2*Real.pi*(n:ℕ):ℝ):ℂ)*(hillActionRotationRate n k*(hillRealSignedMap q).val.val.val k) := by
    change L (∑ n ∈ s, (2*Real.pi*(n:ℕ)) • hillRealActionHamiltonianVector n q)= _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_smul]
    change ((2*Real.pi*(n:ℕ):ℝ):ℂ)*
      (((fderiv ℝ hillRealSignedMap q) (hillRealActionHamiltonianVector n q)).val.val.val k)= _
    rw [fderiv_hillRealSignedMap_action_field]
  rw [fderiv_hillRealSignedMap_spatialGenerator q v hv k,hsum]
  exact (finite_rotation_sum_eq_spatial s (hillRealSignedMap q) hs k).symm

/-- EVERY actual finite-gap L2 source has the original spatial generator
as a FINITE sum with EXACT original2*pi*n action weights. -/
theorem exists_hillL2_finite_action_spatialGenerator (u : HillRealL2BanachSource)
    (hf : hillL2SourceInclusion u ∈ hillRealFiniteGapLocus) :
    ∃ s : Finset ℕ+,
      (∀ n : ℕ+, n ∉ s → (hillRealSignedMap (hillL2SourceInclusion u)).val.val.val (n:ℤ)=0) ∧
      hillL2SourceSpatialGenerator u=
        ∑ n ∈ s, (2*Real.pi*(n:ℕ)) • hillRealActionHamiltonianVector n (hillL2SourceInclusion u) := by
  obtain ⟨N,hN⟩ := hf
  let s : Finset ℕ+ := (Finset.range N).subtype (fun n : ℕ => 0<n)
  have hs (n : ℕ+) (hn : n ∉ s) : (hillRealSignedMap (hillL2SourceInclusion u)).val.val.val (n:ℤ)=0 := by
    apply (hillRealSignedMap_positive_eq_zero_iff_gapSquare _ n).mpr
    apply hN n
    have hnot : ¬(n:ℕ)<N := by
      intro hlt
      apply hn
      exact Finset.mem_subtype.mpr (Finset.mem_range.mpr hlt)
    omega
  exact ⟨s,hs,hillReal_spatialGenerator_eq_finite_action_fields (hillL2SourceInclusion u)
    (hillL2SourceSpatialGenerator u) (fun k => by rw [hillL2SourceSpatialGenerator_apply,hillL2SourceInclusion_apply]) s hs⟩

end NLS.Articles.KdVPseudomeasures
