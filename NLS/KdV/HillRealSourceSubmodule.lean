import NLS.KdV.HillRealSourceCompleteness
import NLS.SequenceSpaces.ConjugateReflection
import NLS.SequenceSpaces.Parity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual real period-one rough Hill sources, as a real Banach subspace. -/
def hillRealSourceSubmodule : Submodule ℝ (WeightedCoeff SpectralWeight.one.toWeight 2) where
  carrier := {q | SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0 ∧
    IsRealHillPotential (SpectralWeight.one.toCoeff q)}
  zero_mem' := by
    constructor
    · simp only [map_zero]; exact Submodule.zero_mem _
    · rw [map_zero]
      intro k
      change (0 : ℂ)=conj 0
      exact (map_zero _).symm
  add_mem' := by
    rintro a b ⟨ha,har⟩ ⟨hb,hbr⟩
    constructor
    · simpa only [map_add] using (Coeff.paritySubspace (p := 2) 0).add_mem ha hb
    · intro k
      simp only [SpectralWeight.toCoeff_apply,WeightedCoeff.add_val]
      simpa only [SpectralWeight.toCoeff_apply,map_add] using congrArg₂ (fun x y : ℂ => x+y) (har k) (hbr k)
  smul_mem' := by
    rintro c a ⟨ha,har⟩
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    constructor
    · rw [Coeff.mem_paritySubspace]
      intro k hk
      simp only [SpectralWeight.toCoeff_apply,WeightedCoeff.smul_val]
      rw [← SpectralWeight.toCoeff_apply SpectralWeight.one a k,(Coeff.mem_paritySubspace 0 _).mp ha k hk,mul_zero]
    · intro k
      simp only [SpectralWeight.toCoeff_apply,WeightedCoeff.smul_val]
      change (c : ℂ)*a.val (-k)=conj ((c : ℂ)*a.val k)
      rw [map_mul,Complex.conj_ofReal]
      exact congrArg (fun z : ℂ => (c : ℂ)*z) (by simpa only [SpectralWeight.toCoeff_apply] using har k)

instance : CompleteSpace hillRealSourceSubmodule := completeSpace_realPeriodOneHillPotential

private def realSourceReflectionCLM :
    WeightedCoeff SpectralWeight.one.toWeight 2 →L[ℝ] WeightedCoeff SpectralWeight.one.toWeight 2 :=
  ((WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (((starL' ℝ : Coeff 2 ≃L[ℝ] Coeff 2).toContinuousLinearMap).comp
      ((Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
        ((WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)))

private theorem realSourceReflectionCLM_apply (q : WeightedCoeff SpectralWeight.one.toWeight 2) (k : ℤ) :
    (realSourceReflectionCLM q).val k=conj (q.val (-k)) :=
  WeightedCoeff.conjugateReflection_apply _ (by intro j;rfl) q k

private def realEvenSourceProjection :
    WeightedCoeff SpectralWeight.one.toWeight 2 →L[ℝ] WeightedCoeff SpectralWeight.one.toWeight 2 :=
  (1/2 : ℝ) • ((ContinuousLinearMap.id ℝ _+realSourceReflectionCLM).comp
    ((WeightedCoeff.parityProjection SpectralWeight.one.toWeight 0).restrictScalars ℝ))

private theorem realEvenSourceProjection_apply (q : WeightedCoeff SpectralWeight.one.toWeight 2) (k : ℤ) :
    (realEvenSourceProjection q).val k=
      (1/2 : ℂ)*((WeightedCoeff.parityProjection SpectralWeight.one.toWeight 0 q).val k+
        conj ((WeightedCoeff.parityProjection SpectralWeight.one.toWeight 0 q).val (-k))) := by
  change ((1/2 : ℝ) : ℂ)*((WeightedCoeff.parityProjection SpectralWeight.one.toWeight 0 q).val k+
    (realSourceReflectionCLM (WeightedCoeff.parityProjection SpectralWeight.one.toWeight 0 q)).val k)=_
  rw [realSourceReflectionCLM_apply]
  norm_num

private theorem realEvenSourceProjection_mem (q : WeightedCoeff SpectralWeight.one.toWeight 2) :
    realEvenSourceProjection q∈hillRealSourceSubmodule := by
  constructor
  · rw [Coeff.mem_paritySubspace]
    intro k hk
    have hk' : (-k)%2≠(0 : ℤ)%2 := by omega
    simp only [SpectralWeight.toCoeff_apply,realEvenSourceProjection_apply,
      WeightedCoeff.parityProjection_apply,if_neg hk,if_neg hk',map_zero,add_zero,mul_zero]
  · intro k
    simp only [SpectralWeight.toCoeff_apply,realEvenSourceProjection_apply,neg_neg,map_mul,map_add,
      Complex.conj_conj]
    norm_num [show conj (2 : ℂ)=(2 : ℂ) from Complex.conj_ofReal (2 : ℝ)]
    ring

/-- A bounded real projection onto the actual physical source space. -/
def hillRealSourceProjectionCLM :
    WeightedCoeff SpectralWeight.one.toWeight 2 →L[ℝ] hillRealSourceSubmodule :=
  realEvenSourceProjection.codRestrict hillRealSourceSubmodule realEvenSourceProjection_mem

/-- The real projection fixes every genuine real period-one source. -/
theorem hillRealSourceProjectionCLM_fixed (q : hillRealSourceSubmodule) :
    hillRealSourceProjectionCLM q.val=q := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change (realEvenSourceProjection q.val).val k=q.val.val k
  rw [realEvenSourceProjection_apply]
  have hP (j : ℤ) : (WeightedCoeff.parityProjection SpectralWeight.one.toWeight 0 q.val).val j=q.val.val j := by
    rw [WeightedCoeff.parityProjection_apply]
    by_cases hj : j%2=(0 : ℤ)%2
    · rw [if_pos hj]
    · rw [if_neg hj]
      simpa only [SpectralWeight.toCoeff_apply] using ((Coeff.mem_paritySubspace 0 _).mp q.property.1 j hj).symm
  rw [hP,hP]
  have hreal := q.property.2 k
  simp only [SpectralWeight.toCoeff_apply] at hreal
  rw [hreal,Complex.conj_conj]
  ring

end NLS.KdV
