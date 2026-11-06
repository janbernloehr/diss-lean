import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.KdV.HillUnitRealSourceCoordinates

/-! # Original mean-zero real L2 sources determine continuous rough functions

Symmetric finite raw truncations preserve the mean and physical reality.
Their ORIGINAL even-indexed physical representatives converge in H-minus-one;
no uniform physical L2 norm is required.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

theorem eq_on_real_meanZero_of_original_physical
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {U : Set PeriodOneHminusOne} (hU : IsOpen U)
    (f g : PeriodOneHminusOne → E) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : ∀ p : RealPeriodOneHillPotential, p.val.val 0=0 →
      hillOriginalHminusSource p.val∈U → f (hillOriginalHminusSource p.val)=g (hillOriginalHminusSource p.val))
    (q : PeriodOneHminusOne) (hq : q∈U) (hreal : IsRealPeriodOneHminusOne q) (hmean : q.val 0=0) :
    f q=g q := by
  let u (S : Finset ℤ) : Coeff 2 := periodOneFiniteL2Approx q (periodOneSymmetricSupport S)
  have hur (S : Finset ℤ) : periodOneL2Conjugation (u S)=u S :=
    (periodOneL2Conjugation_fixed_iff _).mpr (periodOneFiniteL2Approx_real ⟨q,hreal⟩ S)
  let p (S : Finset ℤ) := hillRealWeightedEmbedding SpectralWeight.one (hillUnitRealSourceLift (u S) (hur S))
  have hcoeff (S : Finset ℤ) : SpectralWeight.one.toCoeff (p S).val=Coeff.periodDouble (u S) := by
    rw [hillRealWeightedEmbedding_toCoeff,hillUnitRealSourceLift_toCoeff]
  have hpmean (S : Finset ℤ) : (p S).val.val 0=0 := by
    have hu0 : u S 0=0 := by simp only [u,periodOneFiniteL2Approx_apply,hmean,ite_self]
    have hh : SpectralWeight.one.toCoeff (p S).val 0=0 := by
      rw [hcoeff]
      change Coeff.periodDouble (u S) (2*0)=0
      rw [Coeff.periodDouble_even]
      exact hu0
    simpa only [SpectralWeight.toCoeff_apply] using hh
  have hsource (S : Finset ℤ) : hillOriginalHminusSource (p S).val=periodOneL2Inclusion (u S) := by
    apply Subtype.ext
    funext j
    rw [hillOriginalHminusSource_apply,periodOneL2Inclusion_apply]
    have hc := congrArg (fun a : Coeff 2 => a (2*j)) (hcoeff S)
    simpa only [SpectralWeight.toCoeff_apply,Coeff.periodDouble_even] using hc
  have ht : Tendsto (fun S => hillOriginalHminusSource (p S).val) atTop (𝓝 q) := by
    have hh := (WeightedCoeff.tendsto_truncate (Weight.sobolev (-1)) 2 (by simp) q).comp
      tendsto_periodOneSymmetricSupport
    simpa only [hsource,u,periodOneL2Inclusion_finiteApprox,Function.comp_def] using hh
  have hnear := ht.eventually (hU.mem_nhds hq)
  have hevent : (fun S => f (hillOriginalHminusSource (p S).val)) =ᶠ[atTop]
      (fun S => g (hillOriginalHminusSource (p S).val)) := by
    filter_upwards [hnear] with S hS
    exact he (p S) (hpmean S) hS
  have hfl := ((hf.continuousAt (hU.mem_nhds hq)).tendsto).comp ht
  have hgl := ((hg.continuousAt (hU.mem_nhds hq)).tendsto).comp ht
  exact tendsto_nhds_unique (hfl.congr' hevent) hgl

end NLS.KdV
