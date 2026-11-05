import NLS.MKdV.MiuraNativeHamiltonianGlobalActionFactor
import NLS.MKdV.MiuraL2MassGeometry
import NLS.MKdV.MiuraFiniteEncodedActionRealization
import NLS.SequenceSpaces.WeightedSingle

/-! # The L² mass normal form and global native normal forms at every order

The mass trace supplies K_1 without any rough-L² Cartesian inverse.
Together with the higher-order construction, every independent physical
K_m has a global holomorphic normal form in its exact native action norm.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraMassActionFactor (b : MiuraActionMeanTarget) : ℂ :=
  (1/2 : ℂ)*b.2^2+miuraL2ActionMomentFunctional b.1

theorem analyticAt_miuraMassActionFactor (b : MiuraActionMeanTarget) : AnalyticAt ℂ miuraMassActionFactor b :=
  (analyticAt_const.mul (analyticAt_snd.pow 2)).add
    (miuraL2ActionMomentFunctional.analyticAt _ |>.comp analyticAt_fst)

theorem miuraNormalizedNativeActionMeanMap_zero_L2 (a : MiuraRealSobolevSource 0) :
    miuraNormalizedNativeActionMeanMap 0 a.val =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 0 a) := by
  apply Prod.ext
  · apply Subtype.ext
    funext n
    change (miuraNativeActionMeanEquiv 0 (miuraNativeActionMeanMap 0 a.val)).1.val n =
      (miuraL2ActionSequence (miuraPhysicalSobolevL2SourceInclusion 0 a).val).val n
    rw [miuraNativeActionMeanEquiv_fst]
    simp only [miuraSpectralActionWeight,Nat.mul_zero,Nat.zero_add,Nat.cast_one]
    rw [mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero n)]
    exact miuraSobolevActionSequence_L2_coefficients 0 a n
  · rw [miuraNormalizedNativeActionMeanMap,miuraNativeActionMeanEquiv_mean]
    exact (miuraPhysicalSobolevL2SourceInclusion_apply 0 a 0).symm

theorem miuraMassActionFactor_native_recovery (a : MiuraRealSobolevSource 0) :
    miuraMassActionFactor (miuraNormalizedNativeActionMeanMap 0 a.val) = miuraSpectralHillHamiltonian 0 a.val := by
  rw [miuraNormalizedNativeActionMeanMap_zero_L2,miuraSpectralHillHamiltonian_eq_native,
    nativeMiuraHillHamiltonian_zero_eq_L2Mass]
  exact (miuraL2Mass_eq_mean_sq_add_actionMoment (miuraPhysicalSobolevL2SourceInclusion 0 a).val
    (miuraPhysicalSobolevL2SourceInclusion 0 a).property).symm

/-- Global native holomorphic action normal forms for every independent
physical Hill Hamiltonian K_(s+1), including s=0 on the full real L² space. -/
theorem exists_global_native_miuraHamiltonian_action_factor_allOrders (s : ℕ) :
    ∃ V : Set (MiuraNativeActionMeanTarget s), ∃ F : MiuraNativeActionMeanTarget s → ℂ,
      IsOpen V ∧ (∀ a : MiuraRealSobolevSource s, miuraNativeActionMeanMap s a.val ∈ V) ∧
        AnalyticOnNhd ℂ F V ∧ ∀ a : MiuraRealSobolevSource s,
          F (miuraNativeActionMeanMap s a.val) = miuraSpectralHillHamiltonian s a.val := by
  by_cases hs : 1 ≤ s
  · exact exists_global_native_miuraHamiltonian_action_factor s hs
  · have he : s = 0 := by omega
    subst s
    refine ⟨univ,fun b => miuraMassActionFactor (miuraNativeActionMeanEquiv 0 b),isOpen_univ,
      fun _ => mem_univ _,?_,miuraMassActionFactor_native_recovery⟩
    intro b _
    exact (analyticAt_miuraMassActionFactor _).comp ((miuraNativeActionMeanEquiv 0).analyticAt b)

theorem miuraL2ActionMomentFunctional_single (n : ℤ) :
    miuraL2ActionMomentFunctional (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1) = 2*(Real.pi : ℂ)*n := by
  have he : miuraL2ActionMomentSequence (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1) =
      lp.single 1 n (2*(Real.pi : ℂ)*n) := by
    ext k
    rw [miuraL2ActionMomentSequence_apply,WeightedCoeff.single_val]
    by_cases hk : k = n <;> simp [lp.single_apply,hk]
  change (∑' k : ℤ, miuraL2ActionMomentSequence (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1) k) = _
  rw [he]
  simp only [lp.single_apply,tsum_pi_single]

/-- The physical K_1 action frequency is exactly 2πn, everywhere in
the full complex mass action domain, including collapsed selected actions. -/
theorem fderiv_miuraMassActionFactor_single (b : MiuraActionMeanTarget) (n : ℤ) :
    fderiv ℂ miuraMassActionFactor b (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1,0) =
      2*(Real.pi : ℂ)*n := by
  let L := ContinuousLinearMap.snd ℂ (WeightedCoeff (Weight.sobolev 1) 1) ℂ
  let M := miuraL2ActionMomentFunctional.comp (ContinuousLinearMap.fst ℂ (WeightedCoeff (Weight.sobolev 1) 1) ℂ)
  have hd := (((L.hasFDerivAt (x := b)).mul (L.hasFDerivAt (x := b))).const_mul (1/2 : ℂ)).add (M.hasFDerivAt (x := b))
  have he : (fun y : MiuraActionMeanTarget => (1/2 : ℂ)*(L y*L y)+M y) = miuraMassActionFactor := by
    funext y
    change (1/2 : ℂ)*(y.2*y.2)+miuraL2ActionMomentFunctional y.1 =
      (1/2 : ℂ)*y.2^2+miuraL2ActionMomentFunctional y.1
    rw [pow_two]
  change HasFDerivAt (𝕜 := ℂ) (fun y : MiuraActionMeanTarget => (1/2 : ℂ)*(L y*L y)+M y) _ b at hd
  rw [he] at hd
  rw [hd.fderiv]
  change (1/2 : ℂ)*(b.2*0+b.2*0)+miuraL2ActionMomentFunctional
    (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1) = _
  rw [mul_zero,add_zero,mul_zero,zero_add,miuraL2ActionMomentFunctional_single]

end NLS.MKdV
