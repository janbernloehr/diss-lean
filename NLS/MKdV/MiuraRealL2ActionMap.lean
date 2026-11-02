import NLS.MKdV.MiuraL2MassGeometry
import NLS.SequenceSpaces.PhysicalRealUnweightedCoefficients

/-! # The actual action and mean map on the physical real L² space

The map is continuous in its full native weighted target norm. The mass
trace bounds source preimages of bounded target families and upgrades
coefficient convergence to strong L² convergence whenever the complete
action and mean data converge.
-/
noncomputable section
open Set Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraRealL2 := Coeff.physicalRealSubmodule 2

def miuraRealL2ActionMeanMap (a : MiuraRealL2) : WeightedCoeff (Weight.sobolev 1) 1 × ℂ :=
  miuraL2ActionMeanMap a.val

theorem continuous_miuraRealL2ActionMeanMap : Continuous miuraRealL2ActionMeanMap := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact (analyticAt_miuraL2ActionMeanMap a.val a.property).continuousAt.comp
    continuous_subtype_val.continuousAt

/-- Bounded original action and signed-mean data give bounded original scalar L² sources. -/
theorem miuraRealL2_bounded_of_actionMean_bounded {A : Type*} (a : A → MiuraRealL2)
    (hb : Bornology.IsBounded (range (fun k => miuraRealL2ActionMeanMap (a k)))) :
    Bornology.IsBounded (range a) := by
  obtain ⟨M,hM⟩ := hb.exists_norm_le
  let C := max M 0
  have hC : 0 ≤ C := le_max_right M 0
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C+‖miuraL2ActionMomentFunctional‖+1,?_⟩
  rintro _ ⟨k,rfl⟩
  have hk : ‖miuraL2ActionMeanMap (a k).val‖ ≤ C := (hM _ ⟨k,rfl⟩).trans (le_max_left M 0)
  have hsq := miuraL2_norm_sq_le_actionMeanMap (a k).val (a k).property
  have hksq := (sq_le_sq₀ (norm_nonneg _) hC).mpr hk
  have hkmul := mul_le_mul_of_nonneg_left hk (show 0 ≤ 2*‖miuraL2ActionMomentFunctional‖ by positivity)
  change ‖(a k).val‖ ≤ _
  nlinarith [norm_nonneg (a k).val,norm_nonneg miuraL2ActionMomentFunctional,
    sq_nonneg ‖miuraL2ActionMomentFunctional‖]

/-- The complete actual action and mean data prevent loss of L² norm at a coefficient limit. -/
theorem tendsto_miuraRealL2_of_coefficientwise_of_actionMean
    {A : Type*} {l : Filter A} (a : A → MiuraRealL2) (b : MiuraRealL2)
    (ht : ∀ n : ℤ, Tendsto (fun k => (a k).val n) l (𝓝 (b.val n)))
    (hJ : Tendsto (fun k => miuraRealL2ActionMeanMap (a k)) l (𝓝 (miuraRealL2ActionMeanMap b))) :
    Tendsto a l (𝓝 b) := by
  apply tendsto_subtype_rng.mpr
  apply Coeff.tendsto_of_coefficientwise_of_norm_sq (fun k => (a k).val) b.val ht
  let R : WeightedCoeff (Weight.sobolev 1) 1 × ℂ → ℝ :=
    fun z => z.2.re^2+2*(miuraL2ActionMomentFunctional z.1).re
  have hR : Continuous R := by fun_prop
  have hn := hR.continuousAt.tendsto.comp hJ
  have he (u : MiuraRealL2) : R (miuraRealL2ActionMeanMap u) = ‖u.val‖^2 :=
    (miuraL2_norm_sq_eq_action_mean u.val u.property).symm
  change Tendsto (fun k => R (miuraRealL2ActionMeanMap (a k))) l (𝓝 (R (miuraRealL2ActionMeanMap b))) at hn
  simpa only [he] using hn

end NLS.MKdV
