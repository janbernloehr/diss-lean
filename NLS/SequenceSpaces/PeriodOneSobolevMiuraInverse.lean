import NLS.SequenceSpaces.PeriodOneMiuraSobolevJacobian
import NLS.ComplexAnalysis.AnalyticInverseBetweenSpaces

/-! # Actual analytic Miura inverse germs in native Sobolev spaces

The bounded native Jacobian equivalence gives actual open inverse charts.
Both the rough and stronger maps have the same exact coefficient formulas;
these identities allow the inverse germs to be matched to a fixed rough branch.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS
open NLS.ComplexAnalysis

/-- The literal native H^(t-1) inclusion into H-minus-one. -/
def periodOneSobolevImageInclusion (t : ℝ) (ht : 0≤t) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] PeriodOneHminusOne :=
  WeightedCoeff.sobolevInclusion (by linarith : -1≤t-1)

@[simp] theorem periodOneSobolevImageInclusion_apply (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) (n : ℤ) :
    (periodOneSobolevImageInclusion t ht q).val n=q.val n :=
  WeightedCoeff.sobolevInclusion_apply _ _ _

/-- The stronger analytic map is EXACTLY the actual rough map under the
original coefficient inclusions. -/
theorem periodOneSobolevShiftedMiura_inclusion (m : ℕ) (t : ℝ) (ht : 0≤t)
    (a : WeightedCoeff (Weight.sobolev t) 2) :
    periodOneSobolevImageInclusion t ht (periodOneSobolevShiftedMiura m t ht a)=
      periodOneShiftedMiura m (WeightedCoeff.sobolevToL2 ht a) := by
  apply Subtype.ext
  funext n
  simp only [periodOneSobolevImageInclusion_apply,periodOneSobolevShiftedMiura_apply,
    periodOneShiftedMiura_apply,WeightedCoeff.sobolevToL2_apply]

/-- The ACTUAL weak Miura derivative, with its exact factor two. -/
theorem hasFDerivAt_periodOneShiftedMiura (m : ℕ) (u : Coeff 2) :
    HasFDerivAt (periodOneShiftedMiura m) (periodOneMiuraJacobian m u) u := by
  have hp := periodOneMiuraProduct.hasFDerivAt_of_bilinear (hasFDerivAt_id u) (hasFDerivAt_id u)
  have hD : periodOneMiuraProduct.precompR _ u (ContinuousLinearMap.id ℂ _)+
      periodOneMiuraProduct.precompL _ (ContinuousLinearMap.id ℂ _) u=
      (2 : ℂ) • periodOneMiuraProduct u := by
    ext v
    change periodOneMiuraProduct u v+periodOneMiuraProduct v u=(2 : ℂ) • periodOneMiuraProduct u v
    rw [periodOneMiuraProduct_comm v u]
    module
  rw [show id u=u from rfl,hD] at hp
  exact (periodOneMassOperator m).hasFDerivAt.add hp

/-- The actual native Sobolev Jacobian equivalence gives a two-sided
analytic inverse on open native source and target neighborhoods. -/
theorem exists_periodOneSobolevMiura_inverse_at
    (m : ℕ) (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2)
    (hb : Function.Bijective (periodOneMiuraJacobian m (WeightedCoeff.sobolevToL2 ht a))) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev t) 2),
      ∃ W : Set (WeightedCoeff (Weight.sobolev (t-1)) 2),
      IsOpen V ∧ IsOpen W ∧ a∈V ∧ periodOneSobolevShiftedMiura m t ht a∈W ∧
      ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
        AnalyticOnNhd ℂ g W ∧
        (∀ v∈V, g (periodOneSobolevShiftedMiura m t ht v)=v) ∧
        (∀ q∈W, g q∈V ∧ periodOneSobolevShiftedMiura m t ht (g q)=q) := by
  let J := periodOneSobolevMiuraJacobianEquiv m t ht a hb
  have hd : HasStrictFDerivAt (periodOneSobolevShiftedMiura m t ht) J.toContinuousLinearMap a := by
    have H := (analyticAt_periodOneSobolevShiftedMiura m t ht a).hasStrictFDerivAt
    rw [(hasFDerivAt_periodOneSobolevShiftedMiura m t ht a).fderiv] at H
    exact H
  obtain ⟨V,W,hV,hW,ha,hq,_hsub,_him,_hbij,g,_hfa,hga,hl,hr⟩ :=
    exists_analytic_inverse_between_open_sets isOpen_univ
      (fun v _ => analyticAt_periodOneSobolevShiftedMiura m t ht v) (mem_univ a) J hd
  exact ⟨V,W,hV,hW,ha,hq,g,hga,hl,hr⟩

/-- An actual weak inverse germ, used for local uniqueness when identifying
a given rough analytic branch with a stronger Sobolev inverse. -/
theorem exists_periodOneMiura_inverse_at_of_bijectiveJacobian
    (m : ℕ) (u : Coeff 2) (hb : Function.Bijective (periodOneMiuraJacobian m u)) :
    ∃ V : Set (Coeff 2), ∃ W : Set PeriodOneHminusOne,
      IsOpen V ∧ IsOpen W ∧ u∈V ∧ periodOneShiftedMiura m u∈W ∧
      ∃ g : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ g W ∧
        (∀ v∈V, g (periodOneShiftedMiura m v)=v) ∧
        (∀ q∈W, g q∈V ∧ periodOneShiftedMiura m (g q)=q) := by
  let J := ContinuousLinearEquiv.ofBijective (periodOneMiuraJacobian m u)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hd : HasStrictFDerivAt (periodOneShiftedMiura m) J.toContinuousLinearMap u := by
    have H := (analyticAt_periodOneShiftedMiura m u).hasStrictFDerivAt
    rw [(hasFDerivAt_periodOneShiftedMiura m u).fderiv] at H
    exact H
  obtain ⟨V,W,hV,hW,hu,hq,_hsub,_him,_hbij,g,_hfa,hga,hl,hr⟩ :=
    exists_analytic_inverse_between_open_sets isOpen_univ
      (fun v _ => analyticAt_periodOneShiftedMiura m v) (mem_univ u) J hd
  exact ⟨V,W,hV,hW,hu,hq,g,hga,hl,hr⟩

end NLS
