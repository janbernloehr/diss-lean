import NLS.MKdV.MiuraNativeHamiltonianMassActionFactor
import NLS.MKdV.MiuraH1ActionRaysInL2
import NLS.MKdV.MiuraGlobalNLSActionFactor
import NLS.ComplexAnalysis.AnalyticFactorDirectionUnique

/-! # Intrinsic physical mass frequencies on the entire original real L² domain

H¹ one-sided action rays fix the derivative of any global mass normal
form. Norm continuity and physical real H¹ density then give the same
derivative on all real L² profiles, including every collapsed action.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

structure MiuraL2MassActionData where
  domain : Set MiuraActionMeanTarget
  hamiltonian : MiuraActionMeanTarget → ℂ
  domain_open : IsOpen domain
  contains : ∀ a : MiuraRealL2, miuraRealL2ActionMeanMap a ∈ domain
  analytic : AnalyticOnNhd ℂ hamiltonian domain
  recovery : ∀ a : MiuraRealL2, hamiltonian (miuraRealL2ActionMeanMap a) = miuraL2Mass a.val

def miuraL2MassActionData : MiuraL2MassActionData where
  domain := univ
  hamiltonian := miuraMassActionFactor
  domain_open := isOpen_univ
  contains := fun _ => mem_univ _
  analytic := fun b _ => analyticAt_miuraMassActionFactor b
  recovery := fun a => (miuraL2Mass_eq_mean_sq_add_actionMoment a.val a.property).symm

namespace MiuraL2MassActionData

/-- Transport a mass normal form through a bounded linear map. Keeping
this construction abstract avoids expanding a concrete weight equivalence
inside the analytic composition proof. -/
def ofLinearPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : MiuraActionMeanTarget →L[ℂ] E) (V : Set E) (F : E → ℂ)
    (hV : IsOpen V) (hF : AnalyticOnNhd ℂ F V)
    (hc : ∀ a : MiuraRealL2, L (miuraRealL2ActionMeanMap a) ∈ V)
    (hr : ∀ a : MiuraRealL2, F (L (miuraRealL2ActionMeanMap a)) = miuraL2Mass a.val) :
    MiuraL2MassActionData where
  domain := L ⁻¹' V
  hamiltonian := fun b => F (L b)
  domain_open := hV.preimage L.continuous
  contains := hc
  analytic := fun b hb => (hF _ hb).comp (L.analyticAt b)
  recovery := hr

def frequency (D : MiuraL2MassActionData) (n : ℤ) (b : MiuraActionMeanTarget) : ℂ :=
  fderiv ℂ D.hamiltonian b (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1,0)

theorem frequency_analytic (D : MiuraL2MassActionData) (n : ℤ) :
    AnalyticOnNhd ℂ (D.frequency n) D.domain := by
  intro b hb
  exact ((ContinuousLinearMap.apply (E := MiuraActionMeanTarget) ℂ ℂ).analyticAt_bilinear _).comp₂
    analyticAt_const (D.analytic b hb).fderiv

theorem source_frequency_analyticAt (D : MiuraL2MassActionData) (n : ℤ) (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    AnalyticAt ℂ (fun b => D.frequency n (miuraL2ActionMeanMap b)) a :=
  (D.frequency_analytic n (miuraL2ActionMeanMap a) (D.contains ⟨a,ha⟩)).comp
    (f := miuraL2ActionMeanMap) (analyticAt_miuraL2ActionMeanMap a ha)

theorem frequency_H1 (D : MiuraL2MassActionData) (a : MiuraRealSobolevSource 1)
    (n : ℤ) (hn : 0 < n) :
    D.frequency n (miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a)) = 2*(Real.pi : ℂ)*n := by
  have h := NLS.ComplexAnalysis.fderiv_eq_of_nonnegative_ray_realization
    D.hamiltonian miuraMassActionFactor
    (fun b : MiuraRealSobolevSource 1 => miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b))
    (fun b : MiuraRealSobolevSource 1 => miuraL2Mass (miuraPhysicalSobolevL2SourceInclusion 1 b).val)
    (miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a))
    (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1,0)
    (D.analytic _ (D.contains _)).differentiableAt (analyticAt_miuraMassActionFactor _).differentiableAt
    (fun b => D.recovery _) (fun b => miuraL2MassActionData.recovery _)
    (exists_H1_profile_on_L2_positive_action_ray a n hn)
  exact h.trans (fderiv_miuraMassActionFactor_single _ n)

/-- Every analytic mass normal form has the same raw positive action
derivative on every real original L² profile, including a closed action. -/
theorem frequency_eq (D : MiuraL2MassActionData) (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (n : ℤ) (hn : 0 < n) :
    D.frequency n (miuraL2ActionMeanMap a) = 2*(Real.pi : ℂ)*n := by
  apply realL2_eq_of_realH1_agreement
    (fun b => D.frequency n (miuraL2ActionMeanMap b)) (fun _ => 2*(Real.pi : ℂ)*n) _ a ha
    (D.source_frequency_analyticAt n a ha).continuousAt continuousAt_const
  intro b hb
  have h := D.frequency_H1 ⟨miuraH1SobolevEquiv b,miuraH1SobolevReal b hb⟩ n hn
  change D.frequency n (miuraL2ActionMeanMap
    (miuraPhysicalSobolevL2SourceInclusion 1 ⟨miuraH1SobolevEquiv b,miuraH1SobolevReal b hb⟩).val) = _ at h
  rwa [miuraPhysicalSobolevL2SourceInclusion_H1 b hb] at h

end MiuraL2MassActionData
end NLS.MKdV
