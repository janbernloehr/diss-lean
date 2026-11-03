import NLS.MKdV.MiuraNativeHamiltonianMassActionFactor
import NLS.MKdV.MiuraNativePhysicalActionRays
import NLS.ComplexAnalysis.AnalyticFactorDirectionUnique

/-! # Intrinsic analytic action frequencies of the independent Hill hierarchy

Different global native normal forms give the same positive action
derivatives at every physical profile. One-sided realized action rays
prove uniqueness even at a collapsed selected action.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

structure MiuraNativeHamiltonianActionData (s : ℕ) where
  domain : Set (MiuraNativeActionMeanTarget s)
  hamiltonian : MiuraNativeActionMeanTarget s → ℂ
  domain_open : IsOpen domain
  contains : ∀ a : MiuraRealSobolevSource s, miuraNativeActionMeanMap s a.val ∈ domain
  analytic : AnalyticOnNhd ℂ hamiltonian domain
  recovery : ∀ a : MiuraRealSobolevSource s,
    hamiltonian (miuraNativeActionMeanMap s a.val) = miuraSpectralHillHamiltonian s a.val

theorem nonempty_miuraNativeHamiltonianActionData (s : ℕ) : Nonempty (MiuraNativeHamiltonianActionData s) := by
  obtain ⟨V,F,hV,hall,hF,hrec⟩ := exists_global_native_miuraHamiltonian_action_factor_allOrders s
  exact ⟨⟨V,F,hV,hall,hF,hrec⟩⟩

namespace MiuraNativeHamiltonianActionData
variable {s : ℕ}

def frequency (D : MiuraNativeHamiltonianActionData s) (n : ℤ) (b : MiuraNativeActionMeanTarget s) : ℂ :=
  fderiv ℂ D.hamiltonian b (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight s) n 1,0)

theorem frequency_analytic (D : MiuraNativeHamiltonianActionData s) (n : ℤ) :
    AnalyticOnNhd ℂ (D.frequency n) D.domain := by
  intro b hb
  exact ((ContinuousLinearMap.apply (E := MiuraNativeActionMeanTarget s) ℂ ℂ).analyticAt_bilinear _).comp₂
    analyticAt_const (D.analytic b hb).fderiv

/-- The frequency is independent of the global analytic factor chosen
to represent K_(s+1), at every physical H^s profile and positive index.
The selected action may be closed; no genericity assumption is used. -/
theorem frequency_unique (D E : MiuraNativeHamiltonianActionData s) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℤ) (hn : 0 < n) :
    D.frequency n (miuraNativeActionMeanMap s a.val) = E.frequency n (miuraNativeActionMeanMap s a.val) := by
  exact NLS.ComplexAnalysis.fderiv_eq_of_nonnegative_ray_realization
    D.hamiltonian E.hamiltonian (fun b : MiuraRealSobolevSource s => miuraNativeActionMeanMap s b.val)
    (fun b : MiuraRealSobolevSource s => miuraSpectralHillHamiltonian s b.val)
    (miuraNativeActionMeanMap s a.val) (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight s) n 1,0)
    (D.analytic _ (D.contains a)).differentiableAt (E.analytic _ (E.contains a)).differentiableAt
    D.recovery E.recovery (exists_native_profile_on_positive_action_ray s hs a n hn)

end MiuraNativeHamiltonianActionData
end NLS.MKdV
