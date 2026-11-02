import NLS.ZakharovShabat.SourceActionPhaseGlobalODE
import NLS.Dynamics.ScalarPhaseUniqueness

/-! # Original finite action equations determine the actual Birkhoff trajectory -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The finite original Hamiltonian ODE, together with its actual finite
coordinate support, determines all complex Birkhoff coordinates for all time. -/
theorem complex_map_eq_phase_of_finiteAction_ode
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (h2p : 2 ≤ p)
    (freq : ℤ → ℝ) (S : Finset ℤ) (γ : ℝ → realTypeSourceSubmodule p)
    (hd : ∀ τ : ℝ, HasDerivAt (fun σ => (γ σ).val)
      (sourceFiniteActionHamiltonianVector hp hp1 h2p freq S (γ τ).val) τ)
    (hz : ∀ τ : ℝ, ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s (γ τ).val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s (γ τ).val).2 n = 0) (τ : ℝ) :
    sourceComplexBirkhoffMap hp hp1 s (γ τ).val =
      Birkhoff.hamiltonianPhaseFlow freq τ (sourceComplexBirkhoffMap hp hp1 s (γ 0).val) := by
  have hfull (r : ℝ) : HasDerivAt (fun σ => sourceComplexBirkhoffMap hp hp1 s (γ σ).val)
      (Birkhoff.finiteHamiltonianPhaseVelocity freq S (sourceComplexBirkhoffMap hp hp1 s (γ r).val)) r := by
    have hc := ((D.complex_map_analytic (γ r).val (D.real_subset (γ r).property)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r (hd r)
    change HasDerivAt (fun σ => sourceComplexBirkhoffMap hp hp1 s (γ σ).val)
      ((fderiv ℂ (sourceComplexBirkhoffMap hp hp1 s) (γ r).val)
        (sourceFiniteActionHamiltonianVector hp hp1 h2p freq S (γ r).val)) r at hc
    rw [D.complex_jacobian_finiteActionHamiltonian] at hc
    exact hc
  let ex (n : ℤ) := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
    (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
  let ey (n : ℤ) := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
    (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
  apply Prod.ext
  · ext n
    have hscalar (r : ℝ) : HasDerivAt (fun σ => (sourceComplexBirkhoffMap hp hp1 s (γ σ).val).1 n)
        (-I*(freq n:ℂ)*(sourceComplexBirkhoffMap hp hp1 s (γ r).val).1 n) r := by
      have h := ((ex n).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r (hfull r)
      change HasDerivAt (fun σ => (sourceComplexBirkhoffMap hp hp1 s (γ σ).val).1 n)
        ((Birkhoff.finiteHamiltonianPhaseVelocity freq S (sourceComplexBirkhoffMap hp hp1 s (γ r).val)).1 n) r at h
      by_cases hn : n ∈ S
      · simpa only [Birkhoff.finiteHamiltonianPhaseVelocity_fst,if_pos hn] using h
      · simpa only [Birkhoff.finiteHamiltonianPhaseVelocity_fst,if_neg hn,(hz r n hn).1,mul_zero] using h
    have h := NLS.Dynamics.eq_exp_mul_of_hasDerivAt (-I*(freq n:ℂ)) _ hscalar τ
    rw [Birkhoff.hamiltonianPhaseFlow_fst]
    have he : (-I*(freq n:ℂ))*(τ:ℂ) = (((-τ*freq n:ℝ):ℂ)*I) := by push_cast; ring
    rw [he] at h
    exact h
  · ext n
    have hscalar (r : ℝ) : HasDerivAt (fun σ => (sourceComplexBirkhoffMap hp hp1 s (γ σ).val).2 n)
        (I*(freq n:ℂ)*(sourceComplexBirkhoffMap hp hp1 s (γ r).val).2 n) r := by
      have h := ((ey n).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r (hfull r)
      change HasDerivAt (fun σ => (sourceComplexBirkhoffMap hp hp1 s (γ σ).val).2 n)
        ((Birkhoff.finiteHamiltonianPhaseVelocity freq S (sourceComplexBirkhoffMap hp hp1 s (γ r).val)).2 n) r at h
      by_cases hn : n ∈ S
      · simpa only [Birkhoff.finiteHamiltonianPhaseVelocity_snd,if_pos hn] using h
      · simpa only [Birkhoff.finiteHamiltonianPhaseVelocity_snd,if_neg hn,(hz r n hn).2,mul_zero] using h
    have h := NLS.Dynamics.eq_exp_mul_of_hasDerivAt (I*(freq n:ℂ)) _ hscalar τ
    rw [Birkhoff.hamiltonianPhaseFlow_snd]
    have he : (I*(freq n:ℂ))*(τ:ℂ) = (((τ*freq n:ℝ):ℂ)*I) := by push_cast; ring
    rw [he] at h
    exact h

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
