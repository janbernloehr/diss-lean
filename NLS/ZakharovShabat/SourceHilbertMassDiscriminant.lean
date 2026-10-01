import NLS.ZakharovShabat.SourceHilbertMass
import NLS.ZakharovShabat.ClassicalDiscriminantPhaseStationarity
import NLS.ZakharovShabat.FiniteSourceDiscriminantGradient

/-! # Actual source mass commutes with every discriminant

Exact finite Fourier realization transfers the physical infinitesimal
phase identity to the actual source cotangent. Joint cotangent continuity
and finite Fourier density give the identity at every complex Hilbert
source. The proved mass Hamiltonian direction and source antisymmetry
then establish mass/discriminant commutation with no spectral or norm
invariance assumption.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

private theorem polynomial_smul (c : ℂ) (a : ℤ →₀ ℂ) (t : ℝ) :
    polynomial (c • a) t = c*polynomial a t := by
  unfold polynomial
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.sum,Finset.mul_sum,mul_assoc]

/-- The actual Hilbert source discriminant annihilates the mass phase
direction on finite Fourier sources, by its exact physical realization. -/
theorem sourceDiscriminantCotangent_neg_sourcePhase_finite_eq_zero
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceDiscriminantCotangent (by simp) z (CoeffPair.ofFinsupp (p := 2) a)
      (-sourcePhase (CoeffPair.ofFinsupp (p := 2) a)) = 0 := by
  let b : (ℤ →₀ ℂ) × (ℤ →₀ ℂ) := (-I • a.1,I • a.2)
  have hb : CoeffPair.ofFinsupp (p := 2) b = -sourcePhase (CoeffPair.ofFinsupp (p := 2) a) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext
    · ext n
      change -I*a.1 n = -(I*a.1 n)
      ring
    · ext n
      change I*a.2 n = -(-I*a.2 n)
      ring
  have hcurve : finiteSourceCurve b = classicalMassHamiltonianDirection (finiteSourceCurve a) := by
    apply ContinuousMap.ext
    intro t
    apply Prod.ext
    · exact polynomial_smul (-I) a.1 t
    · exact polynomial_smul I a.2 t
  rw [← hb,sourceDiscriminantCotangent_finite_direction,hcurve]
  exact fderiv_classicalDiscriminant_massHamiltonianDirection_eq_zero _ z

/-- Actual infinitesimal source phase invariance at every complex
Hilbert source follows from finite Fourier density and cotangent continuity. -/
theorem sourceDiscriminantCotangent_neg_sourcePhase_eq_zero (φ : CoeffPair 2) (z : ℂ) :
    sourceDiscriminantCotangent (by simp) z φ (-sourcePhase φ) = 0 := by
  let F : CoeffPair 2 → ℂ := fun ψ => sourceDiscriminantCotangent (by simp) z ψ (-sourcePhase ψ)
  have hC : Continuous F := by
    have hL : Continuous (fun ψ : CoeffPair 2 => sourceDiscriminantCotangent (by simp) z ψ) := by
      apply continuous_iff_continuousAt.mpr
      intro ψ
      exact ((analyticOnNhd_sourceDiscriminantCotangent_joint (p := 2) (by simp) (by norm_num)
        (z,ψ) (mem_univ _)).comp (f := fun χ : CoeffPair 2 => (z,χ))
        (analyticAt_const.prod analyticAt_id)).continuousAt
    exact hL.clm_apply ((sourcePhase (p := 2)).continuous.neg)
  have heq : F = (fun _ => (0:ℂ)) := (denseRange_finiteSourcePairs (by simp)).equalizer hC continuous_const (by
    funext a
    exact sourceDiscriminantCotangent_neg_sourcePhase_finite_eq_zero a z)
  exact congrFun heq φ

/-- The actual source mass cotangent commutes with every actual
fixed-parameter discriminant cotangent at every complex Hilbert source. -/
theorem sourceBivector_mass_discriminant_eq_zero (φ : CoeffPair 2) (z : ℂ) :
    sourceBivector (by norm_num) (fderiv ℂ sourceHilbertMass φ)
      (sourceDiscriminantCotangent (by simp) z φ) = 0 := by
  rw [sourceBivector_antisymm,← apply_sourceHamiltonianDirection]
  change -(sourceDiscriminantCotangent (by simp) z φ)
    (sourceHamiltonianVector (by norm_num) sourceHilbertMass φ) = 0
  rw [sourceHamiltonianVector_sourceHilbertMass_eq_neg_sourcePhase,
    sourceDiscriminantCotangent_neg_sourcePhase_eq_zero,neg_zero]

/-- The original Hilbert mass functional commutes with every actual
source discriminant. No real-type restriction is required. -/
theorem sourceBracket_mass_discriminant_eq_zero (φ : CoeffPair 2) (z : ℂ) :
    sourceBracket (by norm_num) sourceHilbertMass
      (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) z) φ = 0 :=
  sourceBivector_mass_discriminant_eq_zero φ z

end NLS.ZakharovShabat
