import NLS.ZakharovShabat.ClassicalSolutionEnergyBound
import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.ZakharovShabat.SourceDiscriminantCotangent
import NLS.Fourier.IntervalParseval
import Mathlib.Analysis.Complex.Schwarz

/-! # Uniform discriminant and cotangent bounds on Hilbert source balls

Parseval identifies the physical energy of finite Fourier sources with
the square of their original source norm. Exact physical realization
and finite Fourier density extend the actual trace estimate to every
complex Hilbert source. The Banach-space Schwarz lemma then bounds the
full source cotangent on a unit ball, without a physical supremum bound.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The physical energy uses both components and is exactly the square
of the original Hilbert source-pair norm. -/
theorem classicalPotentialEnergy_finiteSourceCurve (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    classicalPotentialEnergy (finiteSourceCurve a) = ‖CoeffPair.ofFinsupp (p := 2) a‖^2 := by
  have he : classicalPotentialEnergy (finiteSourceCurve a) =
      ∫ s in (0 : ℝ)..1, ‖polynomial a.1 s‖^2 + ‖polynomial a.2 s‖^2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    dsimp only
    rw [extend_finiteSourceCurve a s hs']
    rfl
  have hi₁ : IntervalIntegrable (fun s : ℝ => ‖polynomial a.1 s‖^2) volume 0 1 :=
    ((continuous_polynomial a.1).norm.pow 2).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun s : ℝ => ‖polynomial a.2 s‖^2) volume 0 1 :=
    ((continuous_polynomial a.2).norm.pow 2).intervalIntegrable 0 1
  rw [he,intervalIntegral.integral_add hi₁ hi₂,
    integral_sq_polynomial,integral_sq_polynomial,WithLp.prod_norm_sq_eq_of_L2]
  change _ = ‖Coeff.ofFinsupp (p := 2) a.1‖^2 + ‖Coeff.ofFinsupp (p := 2) a.2‖^2
  rw [Coeff.norm_ofFinsupp_sq,Coeff.norm_ofFinsupp_sq]

/-- Every actual complex Hilbert source satisfies the physical trace
bound, extended by density from its exact finite Fourier realization. -/
theorem norm_sourceDiscriminant_le_exp_energy (φ : CoeffPair 2) (z : ℂ) :
    ‖canonicalDiscriminant (by simp) (periodOnePotential φ) z‖ ≤
      2 * Real.exp (‖z‖ + 1 + ‖φ‖^2) := by
  have hF : Continuous (fun ψ : CoeffPair 2 =>
      canonicalDiscriminant (by simp) (periodOnePotential ψ) z) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_canonicalDiscriminant_periodOne (p := 2) (by simp) (by norm_num)
      (z,ψ) (mem_univ _)).comp (f := fun χ : CoeffPair 2 => (z,χ))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  refine (denseRange_finiteSourcePairs (p := 2) (by simp)).induction_on φ
    (isClosed_le hF.norm (by fun_prop)) ?_
  intro a
  rw [canonicalDiscriminant_finite_eq_classical]
  simpa only [classicalPotentialEnergy_finiteSourceCurve] using
    norm_classicalDiscriminant_le_exp_energy (finiteSourceCurve a) z

/-- A uniform bound for the full actual source differential. The unit
source ball adds one to the source norm; the factor four also controls
the distance from the value at its center. -/
theorem norm_sourceDiscriminantCotangent_le_exp_energy (φ : CoeffPair 2) (z : ℂ) :
    ‖sourceDiscriminantCotangent (by simp) z φ‖ ≤
      4 * Real.exp (‖z‖ + 1 + (‖φ‖+1)^2) := by
  let F : CoeffPair 2 → ℂ := fun ψ =>
    canonicalDiscriminant (by simp) (periodOnePotential ψ) z
  let B : ℝ := 2 * Real.exp (‖z‖ + 1 + (‖φ‖+1)^2)
  have hF : Differentiable ℂ F := by
    intro ψ
    exact ((analyticOnNhd_canonicalDiscriminant_periodOne (p := 2) (by simp) (by norm_num)
      (z,ψ) (mem_univ _)).comp (f := fun χ : CoeffPair 2 => (z,χ))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hbound (ψ : CoeffPair 2) (hψ : ‖ψ‖ ≤ ‖φ‖+1) : ‖F ψ‖ ≤ B := by
    apply (norm_sourceDiscriminant_le_exp_energy ψ z).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hs := sq_le_sq₀ (norm_nonneg ψ) (by positivity : 0 ≤ ‖φ‖+1) |>.mpr hψ
    linarith
  have hcenter : ‖F φ‖ ≤ B := hbound φ (by linarith)
  have hmaps : MapsTo F (ball φ 1) (closedBall (F φ) (2*B)) := by
    intro ψ hψ
    have hnorm : ‖ψ‖ ≤ ‖φ‖+1 := by
      have hdist : ‖ψ-φ‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hψ
      have htri := norm_add_le (ψ-φ) φ
      rw [sub_add_cancel] at htri
      linarith
    change dist (F ψ) (F φ) ≤ 2*B
    rw [dist_eq_norm]
    have h := (norm_sub_le (F ψ) (F φ)).trans (add_le_add (hbound ψ hnorm) hcenter)
    linarith
  have h := Complex.norm_fderiv_le_div_of_mapsTo_ball hF.differentiableOn hmaps
    (by norm_num : (0 : ℝ) < 1)
  change ‖fderiv ℂ F φ‖ ≤ _
  simpa only [div_one,B,← mul_assoc,show (2 : ℝ)*2 = 4 by norm_num] using h

/-- One explicit cotangent bound works for a Hilbert source norm ball
and a bounded set of spectral parameters, including complex sources. -/
theorem norm_sourceDiscriminantCotangent_le_of_bounds (φ : CoeffPair 2) (z : ℂ)
    (M R : ℝ) (hφ : ‖φ‖ ≤ M) (hz : ‖z‖ ≤ R) :
    ‖sourceDiscriminantCotangent (by simp) z φ‖ ≤
      4 * Real.exp (R + 1 + (M+1)^2) := by
  have hM : 0 ≤ M := (norm_nonneg φ).trans hφ
  apply (norm_sourceDiscriminantCotangent_le_exp_energy φ z).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hs := sq_le_sq₀ (by positivity : 0 ≤ ‖φ‖+1) (by positivity : 0 ≤ M+1)
    |>.mpr (by linarith)
  linarith

end NLS.ZakharovShabat
