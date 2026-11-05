import NLS.KdV.HillHminusOneUniformAnnularRoot
import NLS.KdV.HillFreeEnergyHomotopyGeometry
import NLS.ComplexAnalysis.SquaredCircleAffineIntegral
import NLS.ComplexAnalysis.BilinearCircleIntegral
import NLS.SequenceSpaces.Basic
/-! # Exact complex rough frequency-to-energy periods on one source ball

A covered annulus shrinks the original frequency contour. Its squared
inner circle deforms through the explicit covered energy shell. Native
Bochner Kronecker periods transfer by bounded coefficient evaluation.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_frequency_energy_period_transfer :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ k : ℕ+,
      (∀ E ∈ sphere (freeHillEnergy k) (k : ℝ), (E,q) ∈ hillHminusContinuationDomain) ∧
      ∀ P : ℂ → ℂ, AnalyticOnNhd ℂ P univ →
        (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          P (z^2)/hillHminusContinuedRoot (z^2,q)*(2*z)) =
        ∮ E in C(freeHillEnergy k,(k : ℝ)), P E/hillHminusContinuedRoot (E,q) := by
  have hr : 0 < 1/(4*Real.pi) := by positivity
  have hrpi : 1/(4*Real.pi) ≤ Real.pi/4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  obtain ⟨δ,_,hδ,_,_,hroot⟩ := exists_hillHminus_uniform_annular_root_bound _ hr hrpi
  refine ⟨δ,hδ,?_⟩
  intro q hq k
  have hcover (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) :
      (E,q) ∈ hillHminusContinuationDomain := by
    obtain ⟨hz,hfar⟩ := hillFreeEnergyCircle_frequency_bounds k E hE
    have hzq := closedBall_subset_closedBall (by linarith [Real.pi_pos] : Real.pi/8 ≤ Real.pi/4) hz
    simpa only [sq_sqrt] using (hroot q hq k (sqrt E) hzq hfar).1
  refine ⟨hcover,?_⟩
  intro P hP
  let D : Set ℂ := {E | (E,q) ∈ hillHminusContinuationDomain}
  let f : ℂ → ℂ := fun E => P E/hillHminusContinuedRoot (E,q)
  have hf : AnalyticOnNhd ℂ f D := by
    intro E hE
    exact (hP E (mem_univ _)).div
      ((analyticOnNhd_hillHminusContinuedRoot (E,q) hE).comp
        (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const))
      (hillHminusSourceFamily.root_ne_zero _ hE)
  have hpath (s : Set.Icc (0 : ℝ) 1) (theta : ℝ) :
      AffineMap.lineMap (circleMap (freeHillEnergy k) (k : ℝ) theta)
        ((circleMap ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/16) theta)^2) (s : ℝ) ∈ D := by
    let E := AffineMap.lineMap (circleMap (freeHillEnergy k) (k : ℝ) theta)
      ((circleMap ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/16) theta)^2) (s : ℝ)
    obtain ⟨hE,hfar⟩ := hillFreeEnergyCircle_squaredCircle_homotopy_shell k s theta
    obtain ⟨hz,hzfar⟩ := hillFreeEnergyShell_frequency_bounds k E hE hfar
    change (E,q) ∈ hillHminusContinuationDomain
    simpa only [sq_sqrt] using (hroot q hq k (sqrt E) hz hzfar).1
  have hhom := circleIntegral_squared_pullback_eq_circle_of_affine_mem f D
    (freeHillEnergy k) ((Real.pi : ℂ)*(k : ℕ)) (k : ℝ) (Real.pi/16) hf hpath
  let A := closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) \
    ball ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/16)
  have hsmall : 1/(4*Real.pi) ≤ Real.pi/16 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  have hfa : AnalyticOnNhd ℂ (fun z : ℂ => f (z^2)*(2*z)) A := by
    intro z hz
    have hfar : Real.pi/16 ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖ := by
      have hh := hz.2
      simpa only [mem_ball,dist_eq_norm,not_lt] using hh
    have ht := (hroot q hq k z hz.1 (hsmall.trans hfar)).1
    exact ((hf (z^2) ht).comp (f := fun w : ℂ => w^2) (analyticAt_id.pow 2)).mul (analyticAt_const.mul analyticAt_id)
  have heq := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (c := ((Real.pi : ℂ)*(k : ℕ))) (r := Real.pi/16) (R := Real.pi/4)
    (by positivity) (by linarith [Real.pi_pos]) (s := (∅ : Set ℂ)) countable_empty
    hfa.continuousOn (by
      intro z hz
      exact (hfa z ⟨ball_subset_closedBall hz.1.1,fun hh => hz.1.2 (ball_subset_closedBall hh)⟩).differentiableAt)
  exact heq.trans hhom

/-- Bounded coefficient evaluation transfers the genuine native Bochner
period; no coordinatewise reconstruction or series interchange is assumed. -/
theorem hillHminus_native_frequency_period_gives_energy_period
    (q : PeriodOneHminusOne) (k : ℕ+) (F : ℂ → Coeff 2)
    (hF : AnalyticOnNhd ℂ F univ)
    (hcover : ∀ E ∈ sphere (freeHillEnergy k) (k : ℝ), (E,q) ∈ hillHminusContinuationDomain)
    (htransfer : ∀ P : ℂ → ℂ, AnalyticOnNhd ℂ P univ →
      (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), P (z^2)/hillHminusContinuedRoot (z^2,q)*(2*z)) =
        ∮ E in C(freeHillEnergy k,(k : ℝ)), P E/hillHminusContinuedRoot (E,q))
    (hperiod : CircleIntegrable (fun z : ℂ => ((2*z)/hillHminusContinuedRoot (z^2,q)) • F (z^2))
        ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) ∧
      (2*(Real.pi : ℂ))⁻¹ • (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        ((2*z)/hillHminusContinuedRoot (z^2,q)) • F (z^2)) = lp.single 2 (k : ℤ) 1) :
    CircleIntegrable (fun E : ℂ => (hillHminusContinuedRoot (E,q))⁻¹ • F E)
      (freeHillEnergy k) (k : ℝ) ∧
    (2*(Real.pi : ℂ))⁻¹ • (∮ E in C(freeHillEnergy k,(k : ℝ)),
      (hillHminusContinuedRoot (E,q))⁻¹ • F E) = lp.single 2 (k : ℤ) 1 := by
  have hA : AnalyticOnNhd ℂ (fun E : ℂ => (hillHminusContinuedRoot (E,q))⁻¹ • F E)
      (sphere (freeHillEnergy k) (k : ℝ)) := by
    intro E hE
    have ht := hcover E hE
    exact (((analyticOnNhd_hillHminusContinuedRoot (E,q) ht).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)).inv
      (hillHminusSourceFamily.root_ne_zero _ ht)).smul (hF E (mem_univ _))
  have hi := hA.continuousOn.circleIntegrable (by positivity : (0 : ℝ) ≤ k)
  refine ⟨hi,?_⟩
  have heq : (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillHminusContinuedRoot (E,q))⁻¹ • F E) =
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), ((2*z)/hillHminusContinuedRoot (z^2,q)) • F (z^2) := by
    ext j
    let ev : Coeff 2 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j
    change ev (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillHminusContinuedRoot (E,q))⁻¹ • F E) =
      ev (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), ((2*z)/hillHminusContinuedRoot (z^2,q)) • F (z^2))
    rw [map_circleIntegral ev hi,map_circleIntegral ev hperiod.1]
    have hp : AnalyticOnNhd ℂ (fun E => F E j) univ := by
      intro E hE
      exact (ev.analyticAt _).comp (hF E hE)
    simp only [map_smul]
    change (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillHminusContinuedRoot (E,q))⁻¹ * F E j) =
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), ((2*z)/hillHminusContinuedRoot (z^2,q)) * F (z^2) j
    have ht := htransfer (fun E => F E j) hp
    convert ht.symm using 1 <;> congr 1 <;> funext z <;> ring
  rw [heq,hperiod.2]
end NLS.KdV
