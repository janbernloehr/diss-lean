import NLS.ZakharovShabat.SobolevBoundaryPhaseFourierTail
import NLS.ZakharovShabat.SobolevNextHamiltonianPhase
import NLS.ZakharovShabat.SourceBoundaryWeightedDisplacement
import NLS.ZakharovShabat.SourceSobolevClassicalCompatibility

/-! # The canonical source boundary phase Fourier tail

Canonical root localization and exact source compatibility give a common Fourier tail bound for matching smooth representatives.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The next Hamiltonian phase offset at the canonically labelled boundary root. -/
def sourceBoundaryNextPhaseOffset (s : ℕ) (θ : BoundaryCondition)
    (ab : SobolevSource s) (n : ℤ) : ℂ :=
  sobolevNextHamiltonianPhase s ab
    (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
      (higherSobolevSourceInclusion s ab) n)+I*(Real.pi:ℂ)*n

/-- Canonical boundary roots avoid the phase pole on one common tail;
matching smooth representatives give the original Fourier half-sum with
an H^(s+1) remainder on one original-source neighborhood. -/
theorem exists_local_source_boundary_phase_smooth_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ab ∈ U,
      (∀ n : ℤ, K ≤ n.natAbs → 1 ≤
        ‖canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
          (higherSobolevSourceInclusion s ab) n‖) ∧
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          sourceBoundaryNextPhaseOffset s θ ab n+(extensionSign θ*I/2)*(ab.1.val (-n)+ab.2.val n)
          else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨U,hU,haU,R,D,M,hR,hD,hM,hdata⟩ :=
    exists_local_higherSobolev_boundary_weighted_displacement_bounds s hs a₀ θ
  obtain ⟨K₀,hK₀,C,hC,h⟩ := exists_uniform_boundary_phase_fourier_tail_bound s hs R D M hR hD hM
  obtain ⟨K₁,_,hgeom⟩ := exists_wkb_leading_frequency_cutoff D M hD
  let K := max K₀ K₁
  refine ⟨U,hU,haU,K,hK₀.trans_le (le_max_left _ _),C,hC,?_⟩
  intro ab hab
  obtain ⟨habR,habD,habM⟩ := hdata ab hab
  let δ₂ := sourceBoundaryDisplacement (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  have hν (n : ℤ) : (Real.pi:ℂ)*n+δ n =
      canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab) n := by
    simp only [δ,Coeff.exponentInclusion_apply,δ₂,sourceBoundaryDisplacement_apply]
    ring
  refine ⟨?_,?_⟩
  · intro n hn
    have hz := (hgeom δ (fun j => (lp.norm_apply_le_norm (by simp) δ j).trans hδD) hδM n
      ((le_max_right _ _).trans hn)).2
    rw [hν n] at hz
    linarith [abs_nonneg (n:ℝ)]
  · intro a b ha hb hpa hpb hca hcb
    have hroot (n : ℤ) (_ : K ≤ n.natAbs) : classicalSeparatedCharacteristic θ
        (classicalPotentialOfFunctions a b ha.continuous hb.continuous) ((Real.pi:ℂ)*n+δ n) = 0 := by
      rw [hν n]
      exact classicalSeparatedCharacteristic_higherSobolev_canonicalRoot_eq_zero s hs ab a b
        ha.continuous hb.continuous hpa hpb hca hcb θ n
    obtain ⟨f,hf,hfn⟩ := h K (le_max_left _ _) ab habR a b ha hb hpa hpb hca hcb δ hδD hδM θ hroot
    refine ⟨f,?_,hfn⟩
    intro n
    rw [hf n]
    split_ifs with hn
    · rw [hν n]
      simp only [sourceBoundaryNextPhaseOffset,sobolevNextHamiltonianPhase_eq_classical s ab a b ha hb hpa hpb hca hcb]
    · rfl

end NLS.ZakharovShabat
