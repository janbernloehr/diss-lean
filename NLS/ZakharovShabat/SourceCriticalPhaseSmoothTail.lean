import NLS.ZakharovShabat.SobolevNextHamiltonianPhase
import NLS.ZakharovShabat.SobolevWKBCriticalPhaseTail
import NLS.ZakharovShabat.SourceCriticalWeightedDisplacement
import NLS.ZakharovShabat.SourceSobolevClassicalCompatibility

/-! # The next-phase offset at canonical critical points

Canonical root localization transfers the smooth phase estimate to the original source with a common tail cutoff.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual next-phase offset at a canonically labelled critical point. -/
def sourceCriticalNextPhaseOffset (s : ℕ) (ab : SobolevSource s) (n : ℤ) : ℂ :=
  sobolevNextHamiltonianPhase s ab
    (canonicalCriticalPoints (by norm_num) (by norm_num)
      (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n)+
    I*(Real.pi:ℂ)*n

/-- The canonical critical sequence lies away from the phase pole on a
common tail, and matching smooth representatives give the uniform
H^(s+1) bound for the literal next-phase offset. -/
theorem exists_local_source_critical_phase_smooth_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ab ∈ U,
      (∀ n : ℤ, K ≤ n.natAbs → 1 ≤
        ‖canonicalCriticalPoints (by norm_num) (by norm_num)
          (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n‖) ∧
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then sourceCriticalNextPhaseOffset s ab n else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨U,hU,haU,R,D,M,hR,hD,_,hdata⟩ :=
    exists_local_higherSobolev_critical_weighted_displacement_bounds s hs a₀
  obtain ⟨K₀,hK₀,C,hC,h⟩ := exists_uniform_nlsWKB_critical_phase_fourier_tail_bound s hs R D M hR hD
  obtain ⟨K₁,_,hgeom⟩ := exists_wkb_leading_frequency_cutoff D M hD
  let K := max K₀ K₁
  refine ⟨U,hU,haU,K,hK₀.trans_le (le_max_left _ _),C,hC,?_⟩
  intro ab hab
  obtain ⟨habR,habD,habM⟩ := hdata ab hab
  let δ₂ := sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  have hν (n : ℤ) : (Real.pi:ℂ)*n+δ n =
      canonicalCriticalPoints (by norm_num) (by norm_num)
        (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n := by
    simp only [δ,Coeff.exponentInclusion_apply,δ₂,sourceCriticalDisplacement,canonicalCriticalDisplacement_apply]
    ring
  refine ⟨?_,?_⟩
  · intro n hn
    have hz := (hgeom δ (fun j => (lp.norm_apply_le_norm (by simp) δ j).trans hδD) hδM n
      ((le_max_right _ _).trans hn)).2
    rw [hν n] at hz
    linarith [abs_nonneg (n:ℝ)]
  · intro a b ha hb hpa hpb hca hcb
    have hdisc : classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) =
        canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab)) := by
      funext z
      exact (higherSobolev_spectral_functions_eq_classical s hs ab a b
        ha.continuous hb.continuous hpa hpb hca hcb z).1.symm
    have hcrit (n : ℤ) (_ : K ≤ n.natAbs) :
        deriv (classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous))
          ((Real.pi:ℂ)*n+δ n) = 0 := by
      rw [hdisc,hν n]
      exact canonicalCriticalPoints_is_critical (by norm_num) (by norm_num) _ _ n
    obtain ⟨f,hf,hfn⟩ := h K (le_max_left _ _) ab habR a b ha hb hpa hpb hca hcb δ hδD hδM hcrit
    refine ⟨f,?_,hfn⟩
    intro n
    rw [hf n]
    split_ifs with hn
    · rw [hν n]
      simp only [sourceCriticalNextPhaseOffset,sobolevNextHamiltonianPhase_eq_classical s ab a b ha hb hpa hpb hca hcb]
    · rfl

end NLS.ZakharovShabat
