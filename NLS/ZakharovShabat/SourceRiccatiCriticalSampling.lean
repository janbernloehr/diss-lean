import NLS.ZakharovShabat.SobolevRiccatiPerturbedLattice
import NLS.ZakharovShabat.SourceCriticalDisplacementContinuity
import NLS.ZakharovShabat.SourceHigherSobolevFiniteGapDensity

/-! # Sampling at actual canonical critical points

The full displacement continuity gives a local L2 bound on actual critical-point samples near every real original Sobolev source.
-/

noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Uniform sampling at the original canonical critical points, with the
actual displacement norm retained as the explicit spectral budget. -/
theorem exists_uniform_sobolevRiccati_critical_sample_bound
    (s N : ℕ) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R →
      ‖sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab)‖ ≤ D →
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ c : NLS.Coeff 2,
        (∀ n, c n = ∫ x in (0:ℝ)..1, nlsRiccatiDensity a b N x*
          exp (-2*I*canonicalCriticalPoints (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab))
            (periodOnePotential_mem (higherSobolevSourceInclusion s ab)) n*x)) ∧ ‖c‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := exists_uniform_sobolevRiccati_perturbed_lattice_bound s N hNs R hR D hD
  refine ⟨C,hC,?_⟩
  intro ab hab hδ a b ha hb hpa hpb hca hcb
  obtain ⟨c,hc,hn⟩ := h ab hab a b ha hb hpa hpb hca hcb
    (sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab)) hδ
  refine ⟨c,?_,hn⟩
  intro n
  have hn := hc n
  simp only [sourceCriticalDisplacement,canonicalCriticalDisplacement_apply] at hn
  have he : (Real.pi:ℂ)*n+(canonicalCriticalPoints (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab))
            (periodOnePotential_mem (higherSobolevSourceInclusion s ab)) n-(Real.pi:ℂ)*n) =
      canonicalCriticalPoints (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab))
            (periodOnePotential_mem (higherSobolevSourceInclusion s ab)) n := by ring
  simpa only [he] using hn

/-- At every real Hs source, the actual canonical critical-point samples
of the top density have one L2 bound on a complex source neighborhood. -/
theorem exists_local_sobolevRiccati_critical_sample_bound
    (s N : ℕ) (hNs : N ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ c : NLS.Coeff 2,
        (∀ n, c n = ∫ x in (0:ℝ)..1, nlsRiccatiDensity a b N x*
          exp (-2*I*canonicalCriticalPoints (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab))
            (periodOnePotential_mem (higherSobolevSourceInclusion s ab)) n*x)) ∧ ‖c‖ ≤ C := by
  let δ (ab : SobolevSource s) := sourceCriticalDisplacement (by norm_num) (by norm_num)
    (higherSobolevSourceInclusion s ab)
  have hδ : ContinuousAt δ a₀.val :=
    (continuousAt_sourceCriticalDisplacement_of_realType (by norm_num) (by norm_num)
      (higherSobolevSourceInclusion s a₀.val) a₀.property).comp
      (higherSobolevSourceInclusion s).continuous.continuousAt
  let R := ‖a₀.val‖+1
  let D := ‖δ a₀.val‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hr : ∀ᶠ ab in 𝓝 a₀.val, ‖ab‖ < R := continuousAt_id.norm.eventually
    (gt_mem_nhds (by dsimp [R]; linarith))
  have hd : ∀ᶠ ab in 𝓝 a₀.val, ‖δ ab‖ < D := hδ.norm.eventually
    (gt_mem_nhds (by dsimp [D]; linarith))
  obtain ⟨U,hsub,hU,haU⟩ := mem_nhds_iff.mp (hr.and hd)
  obtain ⟨C,hC,h⟩ := exists_uniform_sobolevRiccati_critical_sample_bound s N hNs R hR D hD
  refine ⟨U,hU,haU,C,hC,?_⟩
  intro ab hab
  exact h ab (hsub hab).1.le (hsub hab).2.le

end NLS.ZakharovShabat
