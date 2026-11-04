import NLS.KdV.HillDirichletAnalyticAngles

/-! # Actual differentiable real terminal lifts along rough Hill families

Local analytic sheeted angles composed with the original potential curve
give differentiable real lifts. No global continuous angle choice is used,
and this construction also works at either Dirichlet band terminal.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_differentiable_hillDirichlet_family_angle
    (C : ℝ → RealPeriodOneHillPotential) (t0 : ℝ) (hC : ContinuousAt C t0)
    (hQ : DifferentiableAt ℝ (fun t => SpectralWeight.one.toCoeff (C t).val) t0)
    (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength (C t0).val (C t0).property.1 (C t0).property.2 k ≠ 0) :
    ∃ θ : ℝ → ℝ, DifferentiableAt ℝ θ t0 ∧ ∀ᶠ t in 𝓝 t0,
      hillRealGapHalfLength (C t).val (C t).property.1 (C t).property.2 k ≠ 0 ∧
      cosineGapPoint (hillRealGapCenter (C t).val (C t).property.1 (C t).property.2 k)
        (hillRealGapHalfLength (C t).val (C t).property.1 (C t).property.2 k) (θ t : ℂ) =
          (hillDirichletEnergy (C t).val (C t).property.1 (C t).property.2 k hk : ℂ) ∧
      sin (θ t : ℂ) = hillDirichletGapSine (C t).val (C t).property.1 (C t).property.2 k hk := by
  obtain ⟨ε,e,hε,_,_,hmatch⟩ := exists_hillDirichlet_analytic_sheeted_angle
    (C t0).val (C t0).property.1 (C t0).property.2 k hk hgap
  let θ (t : ℝ) := (ε (SpectralWeight.one.toCoeff (C t).val)).re
  have hεQ : DifferentiableAt ℝ (fun t => ε (SpectralWeight.one.toCoeff (C t).val)) t0 :=
    (hε.differentiableAt.restrictScalars ℝ).comp t0 hQ
  have hθ : DifferentiableAt ℝ θ t0 := Complex.reCLM.differentiableAt.comp t0 hεQ
  refine ⟨θ,hθ,?_⟩
  filter_upwards [hC.tendsto.eventually hmatch] with t ht
  have he : ε (SpectralWeight.one.toCoeff (C t).val) = (θ t : ℂ) := by
    apply Complex.ext
    · rfl
    · exact ht.2.1
  have hp := ht.2.2.1
  have hs := ht.2.2.2
  rw [he] at hp hs
  exact ⟨ht.1,hp,hs⟩

end NLS.KdV
