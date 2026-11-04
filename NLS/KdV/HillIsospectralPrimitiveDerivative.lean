import NLS.KdV.HillIsospectralAbelianData
import NLS.KdV.HillAbelianRealPrimitiveDerivative
import NLS.ComplexAnalysis.AbelianTerminalChainRule

/-! # The actual Abelian terminal derivative along an isospectral family

The primitive is frozen by the independently proved spectral invariance.
Differentiating its moving cosine terminal and using the original sheet
then gives psi(mu)*mu_prime/sheetRoot at every interior divisor point.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hasDerivAt_hillAbelianPrimitive_isospectral_terminal
    (C : ℝ → RealPeriodOneHillPotential) (t0 : ℝ)
    (hl : ∀ t,hillRealLabels (C t).val (C t).property.1 (C t).property.2 =
      hillRealLabels (C t0).val (C t0).property.1 (C t0).property.2)
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ → ℝ) (w : ℝ)
    (hθ : HasDerivAt θ w t0)
    (hterminal : ∀ᶠ t in 𝓝 t0,
      cosineGapPoint (hillRealGapCenter (C t).val (C t).property.1 (C t).property.2 k)
        (hillRealGapHalfLength (C t).val (C t).property.1 (C t).property.2 k) (θ t : ℂ) =
          (hillDirichletEnergy (C t).val (C t).property.1 (C t).property.2 k hk : ℂ) ∧
      sin (θ t : ℂ) = hillDirichletGapSine (C t).val (C t).property.1 (C t).property.2 k hk)
    (hgap : hillRealGapHalfLength (C t0).val (C t0).property.1 (C t0).property.2 k ≠ 0)
    (v : ℂ) (hμ : HasDerivAt (fun t =>
      (hillDirichletEnergy (C t).val (C t).property.1 (C t).property.2 k hk : ℂ)) v t0)
    (hR : hillDirichletSheetRoot (SpectralWeight.one.toCoeff (C t0).val)
      (hillDirichletEnergy (C t0).val (C t0).property.1 (C t0).property.2 k hk) ≠ 0) :
    let q := C t0
    let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
    HasDerivAt (fun t => hillAbelianCosinePrimitive (C t).val (C t).property.1 (C t).property.2
      n hn k (θ t : ℂ))
      (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn μ*v/
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) μ) t0 := by
  let q := C t0
  let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
  let τ : ℂ := hillRealGapCenter q.val q.property.1 q.property.2 k
  let δ : ℂ := hillRealGapHalfLength q.val q.property.1 q.property.2 k
  let U := hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k μ
  have hp0 : cosineGapPoint τ δ (θ t0 : ℂ) = μ :=
    Filter.EventuallyEq.eq_of_nhds (hterminal.mono (fun _ ht => ht.1))
  have hs0 : sin (θ t0 : ℂ) = hillDirichletGapSine q.val q.property.1 q.property.2 k hk :=
    Filter.EventuallyEq.eq_of_nhds (hterminal.mono (fun _ ht => ht.2))
  have hcoord := ((hasDerivAt_cosineGapPoint τ δ (θ t0 : ℂ)).comp_ofReal).scomp t0 hθ
  have hpoint : (fun t => cosineGapPoint τ δ (θ t : ℂ)) =ᶠ[𝓝 t0]
      (fun t => (hillDirichletEnergy (C t).val (C t).property.1 (C t).property.2 k hk : ℂ)) := by
    filter_upwards [hterminal] with t ht
    have hp := ht.1
    rw [hillRealGapCenter_eq_of_labels (C t) q (hl t),
      hillRealGapHalfLength_eq_of_labels (C t) q (hl t)] at hp
    exact hp
  have hv := (hcoord.congr_of_eventuallyEq hpoint.symm).unique hμ
  have hU : U ≠ 0 := hillDeflatedEnergyCanonicalRoot_ne_zero q.val q.property.1 q.property.2 k hk μ (by
    rw [← hp0]
    exact hillCosineGapPoint_mem_filledDomain q.val q.property.1 q.property.2 k hk (θ t0))
  have hδ : δ ≠ 0 := ofReal_ne_zero.mpr hgap
  have hs : sin (θ t0 : ℂ)*(δ*U) = I*hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) μ := by
    apply (eq_div_iff (mul_ne_zero hδ hU)).mp
    exact hs0
  have hd := (hasDerivAt_hillAbelianCosinePrimitive_real q n hn k hk (θ t0)).scomp t0 hθ
  have he : (fun t => hillAbelianCosinePrimitive (C t).val (C t).property.1 (C t).property.2 n hn k (θ t : ℂ)) =ᶠ[𝓝 t0]
      (fun t => hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n hn k (θ t : ℂ)) :=
    Filter.Eventually.of_forall (fun t => congrFun (hillAbelianCosinePrimitive_eq_of_labels (C t) q (hl t) n hn k) _)
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  rw [Complex.real_smul] at hv ⊢
  unfold hillAbelianCosineDifferential
  rw [hp0]
  have hchain := abelian_terminal_chain
    (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn μ) U δ
    (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) μ) (sin (θ t0 : ℂ)) (w : ℂ) v
      hU hR hs (by simpa only [mul_comm] using hv)
  rw [← mul_div_assoc,mul_comm (w : ℂ)]
  exact hchain

end NLS.KdV
