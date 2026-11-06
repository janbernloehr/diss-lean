import NLS.MKdV.MiuraActionFlowHillCurve
import NLS.MKdV.MiuraDirichletActionMotion
import NLS.KdV.HillIsospectralFinitePhaseDerivative

/-! # Actual independent phase derivatives along the complete physical action flows

The original Abelian phase is differentiated using its actual spectral
construction and the actual Dirichlet velocities. The finite-gap full
phase is included; contributing divisor points are assumed interior.
Evaluation of the resulting period and continuation through terminals
remain separate from these chain-rule identities.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.MKdV

theorem hasDerivAt_miuraFiniteAbelianPhase_actionFlow_interior
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F) (t : ℝ)
    (hR : ∀ k ∈ F,hillDirichletSheetRoot
      (SpectralWeight.one.toCoeff (miuraNativeHillActionCurve s hs a j t).val)
      (hillDirichletEnergy (miuraNativeHillActionCurve s hs a j t).val
        (miuraNativeHillActionCurve s hs a j t).property.1
        (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) (by omega)) ≠ 0) :
    let q := miuraNativeHillActionCurve s hs a j t
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    HasDerivAt (fun r => hillFiniteAbelianPhase (miuraNativeHillActionCurve s hs a j r) n hn F)
      (I*hillFiniteAbelianPhase q n hn F*
        ∑ k ∈ F,ψ (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega))*
          deriv (fun r => miuraNativeDirichletEnergy s hs (k+1) (by omega) (miuraNativeRealActionFlow s a j r)) t/
            hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
              (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega))) t := by
  apply hasDerivAt_hillFiniteAbelianPhase_isospectral_family (miuraNativeHillActionCurve s hs a j) t
    (continuous_miuraNativeHillActionCurve s hs a j).continuousAt
    (differentiableAt_miuraNativeHillActionCoefficients s hs a j hj t)
    (miuraNativeHillActionCurve_labels s hs a j t) n hn F hnF
  · intro k _
    have hd := hasDerivAt_miuraNativeDirichletEnergy_actionFlow_circle s hs a j hj (k+1) (by omega) t
    exact hd.differentiableAt.hasDerivAt
  · exact hR

/-- The literal full phase on a finite-gap physical orbit has the same
actual derivative. Only contributing open divisors require interior sheets. -/
theorem hasDerivAt_miuraNativeFullAbelianPhase_actionFlow_finiteGap_interior
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F) (t : ℝ)
    (hclosed : ∀ k, k ∉ F → hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1 (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) = 0)
    (hR : ∀ k ∈ F,hillDirichletSheetRoot
      (SpectralWeight.one.toCoeff (miuraNativeHillActionCurve s hs a j t).val)
      (hillDirichletEnergy (miuraNativeHillActionCurve s hs a j t).val
        (miuraNativeHillActionCurve s hs a j t).property.1
        (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) (by omega)) ≠ 0) :
    let q := miuraNativeHillActionCurve s hs a j t
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    HasDerivAt (fun r => miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r))
      (I*miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)*
        ∑ k ∈ F,ψ (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega))*
          deriv (fun r => miuraNativeDirichletEnergy s hs (k+1) (by omega) (miuraNativeRealActionFlow s a j r)) t/
            hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
              (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega))) t := by
  have hd := hasDerivAt_miuraFiniteAbelianPhase_actionFlow_interior s hs a j hj n hn F hnF t hR
  have he : (fun r => miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r)) =ᶠ[𝓝 t]
      (fun r => hillFiniteAbelianPhase (miuraNativeHillActionCurve s hs a j r) n hn F) := by
    apply Filter.Eventually.of_forall
    intro r
    apply hillFullAbelianPhase_eq_finite_of_closed_complement
    intro k hk
    exact (congrFun (hillRealGapHalfLength_eq_of_labels (miuraNativeHillActionCurve s hs a j r)
      (miuraNativeHillActionCurve s hs a j t) (miuraNativeHillActionCurve_labels s hs a j t r)) (k+1)).trans
        (hclosed k hk)
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  rw [Filter.EventuallyEq.eq_of_nhds he]

end NLS.MKdV
