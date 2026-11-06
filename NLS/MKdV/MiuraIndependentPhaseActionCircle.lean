import NLS.MKdV.MiuraIndependentPhaseDerivative
import NLS.MKdV.MiuraAbelianActionCircleContraction

/-! # The actual full independent phase generator as an Abelian action period

At finite-gap interior divisors the original complete physical action
flow differentiates the independently constructed full phase to its
normalized frequency-circle period. The factor is positively i over pi.
The period's Kronecker value and terminal continuation remain separate.
-/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem hasDerivAt_miuraNativeFullAbelianPhase_actionFlow_circle
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F) (t : ℝ)
    (hclosed : ∀ k, k ∉ F → hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1 (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) = 0)
    (hR : ∀ k ∈ F,hillDirichletSheetRoot
      (SpectralWeight.one.toCoeff (miuraNativeHillActionCurve s hs a j t).val)
      (hillDirichletEnergy (miuraNativeHillActionCurve s hs a j t).val
        (miuraNativeHillActionCurve s hs a j t).property.1
        (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) (by omega)) ≠ 0) :
    let b := hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a j t).val
    let hb := miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a j t)
    let q := realSobolevMiuraHillPotential b hb
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    let φ : realDiagonalSourceLocus 2 := ⟨(realDiagonalH1Source b hb).val,⟨(realDiagonalH1Source b hb).property,rfl⟩⟩
    let C := (sourceDiagonalLaurentAtlas (by simp) (by norm_num)).localChart φ
    HasDerivAt (fun r => miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r))
      ((I/(Real.pi : ℂ))*miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)*
        (∮ z in C(C.cauchy.discs.center j,C.contourRadius j),z*ψ (z^2)/
          sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (b,b)) z)) t := by
  let b := hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a j t).val
  let hb := miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a j t)
  let q := realSobolevMiuraHillPotential b hb
  let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
  let φ : realDiagonalSourceLocus 2 := ⟨(realDiagonalH1Source b hb).val,⟨(realDiagonalH1Source b hb).property,rfl⟩⟩
  let C := (sourceDiagonalLaurentAtlas (by simp) (by norm_num)).localChart φ
  have hφ : φ.val ∈ ball φ.val C.radius := mem_ball_self C.radius_pos
  have hcircle : sphere (C.cauchy.discs.center j) (C.contourRadius j) ⊆
      sourceCanonicalRootDomain (by simp) (by norm_num) φ.val := by
    intro z hz
    exact C.cauchy.intermediate_circle_root j φ.val (C.source_subset hφ) _
      (C.contourRadius_bounds j).1 (C.contourRadius_bounds j).2 z hz
  have hsheet : ∀ k ∈ F,hillDirichletSheetRoot (sobolevMiuraHillPotential b) (hillDirichletEnergies q k) ≠ 0 := by
    intro k hk
    have h : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) (hillDirichletEnergies q k) ≠ 0 := hR k hk
    simpa only [q,realSobolevMiuraHillPotential_toCoeff] using h
  have hc := miuraSupportedAbelian_original_action_circle_contraction b hb n hn F hnF hclosed hsheet
    (C.cauchy.discs.center j) (C.contourRadius j) (C.contourRadius_pos j).le hcircle
  have hv (k : ℕ) :
      deriv (fun r => miuraNativeDirichletEnergy s hs (k+1) (by omega) (miuraNativeRealActionFlow s a j r)) t =
        -(2/(Real.pi : ℂ))*(∮ z in C(C.cauchy.discs.center j,C.contourRadius j),
          miuraDirichletTraceKernel b hb (k+1) (by omega) z) :=
    (hasDerivAt_miuraNativeDirichletEnergy_actionFlow_circle s hs a j hj (k+1) (by omega) t).deriv
  have hsum : (∑ k ∈ F,ψ (hillDirichletEnergies q k)*
      deriv (fun r => miuraNativeDirichletEnergy s hs (k+1) (by omega) (miuraNativeRealActionFlow s a j r)) t/
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) (hillDirichletEnergies q k)) =
      (1/(Real.pi : ℂ))*(∮ z in C(C.cauchy.discs.center j,C.contourRadius j),z*ψ (z^2)/
        sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (b,b)) z) := by
    have hq : SpectralWeight.one.toCoeff q.val = sobolevMiuraHillPotential b :=
      realSobolevMiuraHillPotential_toCoeff b hb
    simp only [hq]
    apply Eq.trans ?_ hc
    apply Finset.sum_congr rfl
    intro k _
    rw [hv]
  have hd := hasDerivAt_miuraNativeFullAbelianPhase_actionFlow_finiteGap_interior s hs a j hj n hn F hnF t hclosed hR
  apply hd.congr_deriv
  change I*miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)*
    (∑ k ∈ F,ψ (hillDirichletEnergies q k)*
      deriv (fun r => miuraNativeDirichletEnergy s hs (k+1) (by omega) (miuraNativeRealActionFlow s a j r)) t/
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) (hillDirichletEnergies q k)) = _
  rw [hsum]
  ring

end NLS.MKdV
