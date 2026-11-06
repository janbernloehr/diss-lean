import NLS.MKdV.MiuraIndependentPhaseActionCircle

/-! # Actual independent Abelian phase calculus under the physical actions

The independent normalized differential is invariant along complete
physical action flows. The literal full phase on a finite-gap orbit has
its actual derivative at every time with interior contributing sheets.
No canonical rotation constant, terminal continuation or final factorization is
claimed by these derivative identities.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.KdV NLS.MKdV NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_Abelian_differential_complete_action_invariance
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let q := miuraNativeHillActionCurve s hs a j t
    let r := realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val)
      (miuraNativeH1Profile_real s hs a)
    hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn =
      hillAbelianSelectedGlobalPsi r.val r.property.1 r.property.2 n hn :=
  miuraNativeAbelianPsi_actionFlow s hs a j n hn t

theorem independent_full_Abelian_phase_finite_gap_derivative
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
              (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega))) t :=
  hasDerivAt_miuraNativeFullAbelianPhase_actionFlow_finiteGap_interior s hs a j hj n hn F hnF t hclosed hR

theorem independent_full_Abelian_phase_original_action_circle
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
          sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (b,b)) z)) t :=
  hasDerivAt_miuraNativeFullAbelianPhase_actionFlow_circle s hs a j hj n hn F hnF t hclosed hR

end NLS.Articles.MKdVNLSHierarchies
