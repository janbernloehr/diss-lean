import NLS.MKdV.MiuraIndependentPhaseActionCircle
import NLS.MKdV.MiuraIndependentAbelianActionPeriods

/-! # Actual Kronecker generators of the full independent finite-gap phase

The original exp(+i*sum) convention has positive generators under the
physical actions. Conjugation of this independently spectral phase will
supply the opposite source orientation. Terminal continuation is separate.
-/
noncomputable section
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem hasDerivAt_miuraNativeFullAbelianPhase_actionFlow_finiteGap_generator
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F) (t : ℝ)
    (hclosed : ∀ k, k ∉ F → hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1 (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) = 0)
    (hR : ∀ k ∈ F,hillDirichletSheetRoot
      (SpectralWeight.one.toCoeff (miuraNativeHillActionCurve s hs a j t).val)
      (hillDirichletEnergy (miuraNativeHillActionCurve s hs a j t).val
        (miuraNativeHillActionCurve s hs a j t).property.1
        (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) (by omega)) ≠ 0) :
    HasDerivAt (fun r => miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r))
      (I*(if j = n then 1 else 0)*miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)) t := by
  let b := hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a j t).val
  let hb := miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a j t)
  let q := realSobolevMiuraHillPotential b hb
  let φ : realDiagonalSourceLocus 2 := ⟨(realDiagonalH1Source b hb).val,⟨(realDiagonalH1Source b hb).property,rfl⟩⟩
  let C := (sourceDiagonalLaurentAtlas (by simp) (by norm_num)).localChart φ
  have hp := miuraSelectedAbelianPsi_original_circle_period b hb C.ambient C.cauchy
    (C.source_subset (mem_ball_self C.radius_pos)) j hj (C.contourRadius j) (C.contourRadius_bounds j) n hn
  have hd := hasDerivAt_miuraNativeFullAbelianPhase_actionFlow_circle s hs a j hj n hn F hnF t hclosed hR
  apply hd.congr_deriv
  change (I/(Real.pi:ℂ))*miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)*
    (∮ z in C(C.cauchy.discs.center j,C.contourRadius j),z*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn (z^2)/
      sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (b,b)) z) = _
  rw [hp]
  field_simp

end NLS.MKdV
