import NLS.Articles.KdVPseudomeasures.PeriodicSourceCircles

/-! Appendix C.3 regularity for the ENTIRE actual physical spectral range,
including sums of complex root spaces and all associated-vector directions.
The stronger representative is the identical original distribution. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Every physical spectral vector has the source's two-order improved
endpoint regularity, retaining the entire original complex distribution. -/
theorem sourcePeriodicSpectralVector_regular (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (c : ℂ) (rho : ℝ) (hrho : 0 < rho)
    (hc : sphere c rho ⊆ singularHillResolventSet (sourceComplexHminusOne r hr q))
    (F : CircleL2)
    (hF : F ∈ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q) c rho).range) :
    ∃ u : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤,
      u.val = (singularHillL2BaseInclusion F).val := by
  have ht : 1 < ((-r+2)-(-1))*(2:ℝ≥0∞).toReal := by
    norm_num
    linarith [hr.2]
  let L : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤ →L[ℂ]
      FourierLebesgueSpace (2:ℝ) (-1) 2 := endpointLowerInclusion (-r+2) (-1) (p := 2) (by norm_num) ht
  obtain ⟨a,ha⟩ := singularHillResolventSet_nonempty (sourceComplexHminusOne r hr q)
  have hrange : (singularHillRieszProjection (sourceComplexHminusOne r hr q) c rho).range ≤ L.range := by
    rw [singularHillRieszProjection_range_eq_roots_complex _ c rho hrho hc a ha]
    apply iSup_le
    intro z x hx
    obtain ⟨u,hu⟩ := sourceHillRootSpaceTop_regular r hr q z.val x hx
    refine ⟨u,?_⟩
    apply Subtype.ext
    change (L u).val = x.val
    rw [show (L u).val = u.val from endpointLowerInclusion_val _ _ _ _ _,hu]
  have hm : singularHillL2BaseInclusion F ∈
      (singularHillRieszProjection (sourceComplexHminusOne r hr q) c rho).range := by
    rw [← singularHillL2RieszProjection_range_base _ c rho hrho hc]
    exact ⟨F,hF,rfl⟩
  obtain ⟨u,hu⟩ := hrange hm
  refine ⟨u,?_⟩
  exact (endpointLowerInclusion_val _ _ _ _ u).symm.trans (congrArg Subtype.val hu)

/-- Every original H1 representative of a physical spectral vector is the
SAME source F-ell^(s+2,infinity) distribution; neither basis direction needs
an extra regularity hypothesis. -/
theorem sourcePeriodicH1Vector_regular (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (c : ℂ) (rho : ℝ) (hrho : 0 < rho)
    (hc : sphere c rho ⊆ singularHillResolventSet (sourceComplexHminusOne r hr q))
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillL2DomainInclusion f ∈
      (singularHillL2RieszProjection (sourceComplexHminusOne r hr q) c rho).range) :
    ∃ u : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤, u.val = f.val := by
  obtain ⟨u,hu⟩ := sourcePeriodicSpectralVector_regular r hr q c rho hrho hc
    (singularHillL2DomainInclusion f) hf
  rw [singularHillL2BaseInclusion_domain,singularHillDomainInclusion_val] at hu
  exact ⟨u,hu⟩

end NLS.Articles.KdVPseudomeasures
