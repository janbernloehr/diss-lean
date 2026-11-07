import NLS.KdV.SingularHillRieszDomain
import NLS.KdV.SingularHillPhysicalL2

/-! The ACTUAL periodic Riesz projection on the FULL source-normalized
physical L2 Hilbert space. Its full original H-minus-one/H1 contour lift,
partial-operator domain and complex associated-vector range are preserved. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The source periodic physical L2 projection, from the SAME full native contour. -/
def singularHillL2RieszProjection (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    CircleL2 →L[ℂ] CircleL2 :=
  singularHillL2DomainInclusion.comp ((singularHillRieszToH1 q c r).comp singularHillL2BaseInclusion)

/-- Its full original base realization is EXACTLY the actual native Riesz projection. -/
theorem singularHillL2RieszProjection_base
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularHillResolventSet q) (F : CircleL2) :
    singularHillL2BaseInclusion (singularHillL2RieszProjection q c r F) =
      singularHillRieszProjection q c r (singularHillL2BaseInclusion F) := by
  change singularHillL2BaseInclusion (singularHillL2DomainInclusion
    (singularHillRieszToH1 q c r (singularHillL2BaseInclusion F))) = _
  rw [singularHillL2BaseInclusion_domain,← singularHillRieszToH1_inclusion q c r hr hc]

/-- Its restriction to ALL original H1 data is the ACTUAL full H1 domain projection. -/
theorem singularHillL2RieszProjection_domain
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillL2RieszProjection q c r (singularHillL2DomainInclusion f) =
      singularHillL2DomainInclusion (singularHillDomainRieszProjection q c r f) := by
  change singularHillL2DomainInclusion (singularHillRieszToH1 q c r
    (singularHillL2BaseInclusion (singularHillL2DomainInclusion f))) = _
  rw [singularHillL2BaseInclusion_domain]
  rfl

/-- The ACTUAL periodic projection is a bounded idempotent in the source L2 norm. -/
theorem isIdempotentElem_singularHillL2RieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) :
    IsIdempotentElem (singularHillL2RieszProjection q c r) := by
  apply ContinuousLinearMap.ext
  intro F
  apply singularHillL2BaseInclusion_injective
  change singularHillL2BaseInclusion (singularHillL2RieszProjection q c r
    (singularHillL2RieszProjection q c r F)) =
      singularHillL2BaseInclusion (singularHillL2RieszProjection q c r F)
  rw [singularHillL2RieszProjection_base q c r hr.le hc,
    singularHillL2RieszProjection_base q c r hr.le hc]
  exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 =>
    T (singularHillL2BaseInclusion F)) (isIdempotentElem_singularHillRieszProjection q c r hr hc)

/-- The faithful physical-base image of its FULL L2 range is EXACTLY the
FULL native algebraic spectral range, retaining ALL complex associated vectors. -/
theorem singularHillL2RieszProjection_range_base
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) :
    Submodule.map singularHillL2BaseInclusion.toLinearMap (singularHillL2RieszProjection q c r).range =
      (singularHillRieszProjection q c r).range := by
  apply le_antisymm
  · rintro x ⟨y,⟨F,rfl⟩,rfl⟩
    change singularHillL2BaseInclusion (singularHillL2RieszProjection q c r F) ∈
      (singularHillRieszProjection q c r).range
    rw [singularHillL2RieszProjection_base q c r hr.le hc]
    exact ⟨singularHillL2BaseInclusion F,rfl⟩
  · rintro x ⟨F,rfl⟩
    let g := singularHillRieszToH1 q c r F
    have hg : singularHillL2BaseInclusion (singularHillL2DomainInclusion g) =
        singularHillRieszProjection q c r F := by
      rw [singularHillL2BaseInclusion_domain]
      exact (singularHillRieszToH1_inclusion q c r hr.le hc F).symm
    have hfixed : singularHillL2RieszProjection q c r (singularHillL2DomainInclusion g) =
        singularHillL2DomainInclusion g := by
      apply singularHillL2BaseInclusion_injective
      rw [singularHillL2RieszProjection_base q c r hr.le hc,hg]
      exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 => T F)
        (isIdempotentElem_singularHillRieszProjection q c r hr hc)
    exact ⟨singularHillL2DomainInclusion g,⟨singularHillL2DomainInclusion g,hfixed⟩,hg⟩

/-- The actual physical and native spectral ranges are linearly equivalent,
including all generalized eigenvectors for complex potentials. -/
def singularHillL2RieszRangeEquiv
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) :
    (singularHillL2RieszProjection q c r).range ≃ₗ[ℂ]
      (singularHillRieszProjection q c r).range :=
  (Submodule.equivMapOfInjective singularHillL2BaseInclusion.toLinearMap
    singularHillL2BaseInclusion_injective _).trans
      (LinearEquiv.ofEq _ _ (singularHillL2RieszProjection_range_base q c r hr hc))

/-- The actual source-normalized L2 projection has finite-dimensional range. -/
theorem finiteDimensional_singularHillL2RieszProjection_range
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) :
    FiniteDimensional ℂ (singularHillL2RieszProjection q c r).range := by
  let := finiteDimensional_singularHillRieszProjection_range q c r hr hc
  exact FiniteDimensional.of_injective
    (singularHillL2RieszRangeEquiv q c r hr hc).toLinearMap
    (singularHillL2RieszRangeEquiv q c r hr hc).injective

/-- Algebraic rank is unchanged by the faithful physical realization. -/
theorem finrank_singularHillL2RieszProjection_range
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) :
    Module.finrank ℂ (singularHillL2RieszProjection q c r).range =
      Module.finrank ℂ (singularHillRieszProjection q c r).range :=
  (singularHillL2RieszRangeEquiv q c r hr hc).finrank_eq

/-- The physical projection realizes the entire sum of enclosed original
complex algebraic root spaces. No reality or semisimplicity assumption is used. -/
theorem singularHillL2RieszProjection_range_roots
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) :
    Submodule.map singularHillL2BaseInclusion.toLinearMap
      (singularHillL2RieszProjection q c r).range =
        ⨆ z : ball c r, singularHillRootSpaceTop q z.val := by
  obtain ⟨a,ha⟩ := singularHillResolventSet_nonempty q
  rw [singularHillL2RieszProjection_range_base q c r hr hc,
    singularHillRieszProjection_range_eq_roots_complex q c r hr hc a ha]

end NLS.KdV
