import NLS.KdV.HillCosineSourceGap
import NLS.KdV.HillSelectedCosineArc

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)

theorem originalCosineFrequencyPath_squared_affine (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0) :
    let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap
    ∀ t∈Icc (0:ℝ) 1,
      ((P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap).extend t)^2-P.miura.energyShift=
        cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
          (hillRealGapHalfLength q.val q.property.1 q.property.2 k)
          (AffineMap.lineMap (realCosineArcAnchor θ:ℂ) (θ:ℂ) t) := by
  dsimp only
  intro t ht
  have h := P.originalCosineFrequencyPath_squared q hq hreal houtside c hshift k hgap t
  change _=cosineGapPoint _ _ ((Path.segment _ _).extend t) at h
  rw [Path.extend_apply (Path.segment _ _) ht] at h
  exact h

/-- BOTH signed actual frequency paths stay on the SAME prescribed
original physical sheet in the interior. Its exact cosine cancellation
retains the physical Dirichlet sign at both signed terminals. -/
theorem originalCosineFrequencyPath_sheet_resolution (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)≠0) :
    let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
    ∀ t∈Ioo (0:ℝ) 1,
      (γ.extend t,P.dirichletSource (hillOriginalHminusSource q.val))∈sourceAngularRootSheetDomain (by simp) w ∧
      (-γ.extend t,P.dirichletSource (hillOriginalHminusSource q.val))∈sourceAngularRootSheetDomain (by simp) w ∧
      sourceAngularRootSheet (by simp) w (γ.extend t,P.dirichletSource (hillOriginalHminusSource q.val))=
        -I*(hillRealGapHalfLength q.val q.property.1 q.property.2 k:ℂ)*
          Complex.sin (AffineMap.lineMap (realCosineArcAnchor θ:ℂ) (θ:ℂ) t)*
          hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k
            (cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
              (hillRealGapHalfLength q.val q.property.1 q.property.2 k)
              (AffineMap.lineMap (realCosineArcAnchor θ:ℂ) (θ:ℂ) t)) := by
  dsimp only
  let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
  obtain ⟨S,hS,hθS,hSr,hSin,hline⟩ := exists_hillDirichlet_selected_regular_arc
    q.val q.property.1 q.property.2 k k.pos hgap hw
  have hspec := hillDirichletSelectedRealAngle_spec q.val q.property.1 q.property.2 k k.pos hgap
  have hcancel := hillPrescribedDirichletRoot_cosine_eq q.val q.property.1 q.property.2 k k.pos hgap
    S hS hSr hSin (θ:ℂ) hθS hspec.2.1 hspec.2.2 hw
  have hwr : w.im=0 := by
    dsimp only [w]
    rw [hillDirichletSheetRoot_at_dirichlet_eq_norming q.val q.property.1 q.property.2 k k.pos]
    exact ofReal_im _
  intro t ht
  let z := (P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap).extend t
  let e := AffineMap.lineMap (realCosineArcAnchor θ:ℂ) (θ:ℂ) t
  have heS : e∈S := hline t ht
  have her : e=(e.re:ℂ) := Complex.ext rfl (by simpa using hSr e heS)
  have hdom := hillPrescribedRoot_cosine_domain q.val q.property.1 q.property.2 k k.pos hgap
    w hw hwr e.re (by rw [← her];exact hSin e heS)
  rw [← her] at hdom
  have hquad := P.originalCosineFrequencyPath_squared_affine q hq hreal houtside c hshift k hgap t
    (Ioo_subset_Icc_self ht)
  have hpositive : (z,P.dirichletSource (hillOriginalHminusSource q.val))∈sourceAngularRootSheetDomain (by simp) w := by
    apply (P.prescribedRoot_squared_frequency_domain_iff _ hq w z).mp
    rw [hquad]
    change hillHminusRadicand (hillOriginalHminusSource q.val) _/w^2∈slitPlane
    rw [hillHminusRadicand_original_source_agreement q.val q.property.1]
    exact hdom
  have hnegative : (-z,P.dirichletSource (hillOriginalHminusSource q.val))∈sourceAngularRootSheetDomain (by simp) w := by
    apply (P.prescribedRoot_squared_frequency_domain_iff _ hq w (-z)).mp
    rw [neg_sq]
    exact (P.prescribedRoot_squared_frequency_domain_iff _ hq w z).mpr hpositive
  refine ⟨hpositive,hnegative,?_⟩
  rw [← P.prescribedRoot_squared_frequency_eq_sourcePhase _ hq w z,hquad,
    hillHminusPrescribedRoot_original_source_agreement q.val q.property.1]
  exact hcancel e heS

end NLS.KdV.HillHminusPsiChart
