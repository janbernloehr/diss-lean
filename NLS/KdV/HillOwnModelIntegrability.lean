import NLS.KdV.HillCosineSourceSheet
import NLS.ZakharovShabat.SourceAngularEtaPrescribedSheet
import NLS.KdV.HillHminusDirichletSourceBetaSeries
import NLS.ComplexAnalysis.QuadraticCosinePathIntegrability

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

/-- A numerator continuous on the ACTUAL selected gap suffices for
convergence along the constructed positive frequency path. -/
theorem originalCosineFrequencyPath_curveIntegrable_gap_numerator (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)≠0)
    (N : ℂ → ℂ) (hN : ContinuousOn N (sourcePeriodicSegment (by simp) (by norm_num)
      (P.dirichletSource (hillOriginalHminusSource q.val)) (k:ℕ))) :
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
    let R := fun z => sourceAngularRootSheet (by simp) w
      (z,P.dirichletSource (hillOriginalHminusSource q.val))
    CurveIntegrable (holomorphicOneForm (fun z => N z/R z)) γ := by
  dsimp only
  let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap
  let a : ℂ := realCosineArcAnchor θ
  let b : ℂ := θ
  let τ : ℂ := hillRealGapCenter q.val q.property.1 q.property.2 k
  let δ : ℂ := hillRealGapHalfLength q.val q.property.1 q.property.2 k
  let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
  let E : ℝ → ℂ := fun t => cosineGapPoint τ δ (AffineMap.lineMap a b t)
  let D := hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
  let R := fun z => sourceAngularRootSheet (by simp) w
    (z,P.dirichletSource (hillOriginalHminusSource q.val))
  have hγ := P.contDiffOn_originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
  have hquad := P.originalCosineFrequencyPath_squared_affine q hq hreal houtside c hshift k hgap
  have hsheet := P.originalCosineFrequencyPath_sheet_resolution q hq hreal houtside c hshift k hgap hw
  have hline (t : ℝ) : (AffineMap.lineMap a b t).im=0 := by
    simp [a,b,AffineMap.lineMap_apply_module',Complex.real_smul]
  have hfilled (t : ℝ) : E t∈hillGapFilledDomain q.val q.property.1 q.property.2 k := by
    have he : AffineMap.lineMap a b t=((AffineMap.lineMap a b t).re:ℂ) :=
      Complex.ext rfl (by simpa using hline t)
    dsimp only [E]
    rw [he]
    exact hillCosineGapPoint_mem_filledDomain q.val q.property.1 q.property.2 k k.pos _
  have hD (t : ℝ) (_ : t∈Icc (0:ℝ) 1) : D (E t)≠0 :=
    hillDeflatedEnergyCanonicalRoot_ne_zero q.val q.property.1 q.property.2 k k.pos _ (hfilled t)
  have hEc : Continuous E := by
    change Continuous (fun t : ℝ => τ+δ*Complex.cos (AffineMap.lineMap a b t))
    fun_prop
  have hDc : ContinuousOn (fun t : ℝ => D (E t)) (Icc 0 1) := by
    intro t _
    exact ((analyticOnNhd_hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k _
      (hfilled t)).continuousAt.comp hEc.continuousAt).continuousWithinAt
  have hz (t : ℝ) (_ : t∈Icc (0:ℝ) 1) : γ.extend t≠0 := by
    intro he
    have hp := P.originalCosineFrequencyPath_re_pos q hq hreal houtside c hshift k hgap t
    change 0<(γ.extend t).re at hp
    rw [he,zero_re] at hp
    exact lt_irrefl 0 hp
  have hR (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) : R (γ.extend t)≠0 :=
    sourceAngularRootSheet_ne_zero (by simp) w hw _ (hsheet t ht).1
  exact curveIntegrable_of_quadratic_cosine_resolution γ hγ a b τ δ P.miura.energyShift N D R
    hquad (fun t ht => (hsheet t ht).2.2) hz hD hR
    (hN.comp γ.continuous_extend.continuousOn
      (fun t _ => P.originalCosineFrequencyPath_mem_sourceGap q hq hreal houtside c hshift k hgap t)) hDc

/-- The own eta MODEL integral on the CONSTRUCTED original frequency
path converges. The omitted product is only required analytic on its
actual omitted domain, and no global continuity across other cuts is used. -/
theorem originalCosineFrequencyPath_eta_model_curveIntegrable
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)≠0) :
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
    let ψ := P.dirichletSource (hillOriginalHminusSource q.val)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
    CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand
      (by simp) (by norm_num) ((n:ℕ):ℤ) ψ w)) γ := by
  let ψ := P.dirichletSource (hillOriginalHminusSource q.val)
  have hψ : ψ∈P.family.domain := (P.mem_sourceBetaDomain_of_real _ hq
    (hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2))).2
  have hd := H.angular_endpoint_data ψ hψ ((n:ℕ):ℤ)
  let N : ℂ → ℂ := fun z => -(2*sourceStandardRootOmittedProduct (by simp) (by norm_num) ((n:ℕ):ℤ) ψ z)
  have hN : ContinuousOn N (sourcePeriodicSegment (by simp) (by norm_num) ψ ((n:ℕ):ℤ)) :=
    (continuousOn_const.mul (hd.analytic_omitted.continuousOn.mono hd.gap_avoids_other_gaps)).neg
  exact P.originalCosineFrequencyPath_curveIntegrable_gap_numerator q hq hreal houtside c hshift n hgap hw N hN

end NLS.KdV.HillHminusPsiChart
