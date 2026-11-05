import NLS.KdV.HillCosineSourceSheet
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

/-- The constructed paths have individually convergent prescribed-sheet
integrals for EVERY continuous numerator, at the singular initial endpoint. -/
theorem originalCosineFrequencyPath_curveIntegrable_numerator (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)≠0)
    (N : ℂ → ℂ) (hN : Continuous N) :
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
    let R := fun z => sourceAngularRootSheet (by simp) w
      (z,P.dirichletSource (hillOriginalHminusSource q.val))
    CurveIntegrable (holomorphicOneForm (fun z => N z/R z)) γ ∧
      CurveIntegrable (holomorphicOneForm (fun z => N z/R z)) (γ.map continuous_neg) := by
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
  have hRn (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) : R (-γ.extend t)≠0 :=
    sourceAngularRootSheet_ne_zero (by simp) w hw _ (hsheet t ht).2.1
  have hrootn (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
      R (-γ.extend t)= -I*δ*Complex.sin (AffineMap.lineMap a b t)*D (E t) := by
    dsimp only [R]
    rw [P.sourcePhase_prescribedRoot_neg _ hq]
    exact (hsheet t ht).2.2
  constructor
  · exact curveIntegrable_of_quadratic_cosine_resolution γ hγ a b τ δ P.miura.energyShift N D R
      hquad (fun t ht => (hsheet t ht).2.2) hz hD hR
      (hN.comp γ.continuous_extend).continuousOn hDc
  · have hγn : ContDiffOn ℝ 1 (γ.map continuous_neg).extend (Icc 0 1) :=
      contDiff_neg.comp_contDiffOn hγ
    exact curveIntegrable_of_quadratic_cosine_resolution (γ.map continuous_neg) hγn a b τ δ
      P.miura.energyShift N D R (fun t ht => by change (-γ.extend t)^2-_= _;rw [neg_sq];exact hquad t ht)
      hrootn (fun t ht => neg_ne_zero.mpr (hz t ht)) hD hRn
      (hN.comp γ.continuous_extend.neg).continuousOn hDc

/-- Both ACTUAL ordinary-source psi integrals along the constructed
positive and negative paths converge individually, with no integrability
hypothesis and no off-index restriction on the numerator. -/
theorem originalCosineFrequencyPath_source_curveIntegrable (n : ℤ) (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)≠0) :
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
    let f := fun z => sourceAngularIntegrand n P.family.roots (sourceAngularRootSheet (by simp) w)
      (z,P.dirichletSource (hillOriginalHminusSource q.val))
    CurveIntegrable (holomorphicOneForm f) γ ∧ CurveIntegrable (holomorphicOneForm f) (γ.map continuous_neg) := by
  let ψ : CoeffPair 2 := P.dirichletSource (hillOriginalHminusSource q.val)
  let a : Coeff 2 := P.family.roots n ψ
  let N : ℂ → ℂ := fun z => sourcePsiCandidate n (z,a)
  have hN : Continuous N := (differentiable_sourcePsiCandidate (by simp) (by norm_num) n a).continuous
  have h := P.originalCosineFrequencyPath_curveIntegrable_numerator q hq hreal houtside c hshift
    k hgap hw N hN
  dsimp only [sourceAngularIntegrand]
  exact h

end NLS.KdV.HillHminusPsiChart
