import NLS.KdV.HillCosineSourceBeta
import NLS.KdV.HillHminusPhysicalPhasePaths

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)

/-- The ORIGINAL scalar terminal value is the actual integral on the
quadratic image of its actual source-endpoint-labelled frequency path. -/
theorem originalCosineFrequencyPath_physical_integral (n k : ℕ+) (hkn : k≠n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)≠0) :
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
    let f := fun E => hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
      prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q.val)) w E
    (∫ᶜ E in quadraticEnergyPath P.miura.energyShift γ, holomorphicOneForm f E)=
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos k k.pos := by
  dsimp only
  let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap
  let Γ := hillPhysicalCosineEnergyPath q.val q.property.1 q.property.2 k (realCosineArcAnchor θ) θ
  let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
  let f := fun E => hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
    prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q.val))
      (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)) E
  have hpaths : ((quadraticEnergyPath P.miura.energyShift γ).extend:ℝ → ℂ)=Γ.extend :=
    funext (P.originalCosineFrequencyPath_squared q hq hreal houtside c hshift k hgap)
  have hcurve : curveIntegralFun (holomorphicOneForm f) (quadraticEnergyPath P.miura.energyShift γ)=
      curveIntegralFun (holomorphicOneForm f) Γ := by
    funext t
    simp only [curveIntegralFun_def']
    rw [hpaths]
  change (∫ᶜ E in quadraticEnergyPath P.miura.energyShift γ, holomorphicOneForm f E)=_
  rw [curveIntegral_def',hcurve,← curveIntegral_def']
  exact (hillRegularAbelianCorrection_eq_prescribed_cosine_path q.val q.property.1 q.property.2
    n k n.pos k.pos (fun he => hkn (Subtype.ext he)) hgap hw).2

include hq hreal houtside hshift

/-- At EVERY regular off-index terminal, the ORIGINAL normalized scalar
cosine correction is exactly the PAIRED ordinary-source beta value.
No replacement phase, chosen integral hypothesis, supplied primitive,
source-domain condition or integrability assumption remains. -/
theorem originalRegularCorrection_eq_source_beta_pair
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n k : ℕ+) (hkn : k≠n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)≠0) :
    hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos k k.pos=
      sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((k:ℕ):ℤ) P.family.roots
        (P.dirichletSource (hillOriginalHminusSource q.val))+
      sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((k:ℕ):ℤ)) P.family.roots
        (P.dirichletSource (hillOriginalHminusSource q.val)) := by
  let a := hillOriginalHminusSource q.val
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
  let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
  have hrealA := hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2)
  obtain ⟨U,_,haU,_,hpull⟩ := P.exists_common_prescribed_path_pullback a hq hrealA
  have hInt := P.originalCosineFrequencyPath_source_curveIntegrable q hq hreal houtside c hshift
    ((n:ℕ):ℤ) k hgap hw
  have h := hpull a haU n w _ _ γ
    (P.contDiffOn_originalCosineFrequencyPath q hq hreal houtside c hshift k hgap) hInt.1 hInt.2
  have he : (fun E => P.prescribedDifferential n w (E,a))=
      (fun E => hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
        prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q.val)) w E) := by
    funext E
    exact P.prescribedDifferential_eq_original q hq hreal houtside c hshift n w E
  rw [he] at h
  exact (P.originalCosineFrequencyPath_physical_integral q hq hreal houtside c hshift n k hkn hgap hw).symm.trans
    (h.2.trans (P.originalCosineFrequencyPath_integral_eq_beta_pair q hq hreal houtside c hshift H n k hkn hgap hw))

end NLS.KdV.HillHminusPsiChart
