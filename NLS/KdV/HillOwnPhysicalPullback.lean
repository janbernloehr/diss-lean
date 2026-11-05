import NLS.KdV.HillOwnCosineEnergy
import NLS.KdV.HillOwnNegativeBeta
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

theorem originalOwnFrequencyPath_physical_integral (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)≠0) :
    let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 n n.pos hgap
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
    let f := fun E => hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
      prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q.val)) w E
    (∫ᶜ E in quadraticEnergyPath P.miura.energyShift γ, holomorphicOneForm f E)=
      hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n n.pos n (θ:ℂ)+
        (if θ<0 then 2*(Real.pi:ℂ) else 0) := by
  dsimp only
  let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 n n.pos hgap
  let Γ := hillPhysicalCosineEnergyPath q.val q.property.1 q.property.2 n (realCosineArcAnchor θ) θ
  let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
  let f := fun E => hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
    prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q.val))
      (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)) E
  have hpaths : ((quadraticEnergyPath P.miura.energyShift γ).extend:ℝ → ℂ)=Γ.extend :=
    funext (P.originalCosineFrequencyPath_squared q hq hreal houtside c hshift n hgap)
  have hcurve : curveIntegralFun (holomorphicOneForm f) (quadraticEnergyPath P.miura.energyShift γ)=
      curveIntegralFun (holomorphicOneForm f) Γ := by
    funext t
    simp only [curveIntegralFun_def']
    rw [hpaths]
  change (∫ᶜ E in quadraticEnergyPath P.miura.energyShift γ, holomorphicOneForm f E)=_
  rw [curveIntegral_def',hcurve,← curveIntegral_def']
  exact (hillOwnCosineEnergyPath_integral q.val q.property.1 q.property.2 n n.pos hgap hw).2

/-- The ORIGINAL own cosine primitive is the actual own source integral
plus the negative-selected beta, with the NONZERO negative-angle
anchor period retained explicitly. No primitive or integral hypothesis
is supplied. -/
theorem originalOwnCosinePrimitive_source_decomposition
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)≠0) :
    let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 n n.pos hgap
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
    let ψ := P.dirichletSource (hillOriginalHminusSource q.val)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
    hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n n.pos n (θ:ℂ)+
      (if θ<0 then 2*(Real.pi:ℂ) else 0)=
      sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w) ψ γ+
        sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((n:ℕ):ℤ)) P.family.roots ψ := by
  dsimp only
  let a := hillOriginalHminusSource q.val
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
  let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
  have hrealA := hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2)
  obtain ⟨U,_,haU,_,hpull⟩ := P.exists_common_prescribed_path_pullback a hq hrealA
  have hInt := P.originalCosineFrequencyPath_source_curveIntegrable q hq hreal houtside c hshift
    ((n:ℕ):ℤ) n hgap hw
  have h := hpull a haU n w _ _ γ
    (P.contDiffOn_originalCosineFrequencyPath q hq hreal houtside c hshift n hgap) hInt.1 hInt.2
  have he : (fun E => P.prescribedDifferential n w (E,a))=
      (fun E => hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
        prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q.val)) w E) := by
    funext E
    exact P.prescribedDifferential_eq_original q hq hreal houtside c hshift n w E
  rw [he] at h
  have hn := P.originalCosineFrequencyPath_negative_integral_eq_beta q hq hreal houtside c hshift H n n hgap hw
  rw [hn] at h
  exact (P.originalOwnFrequencyPath_physical_integral q hq hreal houtside c hshift n hgap hw).symm.trans h.2

end NLS.KdV.HillHminusPsiChart
