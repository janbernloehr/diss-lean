import NLS.KdV.HillPhysicalCosinePath
import NLS.ComplexAnalysis.RealPositiveEnergyLift

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem contDiffOn_hillPhysicalCosineEnergyPath (k : ℕ) (a θ : ℝ) :
    ContDiffOn ℝ 1 (hillPhysicalCosineEnergyPath q hq hr k a θ).extend (Icc 0 1) := by
  have hT : ContDiff ℝ 1
      (cosineGapPoint (hillRealGapCenter q hq hr k:ℂ) (hillRealGapHalfLength q hq hr k:ℂ)) := by
    unfold cosineGapPoint
    exact contDiff_const.add (contDiff_const.mul (Complex.contDiff_cos.restrict_scalars ℝ))
  exact hT.comp_contDiffOn (contDiffOn_segment_extend (a:ℂ) (θ:ℂ))

theorem hillPhysicalCosineEnergyPath_mem_gap (k : ℕ) (hk : 1≤k) (a θ : ℝ)
    (t : ℝ) :
    (hillPhysicalCosineEnergyPath q hq hr k a θ).extend t∈
      segment ℝ (hillRealLabels q hq hr (2*k-1):ℂ) (hillRealLabels q hq hr (2*k):ℂ) := by
  let e := (Path.segment (a:ℂ) (θ:ℂ)).extend t
  have he : e.im=0 := by
    change (AffineMap.lineMap (a:ℂ) (θ:ℂ) (Set.projIcc 0 1 zero_le_one t:ℝ)).im=0
    simp [AffineMap.lineMap_apply_module',Complex.real_smul]
  have her : e=(e.re:ℂ) := Complex.ext rfl (by simpa using he)
  change cosineGapPoint _ _ e∈_
  rw [her]
  exact hillCosineGapPoint_mem_real_gap q hq hr k hk e.re

theorem hillPhysicalCosineEnergyPath_real (k : ℕ) (hk : 1≤k) (a θ : ℝ) (t : ℝ) :
    ((hillPhysicalCosineEnergyPath q hq hr k a θ).extend t).im=0 :=
  im_eq_zero_of_mem_real_segment _ _ _ (hillPhysicalCosineEnergyPath_mem_gap q hq hr k hk a θ t)

theorem hillPhysicalCosineEnergyPath_shift_pos (k : ℕ) (hk : 1≤k) (a θ c : ℝ)
    (hleft : 0<hillRealLabels q hq hr (2*k-1)+c) (t : ℝ) :
    0<((hillPhysicalCosineEnergyPath q hq hr k a θ).extend t).re+c := by
  have hbounds := re_mem_Icc_of_mem_real_segment _ _
    (monotone_hillRealLabels q hq hr (by omega : 2*k-1≤2*k)) _
    (hillPhysicalCosineEnergyPath_mem_gap q hq hr k hk a θ t)
  linarith [hbounds.1]

/-- The actual positive real frequency lift of the ORIGINAL signed
cosine energy path; no choice of a replacement contour is supplied. -/
def hillPhysicalCosineFrequencyPath (k : ℕ) (a θ c : ℝ) :=
  positiveRealEnergyLiftPath c (hillPhysicalCosineEnergyPath q hq hr k a θ)

theorem contDiffOn_hillPhysicalCosineFrequencyPath (k : ℕ) (hk : 1≤k) (a θ c : ℝ)
    (hleft : 0<hillRealLabels q hq hr (2*k-1)+c) :
    ContDiffOn ℝ 1 (hillPhysicalCosineFrequencyPath q hq hr k a θ c).extend (Icc 0 1) :=
  contDiffOn_positiveRealEnergyLiftPath c _
    (contDiffOn_hillPhysicalCosineEnergyPath q hq hr k a θ)
    (fun t _ => hillPhysicalCosineEnergyPath_shift_pos q hq hr k hk a θ c hleft t)

/-- Squaring the actual frequency lift recovers the ORIGINAL energy
path pointwise, including its singular initial endpoint. -/
theorem hillPhysicalCosineFrequencyPath_squared (k : ℕ) (hk : 1≤k) (a θ c : ℝ)
    (hleft : 0<hillRealLabels q hq hr (2*k-1)+c) (t : ℝ) :
    ((hillPhysicalCosineFrequencyPath q hq hr k a θ c).extend t)^2-(c:ℂ)=
      (hillPhysicalCosineEnergyPath q hq hr k a θ).extend t :=
  positiveRealEnergyLift_sq c _
    (hillPhysicalCosineEnergyPath_real q hq hr k hk a θ t)
    (hillPhysicalCosineEnergyPath_shift_pos q hq hr k hk a θ c hleft t)

/-- The ORIGINAL scalar terminal correction is also the actual integral
on the quadratic image of its CONSTRUCTED positive frequency lift.
Integrability is proved, with no source-side integral assumption. -/
theorem hillRegularAbelianCorrection_eq_lifted_cosine_path (n k : ℕ)
    (hn : 1≤n) (hk : 1≤k) (hkn : k≠n)
    (hgap : hillRealGapHalfLength q hq hr k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr k hk)≠0)
    (c : ℝ) (hleft : 0<hillRealLabels q hq hr (2*k-1)+c) :
    let θ := hillDirichletSelectedRealAngle q hq hr k hk hgap
    let f := fun E : ℂ => hillAbelianSelectedGlobalPsi q hq hr n hn E/
      prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q))
        (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk)) E
    CurveIntegrable (holomorphicOneForm f)
      (quadraticEnergyPath (c:ℂ)
        (hillPhysicalCosineFrequencyPath q hq hr k (realCosineArcAnchor θ) θ c)) ∧
      (∫ᶜ E in quadraticEnergyPath (c:ℂ)
        (hillPhysicalCosineFrequencyPath q hq hr k (realCosineArcAnchor θ) θ c),
        holomorphicOneForm f E)=hillRegularAbelianCorrection q hq hr n hn k hk := by
  dsimp only
  unfold hillPhysicalCosineFrequencyPath
  let θ := hillDirichletSelectedRealAngle q hq hr k hk hgap
  let Γ := hillPhysicalCosineEnergyPath q hq hr k (realCosineArcAnchor θ) θ
  have hreal (t : unitInterval) : (Γ t).im=0 := by
    simpa only [Path.extend_apply _ t.property] using
      hillPhysicalCosineEnergyPath_real q hq hr k hk (realCosineArcAnchor θ) θ (t:ℝ)
  have hpos (t : unitInterval) : 0<(Γ t).re+c := by
    simpa only [Path.extend_apply _ t.property] using
      hillPhysicalCosineEnergyPath_shift_pos q hq hr k hk (realCosineArcAnchor θ) θ c hleft (t:ℝ)
  have he := quadraticEnergyPath_positiveRealEnergyLiftPath c Γ hreal hpos
  have h := hillRegularAbelianCorrection_eq_prescribed_cosine_path q hq hr n k hn hk hkn hgap hw
  dsimp only at h
  rcases h with ⟨hi,hv⟩
  change CurveIntegrable _ Γ at hi
  change (∫ᶜ E in Γ, _) = _ at hv
  rw [← he] at hi hv
  constructor
  · simpa only [curveIntegrable_cast_iff] using hi
  · simpa only [curveIntegral_cast] using hv

end NLS.KdV
