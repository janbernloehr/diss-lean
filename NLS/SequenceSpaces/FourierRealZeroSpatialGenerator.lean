import NLS.SequenceSpaces.FourierRealZeroProjection
import NLS.SequenceSpaces.FourierRealZeroCoordinates
import NLS.SequenceSpaces.SignedSobolevSpatialGenerator
import NLS.SequenceSpaces.WeightedSpatialTranslationDerivative
import NLS.FunctionalAnalysis.LinearCurveDerivative

/-! Spatial generators and strong orbit differentiation on the actual
physical real zero-mode weighted Banach spaces. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Full coefficient-space projection onto the literal physical real zero mode form. -/
def fourierRealZeroFullProjection (w : Weight) (hw : ∀ k, w (-k)=w k) :
    WeightedCoeff w p →L[ℝ] fourierRealZeroSubmodule w p :=
  (fourierRealZeroProjection w hw).comp ((zeroModeProjection w).restrictScalars ℝ)

theorem fourierRealZeroFullProjection_inclusion (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : fourierRealZeroSubmodule w p) : fourierRealZeroFullProjection w hw a.val.val=a := by
  change fourierRealZeroProjection w hw (zeroModeProjection w a.val.val)=a
  have hz : zeroModeProjection w a.val.val=a.val :=
    Subtype.ext (zeroModeProjection_coe w a.val.val a.val.property)
  rw [hz,fourierRealZeroProjection_inclusion]

/-- The SAME physical real zero-mode spatial generator across signed orders. -/
def fourierRealZeroSignedSpatialGenerator (s : ℝ) :
    fourierRealZeroSubmodule (Weight.signedSobolev (s+1)) p →L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev s) p :=
  (fourierRealZeroFullProjection (Weight.signedSobolev s) (Weight.signedSobolev_neg s)).comp
    (((signedSpatialGenerator s).restrictScalars ℝ).comp
      (((zeroModeSubmodule (Weight.signedSobolev (s+1)) p).subtypeL.restrictScalars ℝ).comp
        (fourierRealZeroSubmodule (Weight.signedSobolev (s+1)) p).subtypeL))

theorem fourierRealZeroSignedSpatialGenerator_apply (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (s+1)) p) (k : ℤ) :
    (fourierRealZeroSignedSpatialGenerator s a).val.val.val k=
      I*((2*Real.pi*k:ℝ):ℂ)*a.val.val.val k := by
  let d := signedSpatialGenerator s a.val.val
  have h0 : d.val 0=0 := by rw [signedSpatialGenerator_apply]; simp
  have hr (j : ℤ) : d.val (-j)=(starRingEnd ℂ) (d.val j) := by
    rw [signedSpatialGenerator_apply,signedSpatialGenerator_apply,a.property,map_mul,map_mul]
    simp only [Int.cast_neg,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  have he : fourierRealZeroFullProjection (Weight.signedSobolev s) (Weight.signedSobolev_neg s) d=
      (⟨⟨d,h0⟩,hr⟩ : fourierRealZeroSubmodule (Weight.signedSobolev s) p) :=
    fourierRealZeroFullProjection_inclusion _ _ ⟨⟨d,h0⟩,hr⟩
  change (fourierRealZeroFullProjection (Weight.signedSobolev s) (Weight.signedSobolev_neg s) d).val.val.val k= _
  rw [he]
  exact signedSpatialGenerator_apply s a.val.val k

theorem norm_fourierRealZeroSignedSpatialGenerator_le (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (s+1)) p) :
    ‖fourierRealZeroSignedSpatialGenerator s a‖ ≤ (2*Real.pi)*‖a‖ := by
  have he : (fourierRealZeroSignedSpatialGenerator s a).val.val=signedSpatialGenerator s a.val.val := by
    apply Subtype.ext
    funext k
    exact fourierRealZeroSignedSpatialGenerator_apply s a k
  change ‖(fourierRealZeroSignedSpatialGenerator s a).val.val‖ ≤ (2*Real.pi)*‖a.val.val‖
  rw [he]
  exact norm_signedSpatialGenerator_le s a.val.val

/-- Strong derivative at zero for any physical curve with the literal
Fourier spatial phases and a generator in the SAME weighted space. -/
theorem hasDerivAt_fourierRealZero_spatialCurve (w : Weight) (hw : ∀ k, w (-k)=w k)
    (hp : p ≠ ⊤) (a v : fourierRealZeroSubmodule w p)
    (hv : ∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*a.val.val.val k)
    (γ : ℝ → fourierRealZeroSubmodule w p)
    (hγ : ∀ t k, (γ t).val.val.val k=exp (((t*(2*Real.pi*k):ℝ):ℂ)*I)*a.val.val.val k) :
    HasDerivAt γ v 0 := by
  have hd := hasDerivAt_spatialTranslation w hp (2*Real.pi) a.val.val v.val.val hv 0
  simp only [spatialTranslation_zero] at hd
  have hproj := @NLS.FunctionalAnalysis.hasDerivAt_clm_comp (WeightedCoeff w p) (fourierRealZeroSubmodule w p)
    inferInstance inferInstance inferInstance inferInstance (fourierRealZeroFullProjection (p:=p) w hw) _ _ 0 hd
  have he : (fun t => fourierRealZeroFullProjection w hw (spatialTranslation w (2*Real.pi) t a.val.val))=γ := by
    funext t
    have hraw : spatialTranslation w (2*Real.pi) t a.val.val=(γ t).val.val := by
      apply Subtype.ext
      funext k
      rw [spatialTranslation_apply]
      exact (hγ t k).symm
    rw [hraw,fourierRealZeroFullProjection_inclusion]
  rw [he,fourierRealZeroFullProjection_inclusion] at hproj
  exact hproj


/-- A generator with unchanged coefficients and the physical norm bound,
allowing separately named adjacent source and target orders. -/
theorem exists_fourierRealZeroSignedSpatialGenerator (s t : ℝ) (hst : s+1=t)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev t) p) :
    ∃ v : fourierRealZeroSubmodule (Weight.signedSobolev s) p,
      (∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*a.val.val.val k) ∧
      ‖v‖ ≤ (2*Real.pi)*‖a‖ := by
  subst t
  exact ⟨fourierRealZeroSignedSpatialGenerator s a,
    fourierRealZeroSignedSpatialGenerator_apply s a,norm_fourierRealZeroSignedSpatialGenerator_le s a⟩

/-- Any strong derivative of a physical spatial orbit has the EXACT
original spatial Fourier generator, including negative and zero modes. -/
theorem fourierRealZero_spatialGenerator_of_hasDerivAt (w : Weight)
    (a v : fourierRealZeroSubmodule w p) (γ : ℝ → fourierRealZeroSubmodule w p)
    (hγ : ∀ t k, (γ t).val.val.val k=exp (((t*(2*Real.pi*k):ℝ):ℂ)*I)*a.val.val.val k)
    (hd : HasDerivAt γ v 0) (k : ℤ) :
    v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*a.val.val.val k := by
  have he := @NLS.FunctionalAnalysis.hasDerivAt_clm_comp (fourierRealZeroSubmodule w p) ℂ
    inferInstance inferInstance inferInstance inferInstance (fourierRealZeroEvalCLM w p k) _ _ 0 hd
  change HasDerivAt (fun s => (γ s).val.val.val k) (v.val.val.val k) 0 at he
  have hp := (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (I*((2*Real.pi*k:ℝ):ℂ)) 0).mul_const
    (a.val.val.val k)
  have hphase (s : ℝ) : I*((2*Real.pi*k:ℝ):ℂ)*(s:ℂ)=((s*(2*Real.pi*k):ℝ):ℂ)*I := by
    push_cast
    ring
  simp_rw [hphase] at hp
  simp only [zero_mul,ofReal_zero,exp_zero,one_mul] at hp
  have hfun : (fun s => (γ s).val.val.val k)=
      (fun s => exp (((s*(2*Real.pi*k):ℝ):ℂ)*I)*a.val.val.val k) := funext (fun s => hγ s k)
  rw [hfun] at he
  exact he.unique hp

end NLS.WeightedCoeff
