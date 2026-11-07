import NLS.SequenceSpaces.FourierRealZeroSpatialGenerator
import NLS.SequenceSpaces.FourierRealZeroMultiplier
import NLS.SequenceSpaces.SpatialInverseSymbol

/-! Adjacent signed Sobolev orders on the physical real zero-mode form.
Every inclusion, derivative and recovery retains the original 2*pi symbol. -/
noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def signedRealInclusion (s : ℝ) :
    fourierRealZeroSubmodule (Weight.signedSobolev (s+1)) p →L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev s) p :=
  fourierRealZeroMultiplier _ _ (Weight.signedSobolev_neg s) (fun _ => 1) 1 zero_le_one
    (by intro k; simp only [norm_one,mul_one,one_mul];
        exact Real.rpow_le_rpow_of_exponent_le (le_max_left (1:ℝ) |(k:ℝ)|) (by linarith))
    (by intro k; simp)

def signedRealSpatialRecovery (s : ℝ) :
    fourierRealZeroSubmodule (Weight.signedSobolev s) p →L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev (s+1)) p :=
  fourierRealZeroMultiplier _ _ (Weight.signedSobolev_neg (s+1)) spatialInverseSymbol
    (1/(2*Real.pi)) (by positivity) (Weight.signedSobolev_spatialInverse_bound s) spatialInverseSymbol_neg

theorem signedRealInclusion_apply (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (s+1)) p) (k : ℤ) :
    (signedRealInclusion s a).val.val.val k=a.val.val.val k := by
  rw [signedRealInclusion,fourierRealZeroMultiplier_apply,one_mul]

theorem signedRealSpatialRecovery_apply (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) p) (k : ℤ) :
    (signedRealSpatialRecovery s a).val.val.val k=spatialInverseSymbol k*a.val.val.val k :=
  fourierRealZeroMultiplier_apply _ _ _ _ _ _ _ _ a k

theorem signedRealInclusion_injective (s : ℝ) : Function.Injective (signedRealInclusion (p:=p) s) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have he := congrArg (fun z => z.val.val.val k) h
  simpa only [signedRealInclusion_apply] using he

theorem signedRealSpatialRecovery_generator (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (s+1)) p) :
    signedRealSpatialRecovery s (fourierRealZeroSignedSpatialGenerator s a)=a := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [signedRealSpatialRecovery_apply,fourierRealZeroSignedSpatialGenerator_apply,spatialInverseSymbol_generator]
  split_ifs with hk
  · subst k; exact a.val.property.symm
  · rfl

theorem signedRealInclusion_recovery (s : ℝ)
    (a v : fourierRealZeroSubmodule (Weight.signedSobolev s) p)
    (hv : ∀ k, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*a.val.val.val k) :
    signedRealInclusion s (signedRealSpatialRecovery s v)=a := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [signedRealInclusion_apply,signedRealSpatialRecovery_apply,hv,spatialInverseSymbol_generator]
  split_ifs with hk
  · subst k; exact a.val.property.symm
  · rfl

def fourierRealZeroSpatialTranslation (w : Weight) (hw : ∀ k, w (-k)=w k) (t : ℝ) :
    fourierRealZeroSubmodule w p →L[ℝ] fourierRealZeroSubmodule w p :=
  (fourierRealZeroFullProjection w hw).comp
    (((spatialTranslation w (2*Real.pi) t).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
      (((zeroModeSubmodule w p).subtypeL.restrictScalars ℝ).comp (fourierRealZeroSubmodule w p).subtypeL))

theorem fourierRealZeroSpatialTranslation_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (t : ℝ) (a : fourierRealZeroSubmodule w p) (k : ℤ) :
    (fourierRealZeroSpatialTranslation w hw t a).val.val.val k=
      exp (((t*(2*Real.pi*k):ℝ):ℂ)*I)*a.val.val.val k := by
  let b := spatialTranslation w (2*Real.pi) t a.val.val
  have h0 : b.val 0=0 := by
    dsimp only [b]
    rw [spatialTranslation_apply]
    rw [show a.val.val.val 0=0 from a.val.property,mul_zero]
  have hr (j : ℤ) : b.val (-j)=(starRingEnd ℂ) (b.val j) := by
    dsimp only [b]
    rw [spatialTranslation_apply,spatialTranslation_apply]
    rw [show a.val.val.val (-j)=(starRingEnd ℂ) (a.val.val.val j) from a.property j]
    simp only [map_mul,← Complex.exp_conj,Complex.conj_I,
      Complex.conj_ofReal,Int.cast_neg]
    push_cast
    congr 2
    ring
  have he := fourierRealZeroFullProjection_inclusion w hw (⟨⟨b,h0⟩,hr⟩ : fourierRealZeroSubmodule w p)
  change (fourierRealZeroFullProjection w hw b).val.val.val k=_
  rw [he]
  exact spatialTranslation_apply w (2*Real.pi) t a.val.val k

theorem fourierRealZeroSpatialTranslation_zero (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : fourierRealZeroSubmodule w p) : fourierRealZeroSpatialTranslation w hw 0 a=a := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  simp only [fourierRealZeroSpatialTranslation_apply,zero_mul,ofReal_zero,exp_zero,one_mul]

end NLS.WeightedCoeff
