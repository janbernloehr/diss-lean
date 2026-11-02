import NLS.KdV.SingularHillAlgebraicMultiplicity
import NLS.Articles.KdVPseudomeasures.SpectralClosedFibers

/-! The source's FULL original real H-minus-one potential and isospectral
set, defined from the actual full-domain physical operator and multiplicities.
No endpoint membership is built into this original potential type. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The article's original real, mean-zero, physically period-one H-minus-one domain. -/
def OriginalHminusOnePotential :=
  {q : FourierLebesgueSpace (2:ℝ) (-1) 2 // q.val.IsRealMeanZeroPeriodOne}

/-- The full original isospectral set, retaining every actual physical
algebraic multiplicity and allowing all original H-minus-one potentials. -/
def originalIsospectralSet (q : OriginalHminusOnePotential) : Set OriginalHminusOnePotential :=
  {p | ∀ z : ℂ, singularHillAlgebraicMultiplicity p.val z = singularHillAlgebraicMultiplicity q.val z}

/-- Every original potential belongs to its actual isospectral set. -/
theorem mem_originalIsospectralSet_self (q : OriginalHminusOnePotential) : q ∈ originalIsospectralSet q :=
  fun _ => rfl

/-- The full original definition fixes the ENTIRE physical complex spectrum. -/
theorem originalIsospectralSet_spectrum (q p : OriginalHminusOnePotential)
    (h : p ∈ originalIsospectralSet q) : singularHillSpectrum p.val = singularHillSpectrum q.val := by
  ext z
  rw [← singularHillAlgebraicMultiplicity_pos_iff, ← singularHillAlgebraicMultiplicity_pos_iff, h z]

/-- An endpoint potential is realized in the original source domain with its
ENTIRE distribution and all three physical constraints retained. -/
def sourceOriginalPotential (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    OriginalHminusOnePotential :=
  ⟨potentialHminusOne r hr q, potentialHminusOne_source_conditions r hr q⟩

/-- The original adapter changes no smooth-test action. -/
theorem sourceOriginalPotential_val (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    (sourceOriginalPotential r hr q).val.val = q.val.val := potentialHminusOne_val r hr q

/-- The previously proved endpoint source spectrum is EXACTLY the full original spectrum. -/
theorem sourceHillSpectrum_eq_original (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    sourceHillSpectrum r hr q = singularHillSpectrum (sourceComplexHminusOne r hr q) := rfl

/-- The actual endpoint multiplicity is the SAME full original root-space dimension. -/
theorem sourceHillAlgebraicMultiplicity_eq_original (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    sourceHillAlgebraicMultiplicity r hr q z =
      singularHillAlgebraicMultiplicity (sourceComplexHminusOne r hr q) z := rfl

/-- On endpoint realizations, membership in the FULL original isospectral set
is precisely equality of the ENTIRE canonical label sequence. The two
endpoint orders may be unrelated. -/
theorem sourceOriginalPotential_mem_isospectral_iff (r t : ℝ)
    (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : Potential r) (v : Potential t) :
    sourceOriginalPotential t ht v ∈ originalIsospectralSet (sourceOriginalPotential r hr q) ↔
      sourceHillLabels t ht v = sourceHillLabels r hr q := by
  constructor
  · intro h
    apply NLS.ordered_nat_enumeration_eq_of_multiplicity _ _
      (sourceHillLabels_finite_fiber t ht v) (sourceHillLabels_finite_fiber r hr q)
      (monotone_sourceHillLabels t ht v) (monotone_sourceHillLabels r hr q)
    intro x
    rw [sourceHillLabels_global_multiplicity, sourceHillLabels_global_multiplicity,
      sourceHillAlgebraicMultiplicity_eq_original, sourceHillAlgebraicMultiplicity_eq_original]
    exact h x
  · intro h z
    by_cases hz : z.im = 0
    · have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hz]
      rw [he]
      change singularHillAlgebraicMultiplicity (sourceComplexHminusOne t ht v.val) z.re =
        singularHillAlgebraicMultiplicity (sourceComplexHminusOne r hr q.val) z.re
      rw [← sourceHillAlgebraicMultiplicity_eq_original t ht v.val,
        ← sourceHillAlgebraicMultiplicity_eq_original r hr q.val,
        ← sourceHillLabels_global_multiplicity, ← sourceHillLabels_global_multiplicity, h]
    · rw [singularHillAlgebraicMultiplicity_eq_zero_of_im_ne_zero
        (sourceOriginalPotential t ht v).val (sourceOriginalPotential t ht v).property.1 z hz,
        singularHillAlgebraicMultiplicity_eq_zero_of_im_ne_zero
        (sourceOriginalPotential r hr q).val (sourceOriginalPotential r hr q).property.1 z hz]

end NLS.Articles.KdVPseudomeasures
