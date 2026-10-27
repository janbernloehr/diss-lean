import NLS.ZakharovShabat.NativeWeightedBirkhoff
import NLS.ZakharovShabat.SourceBirkhoffWeightedCanonical
import NLS.ZakharovShabat.PhysicalPoissonBracket

/-! # Canonical derivatives on original weighted distributions

The scalar coordinates extend to original complex distributions. Their full
derivatives satisfy all three canonical identities in the absolutely convergent
Fourier formula, with raw unit-mode directions and the original factor -i.
-/
noncomputable section
set_option autoImplicit false
open Set NLS.Poisson NLS.Fourier SmoothPeriodicTest
open scoped ENNReal
namespace NLS.ZakharovShabat.NativeWeightedPeriodic
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A raw Fourier mode in the first original distribution component. -/
def modeLeft (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : Space w p :=
  (coefficients w p).symm
    (WeightedCoeffPair.inlCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ n 1))

/-- A raw Fourier mode in the second original distribution component. -/
def modeRight (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : Space w p :=
  (coefficients w p).symm
    (WeightedCoeffPair.inrCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ n 1))

@[simp] theorem coefficients_modeLeft (w : SpectralWeight) (n : ℤ) :
    coefficients w p (modeLeft w p n) =
      WeightedCoeffPair.inlCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ n 1) :=
  (coefficients w p).apply_symm_apply _

@[simp] theorem coefficients_modeRight (w : SpectralWeight) (n : ℤ) :
    coefficients w p (modeRight w p n) =
      WeightedCoeffPair.inrCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ n 1) :=
  (coefficients w p).apply_symm_apply _

/-- The physical Fourier pairing uses opposite frequencies and unweighted unit modes. -/
def poissonTerms (w : SpectralWeight) (L M : Space w p →L[ℂ] ℂ) (n : ℤ) : ℂ :=
  L (modeLeft w p n) * M (modeRight w p (-n)) -
    L (modeRight w p n) * M (modeLeft w p (-n))

def poisson (w : SpectralWeight) (L M : Space w p →L[ℂ] ℂ) : ℂ :=
  -Complex.I * ∑' n : ℤ, poissonTerms w L M n

private theorem poisson_pullback (w : SpectralWeight)
    (L M : WeightedRegularSourceCotangent (sourceFrequencyWeight w) p) :
    Summable (fun n => ‖poissonTerms w
      (L.toCotangent.comp (coefficients w p).toContinuousLinearEquiv.toContinuousLinearMap)
      (M.toCotangent.comp (coefficients w p).toContinuousLinearEquiv.toContinuousLinearMap) n‖) ∧
    poisson w
      (L.toCotangent.comp (coefficients w p).toContinuousLinearEquiv.toContinuousLinearMap)
      (M.toCotangent.comp (coefficients w p).toContinuousLinearEquiv.toContinuousLinearMap) =
        L.bivector M := by
  constructor
  · simpa [poissonTerms] using L.summable_norm M
  · simpa [poisson, poissonTerms] using (L.bivector_eq_tsum M).symm

/-- Physical realization of an original complex distribution with weighted square-summable coefficients. -/
def physicalComplex (w : SpectralWeight) : Space w 2 →L[ℂ] IntervalPairL2 :=
  sourcePhysicalL2.comp ((originalWeightedSourceCLM w).comp
    (coefficients w 2).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The complex realization restricts to the same physical representative on real distributions. -/
theorem physicalComplex_real (w : SpectralWeight) (φ : realSpace w 2) :
    physicalComplex w φ.val = (physical w φ).val := by
  change sourcePhysicalL2 (source w φ).val = sourcePhysicalL2Equiv (source w φ).val
  exact (sourcePhysicalL2Equiv_apply _).symm

/-- Actual physical cotangents pull back to the absolutely convergent native bracket,
which equals the literal cross-gradient integral with factor -i. -/
theorem poisson_physical (w : SpectralWeight) (L M : IntervalPairL2 →L[ℂ] ℂ) :
    Summable (fun n => ‖poissonTerms w (L.comp (physicalComplex w))
      (M.comp (physicalComplex w)) n‖) ∧
    poisson w (L.comp (physicalComplex w)) (M.comp (physicalComplex w)) =
      physicalCotangentBivector L M := by
  have h := poisson_pullback w
    ((RegularSourceCotangent.ofCotangent le_rfl (L.comp sourcePhysicalL2)).restrictWeight w)
    ((RegularSourceCotangent.ofCotangent le_rfl (M.comp sourcePhysicalL2)).restrictWeight w)
  change Summable (fun n => ‖poissonTerms w (L.comp (physicalComplex w))
      (M.comp (physicalComplex w)) n‖) ∧
    poisson w (L.comp (physicalComplex w)) (M.comp (physicalComplex w)) =
      sourceBivector le_rfl (L.comp sourcePhysicalL2) (M.comp sourcePhysicalL2) at h
  exact ⟨h.1, h.2.trans (physicalCotangentBivector_eq_source L M).symm⟩

/-- The bracket of full derivatives of physical functionals is preserved on every weighted
Hilbert distribution space. Differentiability is assumed on the physical L2 space. -/
theorem poisson_physical_functions (w : SpectralWeight) (F G : IntervalPairL2 → ℂ)
    (φ : Space w 2) (hF : DifferentiableAt ℂ F (physicalComplex w φ))
    (hG : DifferentiableAt ℂ G (physicalComplex w φ)) :
    poisson w (fderiv ℂ (F ∘ physicalComplex w) φ)
      (fderiv ℂ (G ∘ physicalComplex w) φ) = physicalBracket F G (physicalComplex w φ) := by
  rw [(hF.hasFDerivAt.comp φ (physicalComplex w).hasFDerivAt).fderiv,
    (hG.hasFDerivAt.comp φ (physicalComplex w).hasFDerivAt).fderiv]
  exact (poisson_physical w _ _).2

/-- The original scalar complex x-coordinate, now on the distribution carrier. -/
def complexX (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight) (n : ℤ)
    (φ : Space w p) : ℂ :=
  originalWeightedBirkhoffX hp hp1 s w n (coefficients w p φ)

/-- The original scalar complex y-coordinate, now on the distribution carrier. -/
def complexY (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight) (n : ℤ)
    (φ : Space w p) : ℂ :=
  originalWeightedBirkhoffY hp hp1 s w n (coefficients w p φ)

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  (D : SourceSection17OriginalData hp hp1 W₀ W V s)
include D

/-- The complex extensions retain both actual real Birkhoff coordinates. -/
theorem complex_coordinates_real (w : SpectralWeight) (φ : realSpace w p) (n : ℤ) :
    complexX hp hp1 s w n φ.val = (birkhoff D w φ).fst.val.val n ∧
    complexY hp hp1 s w n φ.val = (birkhoff D w φ).snd.val.val n :=
  D.complex.originalWeightedBirkhoff_real w (realCoefficientsEquiv w φ) n

/-- Full distribution-space derivatives are the exact pullbacks of the weighted derivatives. -/
theorem complex_coordinates_fderiv (w : SpectralWeight) (φ : realSpace w p) (n : ℤ) :
    fderiv ℂ (complexX hp hp1 s w n) φ.val =
      (fderiv ℂ (originalWeightedBirkhoffX hp hp1 s w n) (coefficients w p φ.val)).comp
        (coefficients w p).toContinuousLinearEquiv.toContinuousLinearMap ∧
    fderiv ℂ (complexY hp hp1 s w n) φ.val =
      (fderiv ℂ (originalWeightedBirkhoffY hp hp1 s w n) (coefficients w p φ.val)).comp
        (coefficients w p).toContinuousLinearEquiv.toContinuousLinearMap := by
  let a := coefficients w p φ.val
  have ha : originalWeightedSourceCLM w a ∈ V :=
    D.complex.real_subset (source w φ).property
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
    (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
    (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
  have hx : DifferentiableAt ℂ (originalWeightedBirkhoffX hp hp1 s w n) a :=
    (((ex.analyticAt _).comp (D.complex.analytic _ ha)).comp
      ((originalWeightedSourceCLM w).analyticAt a)).differentiableAt
  have hy : DifferentiableAt ℂ (originalWeightedBirkhoffY hp hp1 s w n) a :=
    (((ey.analyticAt _).comp (D.complex.analytic _ ha)).comp
      ((originalWeightedSourceCLM w).analyticAt a)).differentiableAt
  exact ⟨(hx.hasFDerivAt.comp φ.val
      (coefficients w p).toContinuousLinearEquiv.hasFDerivAt).fderiv,
    (hy.hasFDerivAt.comp φ.val
      (coefficients w p).toContinuousLinearEquiv.hasFDerivAt).fderiv⟩

/-- All three canonical brackets are absolutely convergent and retain their physical signs. -/
theorem birkhoff_canonical (w : SpectralWeight) (φ : realSpace w p) (n m : ℤ) :
    let X := fun j => fderiv ℂ (complexX hp hp1 s w j) φ.val
    let Y := fun j => fderiv ℂ (complexY hp hp1 s w j) φ.val
    Summable (fun j => ‖poissonTerms w (X n) (X m) j‖) ∧
      Summable (fun j => ‖poissonTerms w (X n) (Y m) j‖) ∧
      Summable (fun j => ‖poissonTerms w (Y n) (Y m) j‖) ∧
      poisson w (X n) (X m) = 0 ∧
      poisson w (X n) (Y m) = -(if n = m then 1 else 0) ∧
      poisson w (Y n) (Y m) = 0 := by
  dsimp only
  obtain ⟨X,Y,hd,hb⟩ := D.complex.originalWeightedBirkhoff_canonical w (realCoefficientsEquiv w φ)
  change ∀ j, (X j).toCotangent = fderiv ℂ (originalWeightedBirkhoffX hp hp1 s w j)
    (coefficients w p φ.val) ∧ (Y j).toCotangent =
      fderiv ℂ (originalWeightedBirkhoffY hp hp1 s w j) (coefficients w p φ.val) at hd
  have hx (j : ℤ) : fderiv ℂ (complexX hp hp1 s w j) φ.val =
      (X j).toCotangent.comp (coefficients w p).toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [(complex_coordinates_fderiv D w φ j).1, ← (hd j).1]
  have hy (j : ℤ) : fderiv ℂ (complexY hp hp1 s w j) φ.val =
      (Y j).toCotangent.comp (coefficients w p).toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [(complex_coordinates_fderiv D w φ j).2, ← (hd j).2]
  simp only [hx, hy]
  have hxx := poisson_pullback w (X n) (X m)
  have hxy := poisson_pullback w (X n) (Y m)
  have hyy := poisson_pullback w (Y n) (Y m)
  exact ⟨hxx.1,hxy.1,hyy.1,hxx.2.trans (hb n m).1,
    hxy.2.trans (hb n m).2.1,hyy.2.trans (hb n m).2.2⟩

end NLS.ZakharovShabat.NativeWeightedPeriodic
