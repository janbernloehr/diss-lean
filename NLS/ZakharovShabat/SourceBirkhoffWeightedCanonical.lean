import NLS.ZakharovShabat.SourceWeightedCotangent
import NLS.ZakharovShabat.SourceBirkhoffLemma15_3
import NLS.ZakharovShabat.SourceBirkhoffOriginalWeightedMap

/-! # Canonical identities on original weighted source spaces

The actual weighted real coordinates admit scalar complex extensions whose
full derivatives are regular and satisfy all three canonical relations.
These assertions do not assume analyticity of a weighted sequence-valued map.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open Set NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Scalar complex extension of the original weighted real x-coordinate. -/
def originalWeightedBirkhoffX (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight) (n : ℤ)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) : ℂ :=
  (sourceBirkhoffMap hp hp1 s (originalWeightedSourceCLM w a)).1 n

/-- Scalar complex extension of the original weighted real y-coordinate. -/
def originalWeightedBirkhoffY (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight) (n : ℤ)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) : ℂ :=
  (sourceBirkhoffMap hp hp1 s (originalWeightedSourceCLM w a)).2 n

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The extensions equal the actual weighted map's raw coordinates on every real source. -/
theorem originalWeightedBirkhoff_real
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) (n : ℤ) :
    originalWeightedBirkhoffX hp hp1 s w n a.val = (D.originalWeightedRealMap w a).fst.val.val n ∧
    originalWeightedBirkhoffY hp hp1 s w n a.val = (D.originalWeightedRealMap w a).snd.val.val n := by
  have he := D.real_map_complex_inclusion (originalWeightedRealSource w a)
  constructor
  · rw [D.originalWeightedRealMap_fst]
    exact (congrArg (fun z : Coeff p × Coeff p => z.1 n) he).symm
  · rw [D.originalWeightedRealMap_snd]
    exact (congrArg (fun z : Coeff p × Coeff p => z.2 n) he).symm

/-- The full weighted scalar derivative is the pullback of the original coordinate derivative. -/
theorem originalWeightedBirkhoff_fderiv
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (ha : originalWeightedSourceCLM w a ∈ W) (n : ℤ) :
    fderiv ℂ (originalWeightedBirkhoffX hp hp1 s w n) a =
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) (originalWeightedSourceCLM w a)).comp
        (originalWeightedSourceCLM w) ∧
    fderiv ℂ (originalWeightedBirkhoffY hp hp1 s w n) a =
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) (originalWeightedSourceCLM w a)).comp
        (originalWeightedSourceCLM w) := by
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
  have hx := ((ex.analyticAt _).comp (D.analytic _ ha)).differentiableAt
  have hy := ((ey.analyticAt _).comp (D.analytic _ ha)).differentiableAt
  exact ⟨(hx.hasFDerivAt.comp a (originalWeightedSourceCLM w).hasFDerivAt).fderiv,
    (hy.hasFDerivAt.comp a (originalWeightedSourceCLM w).hasFDerivAt).fderiv⟩

/-- All three physical canonical identities, including closed gaps and exponents below two. -/
theorem originalWeightedBirkhoff_canonical
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    ∃ X Y : ℤ → WeightedRegularSourceCotangent (sourceFrequencyWeight w) p,
      (∀ n, (X n).toCotangent = fderiv ℂ (originalWeightedBirkhoffX hp hp1 s w n) a.val ∧
        (Y n).toCotangent = fderiv ℂ (originalWeightedBirkhoffY hp hp1 s w n) a.val) ∧
      ∀ n m, (X n).bivector (X m) = 0 ∧
        (X n).bivector (Y m) = -(if n = m then 1 else 0) ∧ (Y n).bivector (Y m) = 0 := by
  obtain ⟨X,Y,hd,hb⟩ := D.lemma15_3 (originalWeightedRealSource w a)
  refine ⟨fun n => (X n).restrictWeight w,fun n => (Y n).restrictWeight w,?_,hb⟩
  intro n
  have h := D.originalWeightedBirkhoff_fderiv w a.val
    (D.real_subset (originalWeightedRealSource w a).property) n
  constructor
  · rw [h.1]
    change (X n).toCotangent.comp _ = _
    rw [(hd n).1]
    rfl
  · rw [h.2]
    change (Y n).toCotangent.comp _ = _
    rw [(hd n).2]
    rfl

/-- The mixed identity is the absolutely convergent original Fourier formula
on actual weighted coordinate derivatives. -/
theorem originalWeightedBirkhoff_mixed_fourier_canonical
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) (n m : ℤ) :
    let L := fderiv ℂ (originalWeightedBirkhoffX hp hp1 s w n) a.val
    let M := fderiv ℂ (originalWeightedBirkhoffY hp hp1 s w m) a.val
    Summable (fun j : ℤ => ‖
      L (WeightedCoeffPair.inlCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ j 1)) *
        M (WeightedCoeffPair.inrCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ (-j) 1)) -
      L (WeightedCoeffPair.inrCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ j 1)) *
        M (WeightedCoeffPair.inlCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ (-j) 1))‖) ∧
    -Complex.I * ∑' j : ℤ,
      (L (WeightedCoeffPair.inlCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ j 1)) *
        M (WeightedCoeffPair.inrCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ (-j) 1)) -
      L (WeightedCoeffPair.inrCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ j 1)) *
        M (WeightedCoeffPair.inlCLM (sourceFrequencyWeight w) (WeightedCoeff.single _ (-j) 1))) =
      -(if n = m then 1 else 0) := by
  dsimp only
  obtain ⟨X,Y,hd,hb⟩ := D.originalWeightedBirkhoff_canonical w a
  have hs := (X n).summable_norm (Y m)
  have he := (X n).bivector_eq_tsum (Y m)
  rw [(hd n).1,(hd m).2] at hs he
  exact ⟨hs,he.symm.trans (hb n m).2.1⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
