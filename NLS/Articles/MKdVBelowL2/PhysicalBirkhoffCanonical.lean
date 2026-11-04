import NLS.Articles.MKdVBelowL2.CompatibleBirkhoffFamily
import NLS.ZakharovShabat.SourceComplexBirkhoffCanonical

/-! # Canonical full differentials on physical distribution inputs

Cotangents are represented by their physical Fourier coefficients, with
frequency reversal and the -i Poisson normalization supplied by the
established source bivector. Their pullbacks equal the actual Fréchet
derivatives of the physical family, not assumed coordinate derivatives. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Theorem 1.2(iii): actual physical differentials have absolutely convergent canonical brackets. -/
theorem compatibleBirkhoff_canonical (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p) :
    ∃ Z T : ℤ → RegularSourceCotangent p,
      (∀ n, fderiv ℂ (fun v => (compatibleBirkhoff hp hp1 v).1 n) u.val =
          (Z n).toCotangent.comp physicalCoefficients.toContinuousLinearMap ∧
        fderiv ℂ (fun v => (compatibleBirkhoff hp hp1 v).2 n) u.val =
          (T n).toCotangent.comp physicalCoefficients.toContinuousLinearMap) ∧
      ∀ n m, (Z n).bivector (Z m) = 0 ∧
        (Z n).bivector (T m) = -I*(if n=m then 1 else 0) ∧ (T n).bivector (T m) = 0 := by
  let C := originalBirkhoffChart hp hp1
  let φ := physicalRealCoefficientsCL u
  obtain ⟨Z,T,hd,hb⟩ := C.data.complex.complex_map_regular_canonical φ
  refine ⟨Z,T,?_,hb⟩
  intro n
  have ha := (C.data.complex.complex_map_analytic φ.val
    (C.data.complex.real_subset φ.property)).differentiableAt
  have hz : DifferentiableAt ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 C.roots ψ).1 n) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).differentiableAt.comp φ.val
      ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).differentiableAt.comp φ.val ha)
  have ht : DifferentiableAt ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 C.roots ψ).2 n) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).differentiableAt.comp φ.val
      ((ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).differentiableAt.comp φ.val ha)
  have hφ : φ.val = physicalCoefficients u.val := physicalRealCoefficientsCL_val u
  rw [hφ] at hz ht
  have hdn := hd n
  rw [hφ] at hdn
  constructor
  · have h := hz.hasFDerivAt.comp u.val ((physicalCoefficients (p := p)).toContinuousLinearMap.hasFDerivAt)
    rw [← hdn.1] at h
    exact h.fderiv
  · have h := ht.hasFDerivAt.comp u.val ((physicalCoefficients (p := p)).toContinuousLinearMap.hasFDerivAt)
    rw [← hdn.2] at h
    exact h.fderiv
/-- Physical Fourier Poisson bracket: exact coefficient transport, reversed indices and factor -i.
The full physical Fréchet derivatives are retained by the preceding theorem. -/
def physicalFLBracket (hp2 : (2 : ℝ≥0∞) ≤ p)
    (F G : (PhysicalFL p × PhysicalFL p) → ℂ) (u : PhysicalFL p × PhysicalFL p) : ℂ :=
  sourceBracket hp2 (F ∘ (physicalCoefficients (p := p)).symm) (G ∘ (physicalCoefficients (p := p)).symm)
    (physicalCoefficients u)

/-- Canonicality on the entire complex domain, with the article's phase orientation. -/
theorem compatibleBirkhoff_canonical_complex
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : (2 : ℝ≥0∞) ≤ p)
    (u : PhysicalFL p × PhysicalFL p) (hu : u ∈ compatibleBirkhoffDomain hp hp1) (n m : ℤ) :
    physicalFLBracket hp2 (fun v => (compatibleBirkhoff hp hp1 v).1 n)
      (fun v => (compatibleBirkhoff hp hp1 v).1 m) u = 0 ∧
    physicalFLBracket hp2 (fun v => (compatibleBirkhoff hp hp1 v).1 n)
      (fun v => (compatibleBirkhoff hp hp1 v).2 m) u = -I*(if n=m then 1 else 0) ∧
    physicalFLBracket hp2 (fun v => (compatibleBirkhoff hp hp1 v).2 n)
      (fun v => (compatibleBirkhoff hp hp1 v).2 m) u = 0 := by
  have h := (originalBirkhoffChart hp hp1).data.complex.complex_map_canonical_on_core
    hp2 (physicalCoefficients u) hu n m
  simpa only [physicalFLBracket,Function.comp_def,compatibleBirkhoff,physicalBirkhoff,
    ContinuousLinearEquiv.apply_symm_apply,sourceComplexBirkhoffMap] using! h

end NLS.Articles.MKdVBelowL2
