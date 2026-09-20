import NLS.ZakharovShabat.CanonicalCriticalPoints
import NLS.ComplexAnalysis.RealAxisCalculus

/-!
# Reality of the discriminant on the real axis

The original spectral roots are real at real-type potentials. Thus all
finite parity polynomials commute with conjugation. Their normalized
limits and the intrinsic discriminant have the same symmetry.
-/

noncomputable section
open Complex ComplexConjugate Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each finite central parity polynomial has real coefficients at a real-type potential. -/
theorem conj_centralParityPolynomial_of_realType (hp : p ≠ ⊤) (φ : PairSpace p)
    (hreal : IsRealType φ) (N : ℕ) (r : ℤ) (z : ℂ) :
    conj (centralParityPolynomial hp φ N r z) = centralParityPolynomial hp φ N r (conj z) := by
  simp only [centralParityPolynomial, map_prod, map_pow, map_sub]
  apply Finset.prod_congr rfl
  intro a ha
  have him := periodicSpectrum_im_eq_zero_of_realType hp φ hreal a
    ((mem_centralPeriodicSpectrum hp φ N a).mp ha).1
  have he : conj a = a := by apply Complex.ext <;> simp [him]
  rw [he]

/-- The parity normalization is real, including the exceptional zero mode. -/
theorem conj_centralParityNormalization (N : ℕ) (r : ℤ) :
    conj (centralParityNormalization N r) = centralParityNormalization N r := by
  simp [centralParityNormalization, spectralPairDenominator, apply_ite]

/-- The corrected normalized finite parity polynomials retain conjugation symmetry. -/
theorem conj_normalizedCentralParityPolynomial_of_realType (hp : p ≠ ⊤) (φ : PairSpace p)
    (hreal : IsRealType φ) (N : ℕ) (r : ℤ) (z : ℂ) :
    conj (normalizedCentralParityPolynomial hp φ N r z) =
      normalizedCentralParityPolynomial hp φ N r (conj z) := by
  simp only [normalizedCentralParityPolynomial, map_div₀, map_mul,
    conj_centralParityNormalization, conj_centralParityPolynomial_of_realType hp φ hreal,
    apply_ite, map_neg, map_one, map_ofNat]

/-- Canonical parity products commute with conjugation at real-type potentials. -/
theorem conj_canonicalParityProduct_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    conj (canonicalParityProduct hp φ r z) = canonicalParityProduct hp φ r (conj z) := by
  have ht (a : ℂ) := (tendstoLocallyUniformlyOn_canonicalParityProduct_joint hp hp1 r hr).tendsto_at
    (show (a,(⟨φ,hφ⟩ : pairParitySubspace (p := p) 0)) ∈ univ from mem_univ _)
  have hc := continuous_conj.continuousAt.tendsto.comp (ht z)
  simp only [Function.comp_def, conj_normalizedCentralParityPolynomial_of_realType hp φ hreal] at hc
  exact tendsto_nhds_unique hc (ht (conj z))

/-- The intrinsic discriminant commutes with conjugation at real-type potentials. -/
theorem conj_canonicalDiscriminant_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (z : ℂ) :
    conj (canonicalDiscriminant hp φ z) = canonicalDiscriminant hp φ (conj z) := by
  simp only [canonicalDiscriminant, map_add, map_ofNat,
    conj_canonicalParityProduct_of_realType hp hp1 φ hφ hreal 0 (Or.inl rfl)]

/-- The discriminant is real at every real spectral parameter of a real-type potential. -/
theorem canonicalDiscriminant_im_eq_zero_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    (canonicalDiscriminant hp φ x).im = 0 := by
  have he := congrArg Complex.im (conj_canonicalDiscriminant_of_realType hp hp1 φ hφ hreal (x : ℂ))
  simp only [conj_im, conj_ofReal] at he
  linarith

/-- The spectral derivative is real on the real axis at real-type potentials. -/
theorem discriminant_derivative_im_eq_zero_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    (deriv (canonicalDiscriminant hp φ) x).im = 0 :=
  NLS.ComplexAnalysis.deriv_im_eq_zero_of_real_axis _
    (fun z => (analyticOnNhd_canonicalDiscriminant hp hp1 φ hφ z (mem_univ _)).differentiableAt)
    (canonicalDiscriminant_im_eq_zero_of_realType hp hp1 φ hφ hreal) x

end NLS.ZakharovShabat
