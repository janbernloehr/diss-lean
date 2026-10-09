import NLS.ZakharovShabat.TriangularPeriodicSpectrum
import NLS.SequenceSpaces.HolderEmbedding
import NLS.Fourier.SmoothPeriodicCoefficients

/-! # The real-type qualification in finite-gap regularity

The source's unqualified introductory regularity sentence fails for complex
potentials. The triangular source with coefficients 1/(1+|n|) in its first
component and zero in its second belongs to every finite lp with p>1 and
has free periodic spectrum. Only finitely many canonical gaps can be open,
but its coefficients have no smooth period-one representative.
This does not challenge regularity of real-type finite-gap sources.
-/
noncomputable section
open Set Complex
open scoped ENNReal ContDiff ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A rough scalar source belonging to every finite exponent above one. -/
def roughTriangularCoefficients (hp : p ≠ ⊤) (hp1 : 1 < p) : Coeff p :=
  ⟨fun n => (Weight.sobolev 1 n : ℂ)⁻¹, Weight.inverse_sobolev_memlp
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp) (by
      simpa only [one_mul,ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1)⟩

omit [Fact (1 ≤ p)] in
@[simp] theorem roughTriangularCoefficients_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    roughTriangularCoefficients hp hp1 n = (Weight.sobolev 1 n : ℂ)⁻¹ := rfl

/-- The original source coefficient pair for the complex finite-gap counterexample. -/
def roughTriangularSource (hp : p ≠ ⊤) (hp1 : 1 < p) : CoeffPair p :=
  WithLp.toLp p (roughTriangularCoefficients hp hp1,0)

omit [Fact (1 ≤ p)] in
/-- The coefficients fail absolute summability, at the exact harmonic threshold. -/
theorem roughTriangularCoefficients_not_memlp_one (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ¬ Memℓp (fun n => roughTriangularCoefficients hp hp1 n) 1 := by
  rw [show (fun n => roughTriangularCoefficients hp hp1 n) =
    (fun n => (Weight.sobolev 1 n : ℂ)⁻¹) from rfl,
    Weight.inverse_sobolev_memlp_iff (by norm_num)]
  norm_num

omit [Fact (1 ≤ p)] in
/-- No smooth period-one function has these original Fourier coefficients. -/
theorem roughTriangularCoefficients_no_smooth_representative (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ¬ ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      ∀ n : ℤ, Fourier.periodOneCoefficient f n = roughTriangularCoefficients hp hp1 n := by
  rintro ⟨f,hf,hper,hcoeff⟩
  apply roughTriangularCoefficients_not_memlp_one hp hp1
  have h := Fourier.memlp_periodOneCoefficient_sobolev_one 0 le_rfl f hf hper
  simpa only [Weight.sobolev_apply,Real.rpow_zero,Complex.ofReal_one,one_mul,hcoeff] using h

omit [Fact (1 ≤ p)] in
/-- In particular, the original coefficients have no spatially real-analytic representative. -/
theorem roughTriangularCoefficients_no_analytic_representative (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ¬ ∃ f : ℝ → ℂ, AnalyticOnNhd ℝ f Set.univ ∧ Function.Periodic f 1 ∧
      ∀ n : ℤ, Fourier.periodOneCoefficient f n = roughTriangularCoefficients hp hp1 n := by
  rintro ⟨f,hf,hper,hcoeff⟩
  exact roughTriangularCoefficients_no_smooth_representative hp hp1 ⟨f,hf.contDiff,hper,hcoeff⟩

/-- The counterexample is outside the real form used by the existing regularity theorem. -/
theorem roughTriangularSource_not_realType (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ¬ IsRealType (CoeffPair.toMax p (roughTriangularSource hp hp1)) := by
  intro h
  have h0 := h 0
  change (0 : Coeff p) 0 = conj (roughTriangularCoefficients hp hp1 (-0)) at h0
  simp [roughTriangularCoefficients_apply,Weight.sobolev_apply] at h0

/-- Its entire original periodic spectrum is exactly the free lattice. -/
theorem roughTriangularSource_spectrum (hp : p ≠ ⊤) (hp1 : 1 < p) :
    periodicSpectrum hp (periodOnePotential (roughTriangularSource hp hp1)) = freeLattice :=
  sourcePeriodicSpectrum_triangular hp _

/-- It is finite-gap under the source's literal spectral definition. -/
theorem roughTriangularSource_finite_gap (hp : p ≠ ⊤) (hp1 : 1 < p) :
    {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential (roughTriangularSource hp hp1))
      (periodOnePotential_mem (roughTriangularSource hp hp1)) n ≠ 0}.Finite :=
  finite_canonicalPeriodicGap_triangular hp hp1 _

/-- The unrestricted complex finite-gap-to-smooth assertion is false at every finite p>1. -/
theorem not_every_complex_finiteGap_source_smooth (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ¬ ∀ φ : CoeffPair p,
      {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0}.Finite →
      ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
        ∀ n : ℤ, Fourier.periodOneCoefficient f n = φ.fst n := by
  intro h
  exact roughTriangularCoefficients_no_smooth_representative hp hp1
    (h (roughTriangularSource hp hp1) (roughTriangularSource_finite_gap hp hp1))

end NLS.ZakharovShabat
