import NLS.ZakharovShabat.SmoothNLSDataDensity

/-! # Nonextension of the constructed smooth classical NLS solution map

A candidate map agreeing with the constructed classical solution of every
smooth datum cannot be continuous at a non-Hilbert source. This states the
illposedness conclusion directly using arbitrary smooth data, on either
forward or symmetric compact time intervals.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The arbitrary-smooth constructor agrees with the existing finite-gap classical solution. -/
theorem smoothNLSDataOfFiniteGap_ordinary (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (smoothNLSDataOfFiniteGap hp hp1 φ hf).ordinary = sourceFiniteGapClassicalTrajectory hp hp1 φ hf := by
  apply (smoothNLSDataOfFiniteGap hp hp1 φ hf).ordinary_isClassical.eq_of_eq_at
    (sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf).1 0
  exact (smoothNLSDataOfFiniteGap hp hp1 φ hf).ordinary_zero

/-- Agreement with the actual global classical solutions of all smooth initial data.
The input and output source exponents may differ. -/
def AgreesWithSmoothClassicalNLS (J : Set ℝ)
    (F : realTypeSourceSubmodule p → C(J,realTypeSourceSubmodule q)) : Prop :=
  ∀ f : SmoothNLSData, ∀ time : J, F (f.source p) time = f.ordinarySource q time.val

/-- Smooth agreement entails the original physical coefficient agreement on finite-gap data. -/
theorem AgreesWithSmoothClassicalNLS.finiteGap_coefficients
    {J : Set ℝ} {F : realTypeSourceSubmodule p → C(J,realTypeSourceSubmodule q)}
    (hF : AgreesWithSmoothClassicalNLS J F) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (time : J) (n : ℤ) :
    (F φ time).val.fst n = NLS.Fourier.periodOneCoefficient
      (fun x : ℝ => sourceFiniteGapClassicalTrajectory hp hp1 φ hf time.val (x : AddCircle (2 : ℝ))) n := by
  have he := hF (smoothNLSDataOfFiniteGap hp hp1 φ hf) time
  rw [smoothNLSDataOfFiniteGap_source] at he
  rw [he,SmoothNLSData.ordinarySource,smoothPeriodOneSourceAt_fst,smoothNLSDataOfFiniteGap_ordinary]

/-- Corollary 22.2(iii), directly for extensions of the all-smooth classical solution map. -/
theorem smoothClassicalNLS_corollary22_2_iii
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h2p : 2 < p) (hpq : p ≤ q)
    (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p.le)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q))
    (hF : AgreesWithSmoothClassicalNLS (Icc (0 : ℝ) T) F) : ¬ ContinuousAt F φ :=
  classicalNLS_corollary22_2_iii hp hq h2p hpq T hT φ hφ F
    (hF.finiteGap_coefficients hp (lt_trans (by norm_num) h2p))

/-- Theorem 18.5(iv), directly for the constructed smooth classical solution map. -/
theorem smoothClassicalNLS_theorem18_5_iv
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h2p : 2 < p) (hpq : p ≤ q)
    (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p.le)
    (F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule q))
    (hF : AgreesWithSmoothClassicalNLS (Icc (-T) T) F) : ¬ ContinuousAt F φ :=
  classicalNLS_theorem18_5_iv hp hq h2p hpq T hT φ hφ F
    (hF.finiteGap_coefficients hp (lt_trans (by norm_num) h2p))

end NLS.ZakharovShabat
