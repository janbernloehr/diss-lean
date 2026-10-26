import NLS.ZakharovShabat.L2WholeLinePureAbsoluteContinuity
import NLS.ZakharovShabat.L2WholeLineGapResolvent

/-! # The complete whole-line spectral overview for the original Hilbert source -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace NLS.ZakharovShabat

/-- Pure absolute continuity for the unchanged original real Hilbert source. -/
theorem source_wholeLineRealSpectralMeasure_absolutelyContinuous
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) (v : WholeLineL2) :
    wholeLineRealSpectralMeasure (sourcePhysicalL2 φ)
      ((sourcePhysicalL2_realType_iff φ).mpr hφ) v ≪ (volume : Measure ℝ) :=
  wholeLineRealSpectralMeasure_absolutelyContinuous _ _ v

/-- The printed p.17 whole-line spectral statement with the original source,
original physical closure, actual periodic gap endpoints, and actual scalar
spectral measures. The spectral set is independently defined by failure
of a bounded two-sided inverse. All endpoints and collapsed gaps are retained. -/
theorem source_wholeLine_spectral_overview
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    IsSelfAdjoint (wholeLineMinimalOperator (sourcePhysicalL2 φ)).closure ∧
    wholeLineSpectrum (sourcePhysicalL2 φ) = Complex.ofReal ''
      (⋃ n : ℤ, Ioo
        (canonicalPeriodicLeft (by simp) (by norm_num)
          (periodOnePotential φ) (periodOnePotential_mem φ) n).re
        (canonicalPeriodicRight (by simp) (by norm_num)
          (periodOnePotential φ) (periodOnePotential_mem φ) n).re)ᶜ ∧
    ∀ v : WholeLineL2, wholeLineRealSpectralMeasure (sourcePhysicalL2 φ)
      ((sourcePhysicalL2_realType_iff φ).mpr hφ) v ≪ (volume : Measure ℝ) := by
  refine ⟨source_wholeLineMinimalOperator_closure_isSelfAdjoint φ hφ, ?_,
    source_wholeLineRealSpectralMeasure_absolutelyContinuous φ hφ⟩
  exact source_wholeLineSpectrum_eq_floquetBands φ hφ

end NLS.ZakharovShabat
