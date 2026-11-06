import NLS.ZakharovShabat.SourceComponentSwap
import NLS.ZakharovShabat.CentralPeriodicRoots
import Mathlib.Analysis.Analytic.Order

/-! # Original spectral data under unsigned component exchange

Spectral reflection preserves the original algebraic multiplicities, not
only the zero set of the discriminant. Central root counts therefore
transform with the exact same multiplicities. These are the inputs for
reflecting the signed canonical endpoint labels.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reflection of the spectral parameter identifies the actual periodic
spectra under the component swap, at every finite source exponent p>1. -/
theorem sourcePeriodicSpectrum_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    -z ∈ periodicSpectrum hp (periodOnePotential (sourceComponentSwap φ)) ↔
      z ∈ periodicSpectrum hp (periodOnePotential φ) := by
  rw [← canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem _) (-z),
    sourceDiscriminant_componentSwap hp hp1 φ z,
    canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem _) z]

/-- The exact original algebraic multiplicity is preserved by the spectral
reflection. No simple-root or open-gap hypothesis is needed. -/
theorem sourcePeriodicMultiplicity_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp (periodOnePotential (sourceComponentSwap φ)) (-z) =
      periodicAlgebraicMultiplicity hp (periodOnePotential φ) z := by
  let f := fun w : ℂ => (canonicalDiscriminant hp
    (periodOnePotential (sourceComponentSwap φ)) w)^2-4
  have he : (f ∘ fun w : ℂ => -w) = fun w : ℂ =>
      (canonicalDiscriminant hp (periodOnePotential φ) w)^2-4 := by
    funext w
    exact congrArg (fun d : ℂ => d^2-4) (sourceDiscriminant_componentSwap hp hp1 φ w)
  have hd : deriv (fun w : ℂ => -w) z ≠ 0 := by simp
  have ho := analyticOrderAt_comp_of_deriv_ne_zero (f := f) (z₀ := z)
    (show AnalyticAt ℂ (fun w : ℂ => -w) z from analyticAt_id.neg) hd
  rw [he,analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem _) z] at ho
  have hs : analyticOrderAt f (-z) =
      (periodicAlgebraicMultiplicity hp (periodOnePotential (sourceComponentSwap φ)) (-z) : ℕ∞) :=
    analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem _) (-z)
  rw [hs] at ho
  exact_mod_cast ho.symm

/-- The original central spectral box is invariant under reflection. -/
theorem neg_mem_centralSpectralBox_iff (N : ℕ) (z : ℂ) :
    -z ∈ centralSpectralBox N ↔ z ∈ centralSpectralBox N := by
  simp [centralSpectralBox]

/-- The actual central spectral sets reflect, with the same cutoff. -/
theorem sourceCentralPeriodicSpectrum_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (z : ℂ) :
    -z ∈ centralPeriodicSpectrum hp (periodOnePotential (sourceComponentSwap φ)) N ↔
      z ∈ centralPeriodicSpectrum hp (periodOnePotential φ) N := by
  rw [mem_centralPeriodicSpectrum,mem_centralPeriodicSpectrum,
    sourcePeriodicSpectrum_componentSwap hp hp1 φ z,neg_mem_centralSpectralBox_iff]

/-- Each original central root count is preserved, including repeated
central roots and collapsed gaps. -/
theorem sourceCentralPeriodicRoots_count_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (z : ℂ) :
    (centralPeriodicRoots hp (periodOnePotential (sourceComponentSwap φ)) N).count (-z) =
      (centralPeriodicRoots hp (periodOnePotential φ) N).count z := by
  simp only [count_centralPeriodicRoots,sourceCentralPeriodicSpectrum_componentSwap hp hp1 φ N z,
    sourcePeriodicMultiplicity_componentSwap hp hp1 φ z]

/-- The actual discriminant derivative has the opposite spectral parity. -/
theorem sourceDiscriminant_deriv_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    deriv (canonicalDiscriminant hp (periodOnePotential (sourceComponentSwap φ))) (-z) =
      -deriv (canonicalDiscriminant hp (periodOnePotential φ)) z := by
  have he : (fun w : ℂ => canonicalDiscriminant hp (periodOnePotential (sourceComponentSwap φ)) (-w)) =
      canonicalDiscriminant hp (periodOnePotential φ) := funext (sourceDiscriminant_componentSwap hp hp1 φ)
  have hd := ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
    (-z,sourceComponentSwap φ) (mem_univ _)).comp
      (f := fun w : ℂ => (w,sourceComponentSwap φ)) (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt
  have hc := hd.comp z (hasDerivAt_id z).neg
  have hc' : HasDerivAt (fun w : ℂ => canonicalDiscriminant hp
      (periodOnePotential (sourceComponentSwap φ)) (-w))
      (deriv (canonicalDiscriminant hp (periodOnePotential (sourceComponentSwap φ))) (-z)*(-1)) z := hc
  rw [he] at hc'
  have hval := hc'.deriv
  linear_combination hval

end NLS.ZakharovShabat
