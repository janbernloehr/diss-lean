import NLS.ZakharovShabat.SourceSpectralSelectionCoefficientContinuity
import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing
import NLS.ZakharovShabat.DiscriminantPairFactorization

/-! # Canonical periodic endpoints under bounded coefficient limits

The canonical labels are retained by interpolation through real sources.
Both endpoints at each fixed index therefore converge under bounded
coefficientwise convergence, including at a collapsed gap. The real-type
relation makes convergence of the first Fourier component sufficient.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On real sources, convergence of the first component determines convergence
of the reflected, conjugated second component. -/
theorem tendsto_source_snd_of_realType_coefficientwise
    {α : Type*} {l : Filter α} (φ : α → CoeffPair p) (ψ : CoeffPair p)
    (hφ : ∀ k, IsRealType (CoeffPair.toMax p (φ k))) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) :
    Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)) := by
  have ha (k : α) : (φ k).snd n = conj ((φ k).fst (-n)) := hφ k n
  have hb : ψ.snd n = conj (ψ.fst (-n)) := hψ n
  simpa only [Function.comp_def, ← ha, ← hb] using continuous_conj.continuousAt.tendsto.comp (ht (-n))

/-- Every actual canonical periodic endpoint converges at its original index
under bounded coefficientwise convergence of real sources. No contour,
cluster assignment, reference parameter, or positive-gap premise is supplied. -/
theorem tendsto_source_canonicalPeriodicEndpoints_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax p (φ k))) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) :
    Tendsto (fun k => canonicalPeriodicLeft hp hp1 (periodOnePotential (φ k)) (periodOnePotential_mem (φ k)) n) l
      (𝓝 (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) ∧
    Tendsto (fun k => canonicalPeriodicRight hp hp1 (periodOnePotential (φ k)) (periodOnePotential_mem (φ k)) n) l
      (𝓝 (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) := by
  have ht₂ := tendsto_source_snd_of_realType_coefficientwise φ ψ hφ hψ ht
  constructor
  · exact tendsto_source_spectral_selection_of_bounded_coefficientwise hp hp1 φ ψ hb hφ hψ ht ht₂
      (fun χ => canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)
      (fun χ hχ => continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 χ hχ n)
      (fun χ _ => (canonicalPeriodicEndpoints_mem_spectrum hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n).1)
  · exact tendsto_source_spectral_selection_of_bounded_coefficientwise hp hp1 φ ψ hb hφ hψ ht ht₂
      (fun χ => canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)
      (fun χ hχ => continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 χ hχ n)
      (fun χ _ => (canonicalPeriodicEndpoints_mem_spectrum hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n).2)

/-- Actual canonical midpoints and gaps, rather than unassigned contour
expressions, converge at every fixed index under bounded coefficient limits. -/
theorem tendsto_source_canonicalPeriodicMidpoint_and_gap_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax p (φ k))) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) :
    Tendsto (fun k => canonicalPeriodicMidpoint hp hp1 (periodOnePotential (φ k)) (periodOnePotential_mem (φ k)) n) l
      (𝓝 (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) ∧
    Tendsto (fun k => canonicalPeriodicGap hp hp1 (periodOnePotential (φ k)) (periodOnePotential_mem (φ k)) n) l
      (𝓝 (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) := by
  have h := tendsto_source_canonicalPeriodicEndpoints_of_bounded_coefficientwise hp hp1 φ ψ hb hφ hψ ht n
  exact ⟨(h.1.add h.2).div_const 2, h.2.sub h.1⟩

end NLS.ZakharovShabat
