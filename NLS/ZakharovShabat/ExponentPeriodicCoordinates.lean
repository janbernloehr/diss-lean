import NLS.ZakharovShabat.ExponentCanonicalProducts
import NLS.ZakharovShabat.CanonicalPeriodicEndpoints

/-!
# Canonical periodic endpoints across finite exponents
The original spectra and multiplicities identify every central multiset.
At a common block containing the desired index, ordered paired enumeration
then fixes both canonical endpoints, including repeated roots. No agreement
of the chosen cutoffs or real-type hypothesis is needed.
-/

noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The complete central multiset retains all original periodic algebraic multiplicities. -/
theorem centralPeriodicRoots_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (N : ℕ) :
    centralPeriodicRoots hp φ N = centralPeriodicRoots hq (pairExponentInclusion h φ) N := by
  apply Multiset.ext.mpr
  intro z
  rw [count_centralPeriodicRoots, count_centralPeriodicRoots,
    centralPeriodicSpectrum_exponent hp hq h, periodicAlgebraicMultiplicity_exponent hp hq h]

/-- Both canonical endpoint sequences agree across finite exponents at every signed index. -/
theorem canonicalPeriodicEndpoints_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0)
    (hψ : pairExponentInclusion h φ ∈ pairParitySubspace 0) :
    canonicalPeriodicLeft hp hp1 φ hφ = canonicalPeriodicLeft hq hq1 (pairExponentInclusion h φ) hψ ∧
    canonicalPeriodicRight hp hp1 φ hφ = canonicalPeriodicRight hq hq1 (pairExponentInclusion h φ) hψ := by
  obtain ⟨hξ, hwξ, hcξ⟩ := canonicalPeriodicEndpoints_spec hp hp1 φ hφ
  obtain ⟨hη, hwη, hcη⟩ := canonicalPeriodicEndpoints_spec hq hq1 (pairExponentInclusion h φ) hψ
  have he (n : ℤ) :
      canonicalPeriodicLeft hp hp1 φ hφ n = canonicalPeriodicLeft hq hq1 (pairExponentInclusion h φ) hψ n ∧
      canonicalPeriodicRight hp hp1 φ hφ n = canonicalPeriodicRight hq hq1 (pairExponentInclusion h φ) hψ n := by
    let K := max (max (canonicalPeriodicCutoff hp hp1 φ hφ)
      (canonicalPeriodicCutoff hq hq1 (pairExponentInclusion h φ) hψ)) n.natAbs
    have hpK : canonicalPeriodicCutoff hp hp1 φ hφ ≤ K :=
      (le_max_left _ _).trans (le_max_left _ _)
    have hqK : canonicalPeriodicCutoff hq hq1 (pairExponentInclusion h φ) hψ ≤ K :=
      (le_max_right _ _).trans (le_max_left _ _)
    have hnK : n.natAbs ≤ K := le_max_right _ _
    have hs := (hξ.central_at_larger_cutoff K hpK).roots.trans
      ((centralPeriodicRoots_exponent hp hq h φ K).trans
        (hη.central_at_larger_cutoff K hqK).roots.symm)
    exact NLS.ordered_paired_multiset_enumeration_unique complexLexLE
      (Finset.Icc (-(K : ℤ)) K) _ _ _ _ hs
      (fun i _ => hwξ i) (fun i _ j _ hij => hcξ i j hij)
      (fun i _ => hwη i) (fun i _ j _ hij => hcη i j hij)
      n (by simp only [Finset.mem_Icc]; omega)
  exact ⟨funext (fun n => (he n).1), funext (fun n => (he n).2)⟩

/-- The left endpoint is unchanged by exponent inclusion. -/
theorem canonicalPeriodicLeft_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0)
    (hψ : pairExponentInclusion h φ ∈ pairParitySubspace 0) :
    canonicalPeriodicLeft hp hp1 φ hφ = canonicalPeriodicLeft hq hq1 (pairExponentInclusion h φ) hψ :=
  (canonicalPeriodicEndpoints_exponent hp hq hp1 hq1 h φ hφ hψ).1

/-- The right endpoint is unchanged by exponent inclusion. -/
theorem canonicalPeriodicRight_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0)
    (hψ : pairExponentInclusion h φ ∈ pairParitySubspace 0) :
    canonicalPeriodicRight hp hp1 φ hφ = canonicalPeriodicRight hq hq1 (pairExponentInclusion h φ) hψ :=
  (canonicalPeriodicEndpoints_exponent hp hq hp1 hq1 h φ hφ hψ).2

/-- The full left displacement sequence commutes with coefficient inclusion. -/
theorem canonicalPeriodicLeftDisplacement_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0)
    (hψ : pairExponentInclusion h φ ∈ pairParitySubspace 0) :
    Coeff.exponentInclusion h (canonicalPeriodicLeftDisplacement hp hp1 φ hφ) =
      canonicalPeriodicLeftDisplacement hq hq1 (pairExponentInclusion h φ) hψ := by
  ext n
  simp only [Coeff.exponentInclusion_apply, canonicalPeriodicLeftDisplacement_apply,
    canonicalPeriodicLeft_exponent hp hq hp1 hq1 h φ hφ hψ]

/-- The full right displacement sequence commutes with coefficient inclusion. -/
theorem canonicalPeriodicRightDisplacement_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0)
    (hψ : pairExponentInclusion h φ ∈ pairParitySubspace 0) :
    Coeff.exponentInclusion h (canonicalPeriodicRightDisplacement hp hp1 φ hφ) =
      canonicalPeriodicRightDisplacement hq hq1 (pairExponentInclusion h φ) hψ := by
  ext n
  simp only [Coeff.exponentInclusion_apply, canonicalPeriodicRightDisplacement_apply,
    canonicalPeriodicRight_exponent hp hq hp1 hq1 h φ hφ hψ]

end NLS.ZakharovShabat
