import NLS.Dynamics.PhaseSubsequenceSeparation
import NLS.ZakharovShabat.SourceSection22Nonextension

/-! # Original finite-gap phase separation

The literal Section 22 subsequence and separation estimates apply to
any actual finite-gap approximation of the original non-Hilbert source.
The original frequencies and amplitudes are retained. Negative selected
times give the physical first-coordinate sign on the symmetric interval.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The printed subsequence and separation estimates for any convergent
actual finite-gap approximation to a non-Hilbert source. Negative selected
times give the physical first-coordinate phase orientation. -/
theorem exists_finiteGap_coordinate_separation (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (ψ : ℕ → realTypeSourceSubmodule p) (hf : ∀ j, ψ j ∈ sourceFiniteGapLocus hp hp1)
    (hψ : Tendsto ψ atTop (𝓝 φ)) (n : ℤ)
    (hn : (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n ≠ 0) (T : ℝ) (hT : 0 < T) :
    let freq := fun j => A.finiteGapOrdinaryFrequency (ψ j) (hf j) n
    let amp := fun j => (sourceComplexBirkhoffMap hp hp1 s (ψ j).val).1
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ time : ℕ → ℝ,
      (∀ m, time m ∈ Icc (-T) T) ∧
      (∀ m, 1 ≤ ‖Complex.exp ((((-time m*(freq (r (m+1))-freq (r m)) : ℝ) : ℂ))*Complex.I)-1‖ ∧
        ‖amp (r m) n‖-‖amp (r (m+1))-amp (r m)‖ ≤
          ‖Complex.exp ((((-time m*freq (r (m+1)) : ℝ) : ℂ))*Complex.I)*amp (r (m+1)) n-
            Complex.exp ((((-time m*freq (r m) : ℝ) : ℂ))*Complex.I)*amp (r m) n‖) ∧
      ∀ᶠ m : ℕ in atTop, ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 n‖/2 ≤
        ‖Complex.exp ((((-time m*freq (r (m+1)) : ℝ) : ℂ))*Complex.I)*amp (r (m+1)) n-
          Complex.exp ((((-time m*freq (r m) : ℝ) : ℂ))*Complex.I)*amp (r m) n‖ := by
  dsimp only
  have hfreq := A.tendsto_finiteGapOrdinaryFrequency_atTop Q.roots D.roots_open
    D.roots_real_subset h2p φ hφ ψ hf hψ n
  have hamp : Tendsto (fun j => (sourceComplexBirkhoffMap hp hp1 s (ψ j).val).1)
      atTop (𝓝 (sourceComplexBirkhoffMap hp hp1 s φ.val).1) :=
    D.complex.continuous_complex_map_real.fst.continuousAt.tendsto.comp hψ
  obtain ⟨r,hr,time,ht,hb,he⟩ := Coeff.exists_phase_separated_subsequence
    (fun j => A.finiteGapOrdinaryFrequency (ψ j) (hf j) n) hfreq
    (fun j => (sourceComplexBirkhoffMap hp hp1 s (ψ j).val).1)
    (sourceComplexBirkhoffMap hp hp1 s φ.val).1 hamp n hn T hT
  refine ⟨r,hr,fun m => -time m,fun m => ⟨?_,?_⟩,?_,?_⟩
  · linarith [(ht m).2]
  · linarith [(ht m).1]
  · simpa only [neg_neg] using hb
  · simpa only [neg_neg] using he

end NLS.ZakharovShabat.SourceSection20Data
