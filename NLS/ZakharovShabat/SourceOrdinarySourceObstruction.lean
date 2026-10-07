import NLS.ZakharovShabat.SourceFiniteGapOrdinaryCompatibility
import NLS.ZakharovShabat.SourceOrdinaryCoordinateObstruction

/-! # Ordinary source-trajectory nonextension in weaker target norms

A continuous observation of one nonzero Birkhoff coordinate detects the
unbounded physical phase. Thus even trajectories valued in a larger finite
source exponent cannot continuously extend the Hilbert ordinary flow.
-/
noncomputable section
open Set Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V B X : Set (CoeffPair p)}
  {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every nonzero real source has a nonzero first complex Birkhoff component. -/
theorem SourceBirkhoffMapComplexData.exists_complex_map_fst_ne_zero
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (φ : realTypeSourceSubmodule p) (hφ : φ ≠ 0) :
    ∃ n : ℤ, (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hφ
  apply D.complex_map_real_injective
  dsimp only
  rw [show (0 : realTypeSourceSubmodule p).val = 0 from rfl,D.complex_map_zero]
  apply Prod.ext
  · ext n; exact hn n
  · ext n
    change _ = (0 : ℂ)
    simpa only [hn n,map_zero] using D.complex_map_real φ n

namespace SourceAbelianMomentAtlas
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₂ P₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable {V₂ B₂ X₂ : Set (CoeffPair 2)} {t₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable {hq : q ≠ ⊤} {hq1 : 1 < q} {Vq Bq Xq : Set (CoeffPair q)}
  {tq : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

/-- No weaker finite-exponent source trajectory extension is continuous at a non-Hilbert source.
Only agreement on finite-gap Hilbert representatives is needed. -/
theorem not_continuousAt_ordinarySource_extension (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    (Q : SourceBirkhoffMapComplexData hq hq1 Vq Bq Xq tq)
    (h2p : 2 ≤ p) (h2q : 2 ≤ q) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q))
    (he : ∀ ψ : realTypeSourceSubmodule p, ∀ hf : ψ ∈ sourceFiniteGapLocus hp hp1,
      ∀ τ : Icc (0 : ℝ) T, F ψ τ = realTypeSourceExponentInclusion h2q
        (H.ordinarySourceFlow E le_rfl (sourceFiniteGapHilbertModel hp hp1 ψ hf) τ.val)) :
    ¬ ContinuousAt F φ := by
  intro hF
  have hne : φ ≠ 0 := by
    intro hz
    apply hφ
    rw [hz,mem_sourceHilbertLocus_iff]
    simp
  obtain ⟨n,hn⟩ := D.exists_complex_map_fst_ne_zero φ hne
  let c : C(realTypeSourceSubmodule q,ℂ) :=
    ⟨fun ψ => (sourceComplexBirkhoffMap hq hq1 tq ψ.val).1 n,
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).continuous.comp Q.continuous_complex_map_real.fst⟩
  apply A.not_continuousAt_ordinaryCoordinate_extension hs hP hr D h2p T hT φ hφ n hn
    (fun ψ => c.comp (F ψ)) (fun ψ hf => ?_)
    ((ContinuousMap.continuous_postcomp c).continuousAt.comp hF)
  apply ContinuousMap.ext
  intro τ
  change (sourceComplexBirkhoffMap hq hq1 tq (F ψ τ).val).1 n = _
  rw [he ψ hf τ]
  exact A.complex_map_hilbertOrdinaryFlow_fst hs.toSourcePsiIsolatingComplexExtension
    H hs₂ E D Q h2p h2q T ψ hf n τ

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
