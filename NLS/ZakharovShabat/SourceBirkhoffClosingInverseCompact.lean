import NLS.ZakharovShabat.NormalizedWeightedClosingCompact
import NLS.FunctionalAnalysis.CompactInverseDerivative
import NLS.ZakharovShabat.SourceBirkhoffComplexClosingInverse
import NLS.ZakharovShabat.SourceBirkhoffJacobianCompact

/-! # Compact Birkhoff remainders in actual adapted inverse charts

At every real source, actual analytic adapted inverses retain the
complex deleted-slice zeros and make the derivative of the Birkhoff map
in the chart a compact perturbation of its free Fourier transform.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open Set Filter Topology Metric
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Construct actual inverse charts with compact Birkhoff derivative remainders and complex slice zeros. -/
theorem exists_uniform_complex_closing_inverse_compact
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceLocus p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ δ : ℝ, 0 < δ ∧ ∃ g : CoeffPair p → CoeffPair p,
        AnalyticOnNhd ℂ g (ball (sourceAdaptedClosingMap hp φ.val N) δ) ∧
        g (sourceAdaptedClosingMap hp φ.val N) = φ.val ∧
        (∀ y ∈ ball (sourceAdaptedClosingMap hp φ.val N) δ,
          g y ∈ W ∧ sourceAdaptedClosingMap hp (g y) N = y) ∧
        IsCompactOperator (fderiv ℂ (fun y => sourceBirkhoffMap hp hp1 s (g y))
          (sourceAdaptedClosingMap hp φ.val N)-sourceBirkhoffFourier (p := p)) ∧
        ∃ K : ℕ, N ≤ K ∧ ∀ n : ℤ, K ≤ n.natAbs →
          ∀ y ∈ ball (sourceAdaptedClosingMap hp φ.val N) (δ/2),
            (sourceBirkhoffMap hp hp1 s (g (sourceDeleteResonance n y))).1 n = 0 ∧
            (sourceBirkhoffMap hp hp1 s (g (sourceDeleteResonance n y))).2 n = 0 := by
  obtain ⟨r,hr,Nc,hNc,hC⟩ := exists_uniform_compact_sourceAdaptedClosingMap_derivative hp hp1 φ.val
  obtain ⟨Ni,hNi,hI⟩ := D.exists_uniform_complex_closing_inverse_within φ univ isOpen_univ (mem_univ _)
  refine ⟨max Nc Ni,by omega,fun N hN => ?_⟩
  obtain ⟨δ,hδ,g,hg,hgW,hgφ,hdata,K,hNK,hzero⟩ := hI N (by omega)
  let b := sourceAdaptedClosingMap hp φ.val N
  have hb : b ∈ ball b δ := mem_ball_self hδ
  have hc := hC N (by omega)
  refine ⟨δ,hδ,g,hg,hgφ,(fun y hy => ⟨(hgW hy).2,(hdata y hy).1⟩),?_,K,hNK,hzero⟩
  apply isCompactOperator_fderiv_comp_inverse_sub (fun ψ => sourceAdaptedClosingMap hp ψ N) g
    (sourceBirkhoffMap hp hp1 s) sourceBirkhoffFourier φ.val b
    (hc.1 φ.val (mem_ball_self hr)) (hg b hb)
    (D.analytic φ.val (D.real_subset φ.property)) hgφ
  · filter_upwards [ball_mem_nhds b hδ] with y hy
    exact (hdata y hy).1
  · exact hc.2 φ.val (mem_ball_self hr)
  · exact D.isCompactOperator_jacobianRemainder_real φ
end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
