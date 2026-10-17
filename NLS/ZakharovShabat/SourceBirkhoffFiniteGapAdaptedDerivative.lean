import NLS.ZakharovShabat.SourceBirkhoffClosingInverseCompact
import NLS.ZakharovShabat.SourceFiniteGapAdaptedCoordinates
import NLS.ZakharovShabat.SourceDeletedSliceDerivative
import NLS.ZakharovShabat.SourceCompactSignedEntries

/-! # Exact finite-gap derivative blocks in actual adapted charts

At a finite-gap source, sufficiently distant adapted coordinates vanish.
The complex deleted-slice identity then makes each distant derivative row
depend on precisely its two signed source modes. Compactness makes all four
entries of the difference from the free Fourier block tend uniformly to
zero. The inverse chart, cutoff, and bounds are constructed from the actual
Birkhoff map, for every finite exponent strictly above one.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Actual finite-gap inverse charts have exact two-mode derivative rows,
a compact Fourier remainder, and uniformly vanishing remainder entries. -/
theorem exists_uniform_finiteGap_adapted_derivative_blocks
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceLocus p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ δ : ℝ, 0 < δ ∧ ∃ g : CoeffPair p → CoeffPair p,
        AnalyticOnNhd ℂ g (ball (sourceAdaptedClosingMap hp φ.val N) δ) ∧
        g (sourceAdaptedClosingMap hp φ.val N) = φ.val ∧
        (∀ y ∈ ball (sourceAdaptedClosingMap hp φ.val N) δ,
          g y ∈ W ∧ sourceAdaptedClosingMap hp (g y) N = y) ∧
        let L := fderiv ℂ (fun y => sourceBirkhoffMap hp hp1 s (g y)) (sourceAdaptedClosingMap hp φ.val N)
        let R := L-sourceBirkhoffFourier (p := p)
        IsCompactOperator R ∧ ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, N ≤ K ∧ ∀ n : ℤ, K ≤ n.natAbs →
          (∀ a : CoeffPair p,
            (L a).1 n = a.fst (-n)*(L (CoeffPair.inlCLM (lp.single p (-n) (1:ℂ)))).1 n+
              a.snd n*(L (CoeffPair.inrCLM (lp.single p n (1:ℂ)))).1 n ∧
            (L a).2 n = a.fst (-n)*(L (CoeffPair.inlCLM (lp.single p (-n) (1:ℂ)))).2 n+
              a.snd n*(L (CoeffPair.inrCLM (lp.single p n (1:ℂ)))).2 n) ∧
          ‖(R (CoeffPair.inlCLM (lp.single p (-n) (1:ℂ)))).1 n‖ < ε ∧
          ‖(R (CoeffPair.inlCLM (lp.single p (-n) (1:ℂ)))).2 n‖ < ε ∧
          ‖(R (CoeffPair.inrCLM (lp.single p n (1:ℂ)))).1 n‖ < ε ∧
          ‖(R (CoeffPair.inrCLM (lp.single p n (1:ℂ)))).2 n‖ < ε := by
  obtain ⟨Nf,hNf,htrunc⟩ := sourceAdaptedClosingMap_eq_truncate_of_finiteGap hp hp1 φ hfinite
  obtain ⟨Ni,hNi,hInv⟩ := D.exists_uniform_complex_closing_inverse_compact φ
  refine ⟨max Nf Ni,by omega,fun N hN => ?_⟩
  obtain ⟨δ,hδ,g,hg,hgφ,hdata,hcompact,K,hNK,hzero⟩ := hInv N (by omega)
  let b := sourceAdaptedClosingMap hp φ.val N
  have hb : b ∈ ball b δ := mem_ball_self hδ
  have hF : AnalyticAt ℂ (fun y => sourceBirkhoffMap hp hp1 s (g y)) b :=
    (D.analytic _ (hdata b hb).1).comp (hg b hb)
  refine ⟨δ,hδ,g,hg,hgφ,hdata,hcompact,fun ε hε => ?_⟩
  obtain ⟨Kε,hεtail⟩ := exists_compactOperator_signed_block_entries_small hp _ hcompact ε hε
  refine ⟨max K Kε,by omega,fun n hn => ⟨?_,hεtail n (by omega)⟩⟩
  intro a
  have hbase : b.fst (-n) = 0 ∧ b.snd n = 0 := by
    dsimp [b]
    rw [htrunc N (by omega)]
    constructor
    · change Coeff.truncate (Finset.Ioo (-(N:ℤ)) N) φ.val.fst (-n) = 0
      rw [Coeff.truncate_apply,if_neg (by simp only [Finset.mem_Ioo]; omega)]
    · change Coeff.truncate (Finset.Ioo (-(N:ℤ)) N) φ.val.snd n = 0
      rw [Coeff.truncate_apply,if_neg (by simp only [Finset.mem_Ioo]; omega)]
  apply fderiv_coordinate_rows_of_deleted_zero _ b n hF hbase _ a
  filter_upwards [ball_mem_nhds b (half_pos hδ)] with y hy
  exact hzero n (by omega) y hy

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
