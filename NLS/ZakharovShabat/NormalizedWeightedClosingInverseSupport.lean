import NLS.ZakharovShabat.NormalizedWeightedSourceClosing
import NLS.ZakharovShabat.NormalizedWeightedClosingInverseReality

/-! # Weighted inverse branches with a fixed spectral support bound

A finite Fourier target produces a decoded source whose actual gaps
vanish beyond that same cutoff. For real targets its unweighted adapted
coordinates are exactly the decoded target. This supplies the compatibility
needed to compare weighted and original inverse branches by uniqueness.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A weighted inverse with finite target support has the expected
unweighted adapted coordinates whenever its decoded source is closed. -/
theorem sourceAdaptedClosingMap_decode_inverse
    (hp : p ≠ ⊤) (w : SpectralWeight) (φ y : CoeffPair p) (N : ℕ)
    (hmem : ∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w
      (normalizedWeightedPeriodOne w φ) N positive) p)
    (hinv : normalizedWeightedClosingMap hp w φ N = y)
    (hy : ∀ n : ℤ, N ≤ n.natAbs → y.fst n = 0 ∧ y.snd n = 0)
    (hclosed : sourceAdaptedClosingMap hp (normalizedWeightedSource w φ) N =
      (CoeffPair.toMax p).symm
        (Coeff.truncate (Finset.Ioo (-(N : ℤ)) N) (normalizedWeightedSource w φ).fst,
         Coeff.truncate (Finset.Ioo (-(N : ℤ)) N) (normalizedWeightedSource w φ).snd)) :
    sourceAdaptedClosingMap hp (normalizedWeightedSource w φ) N = normalizedWeightedSource w y := by
  rw [hclosed]
  have hcoord := normalizedWeightedClosingMap_apply_of_mem hp w φ N hmem
  rw [hinv] at hcoord
  apply (CoeffPair.toMax p).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext <;> ext n
  · change Coeff.truncate _ (normalizedWeightedSource w φ).fst n = (normalizedWeightedSource w y).fst n
    rw [Coeff.truncate_apply, normalizedWeightedSource_fst, normalizedWeightedSource_fst]
    by_cases hn : N ≤ n.natAbs
    · have hout : n ∉ Finset.Ioo (-(N : ℤ)) N := by simp only [Finset.mem_Ioo]; omega
      rw [if_neg hout, (hy n hn).1, zero_div]
    · have hin : n ∈ Finset.Ioo (-(N : ℤ)) N := by simp only [Finset.mem_Ioo]; omega
      rw [if_pos hin]
      rw [show y.fst n = φ.fst n from by simpa only [if_neg hn] using (hcoord n).1]
  · change Coeff.truncate _ (normalizedWeightedSource w φ).snd n = (normalizedWeightedSource w y).snd n
    rw [Coeff.truncate_apply, normalizedWeightedSource_snd, normalizedWeightedSource_snd]
    by_cases hn : N ≤ n.natAbs
    · have hout : n ∉ Finset.Ioo (-(N : ℤ)) N := by simp only [Finset.mem_Ioo]; omega
      rw [if_neg hout, (hy n hn).2, zero_div]
    · have hin : n ∈ Finset.Ioo (-(N : ℤ)) N := by simp only [Finset.mem_Ioo]; omega
      rw [if_pos hin]
      rw [show y.snd n = φ.snd n from by simpa only [if_neg hn] using (hcoord n).2]

/-- Uniform real weighted inverse branches preserve a fixed closed-gap tail
and intertwine with the actual unweighted closing map on finite targets. -/
theorem exists_uniform_real_normalizedWeightedClosingInverse_support
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ g : CoeffPair p → CoeffPair p,
        AnalyticOnNhd ℂ g (ball (normalizedWeightedClosingMap hp w φ N) δ) ∧
        g (normalizedWeightedClosingMap hp w φ N) = φ ∧
        ∀ y ∈ ball (normalizedWeightedClosingMap hp w φ N) δ,
          normalizedWeightedClosingMap hp w (g y) N = y ∧
          ‖g y-φ‖ ≤ 2*‖y-normalizedWeightedClosingMap hp w φ N‖ ∧
          (IsRealType (CoeffPair.toMax p y) → IsRealType (CoeffPair.toMax p (g y))) ∧
          ((∀ n : ℤ, N ≤ n.natAbs → y.fst n = 0 ∧ y.snd n = 0) →
            (∀ n : ℤ, N ≤ n.natAbs →
              canonicalPeriodicGap hp hp1 (periodOnePotential (normalizedWeightedSource w (g y)))
                (periodOnePotential_mem (normalizedWeightedSource w (g y))) n = 0) ∧
            (IsRealType (CoeffPair.toMax p y) →
              sourceAdaptedClosingMap hp (normalizedWeightedSource w (g y)) N =
                normalizedWeightedSource w y)) := by
  obtain ⟨δ₀,hδ₀,N₀,hN₀,hI⟩ :=
    exists_uniform_real_normalizedWeightedClosingInverse hp hp1 w φ hreal
  obtain ⟨N₁,_,U₁,ho₁,hφ₁,hgap⟩ := exists_uniform_normalizedWeightedSource_closedGap hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hφ₂,htrunc⟩ :=
    exists_uniform_sourceAdaptedClosingMap_eq_truncate hp hp1 (normalizedWeightedSource w φ)
  obtain ⟨rD,hrD,N₃,_,hD⟩ := exists_fixedBall_normalizedWeightedClosingMap_derivative
    hp hp1 w φ 1 (by norm_num)
  let U := (U₁ ∩ normalizedWeightedSource w ⁻¹' U₂) ∩ ball φ (4*rD)
  have ho : IsOpen U := (ho₁.inter (ho₂.preimage (continuous_normalizedWeightedSource w))).inter isOpen_ball
  have hφ : φ ∈ U := ⟨⟨hφ₁,hφ₂⟩,mem_ball_self (by positivity)⟩
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hφ)
  let δ := min δ₀ (r/4)
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hδ₀le : δ ≤ δ₀ := min_le_left _ _
  have hδr : δ ≤ r/4 := min_le_right _ _
  refine ⟨δ,hδ,max N₀ (max N₁ (max N₂ N₃)),by omega,?_⟩
  intro N hN
  obtain ⟨g,hg,hbase,hdata⟩ := hI N (by omega)
  refine ⟨g,(fun y hy => hg y (ball_subset_ball hδ₀le hy)),hbase,?_⟩
  intro y hy
  have hd := hdata y (ball_subset_ball hδ₀le hy)
  have hgy : g y ∈ U := by
    apply hrU
    rw [mem_ball,dist_eq_norm]
    have hyδ : ‖y-normalizedWeightedClosingMap hp w φ N‖ < δ := by
      simpa only [mem_ball,dist_eq_norm] using hy
    have hb := hd.2.1
    linarith
  have hmem := ((hD N (by omega)).2.1 (g y) hgy.2).1
  refine ⟨hd.1,hd.2.1,hd.2.2.1,?_⟩
  intro hsupport
  have hclosed (n : ℤ) (hn : N ≤ n.natAbs) :
      canonicalPeriodicGap hp hp1 (periodOnePotential (normalizedWeightedSource w (g y)))
        (periodOnePotential_mem (normalizedWeightedSource w (g y))) n = 0 := by
    have hc := hd.2.2.2 n hn
    have hz : (w (2*n) : ℂ) ≠ 0 := w.toWeight.complex_ne_zero _
    have hpz := (mul_eq_zero.mp (hc.2.trans (hsupport n hn).2)).resolve_left hz
    have hmz := (mul_eq_zero.mp (hc.1.trans
      (hsupport (-n) (by simpa only [Int.natAbs_neg] using hn)).1)).resolve_left hz
    exact hgap (g y) hgy.1.1 n (by omega) hpz hmz
  refine ⟨hclosed,?_⟩
  intro hyReal
  exact sourceAdaptedClosingMap_decode_inverse hp w (g y) y N hmem hd.1 hsupport
    (htrunc _ hgy.1.2 (normalizedWeightedSource_realType w (g y) (hd.2.2.1 hyReal))
      N (by omega) hclosed)

end NLS.ZakharovShabat
