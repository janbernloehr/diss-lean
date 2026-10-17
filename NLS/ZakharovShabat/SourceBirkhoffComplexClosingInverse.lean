import NLS.ZakharovShabat.SourceBirkhoffDeletedSlice
import NLS.ZakharovShabat.SourceAdaptedClosingInverseReality

/-! # Actual complex coordinate zeros in adapted inverse charts

An actual adapted inverse maps into any prescribed source neighborhood.
Deleting the signed closing coordinates kills both original Birkhoff
coordinates throughout a common complex ball at every distant index.
The complex zero follows from real spectral closing and holomorphic uniqueness.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Actual closing inverse charts with uniformly vanishing complex deleted slices. -/
theorem exists_uniform_complex_closing_inverse_within
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceLocus p)
    (V : Set (CoeffPair p)) (hV : IsOpen V) (hφV : φ.val ∈ V) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ δ : ℝ, 0 < δ ∧ ∃ g : CoeffPair p → CoeffPair p,
        AnalyticOnNhd ℂ g (ball (sourceAdaptedClosingMap hp φ.val N) δ) ∧
        MapsTo g (ball (sourceAdaptedClosingMap hp φ.val N) δ) (V ∩ W) ∧
        g (sourceAdaptedClosingMap hp φ.val N) = φ.val ∧
        (∀ y ∈ ball (sourceAdaptedClosingMap hp φ.val N) δ,
          sourceAdaptedClosingMap hp (g y) N = y ∧
          ‖g y-φ.val‖ ≤ 2*‖y-sourceAdaptedClosingMap hp φ.val N‖) ∧
        ∃ K : ℕ, N ≤ K ∧ ∀ n : ℤ, K ≤ n.natAbs →
          ∀ y ∈ ball (sourceAdaptedClosingMap hp φ.val N) (δ/2),
            (sourceBirkhoffMap hp hp1 s (g (sourceDeleteResonance n y))).1 n = 0 ∧
            (sourceBirkhoffMap hp hp1 s (g (sourceDeleteResonance n y))).2 n = 0 := by
  obtain ⟨Kz,U,hoU,hφU,hUW,hzero⟩ := D.exists_uniform_zero_of_singleton_strip φ
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ((hoU.inter hV).mem_nhds ⟨hφU,hφV⟩)
  obtain ⟨δ₀,hδ₀,Ni,hNi,hInv⟩ := exists_uniform_real_sourceAdaptedClosingInverse hp hp1 φ.val φ.property
  obtain ⟨Nr,_,Ur,_,hφr,hReal⟩ := exists_uniform_sourceAdaptedClosingMap_realType hp hp1 φ.val
  refine ⟨max Ni Nr,by omega,?_⟩
  intro N hN
  obtain ⟨g,hg,hgφ,hdata⟩ := hInv N (by omega)
  let b := sourceAdaptedClosingMap hp φ.val N
  have hb : IsRealType (CoeffPair.toMax p b) := hReal N (by omega) φ.val hφr φ.property
  let δ := min δ₀ (ε/4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₀le : δ ≤ δ₀ := min_le_left _ _
  have hδε : δ ≤ ε/4 := min_le_right _ _
  have hsub : ball b δ ⊆ ball b δ₀ := ball_subset_ball hδ₀le
  have hgUV (y : CoeffPair p) (hy : y ∈ ball b δ) : g y ∈ U ∩ V := by
    apply hball
    rw [mem_ball,dist_eq_norm]
    have hbound := (hdata y (hsub hy)).2.1
    have hdist : ‖y-b‖ < δ := by simpa only [mem_ball,dist_eq_norm] using hy
    change ‖g y-φ.val‖ ≤ 2*‖y-b‖ at hbound
    linarith
  have hgW : MapsTo g (ball b δ) W := fun y hy => hUW (hgUV y hy).1
  obtain ⟨Kd,hdel⟩ := exists_uniform_sourceDeleteResonance_mapsTo hp b δ hδ
  refine ⟨δ,hδ,g,hg.mono hsub,(fun y hy => ⟨(hgUV y hy).2,hgW hy⟩),hgφ,
    (fun y hy => ⟨(hdata y (hsub hy)).1,(hdata y (hsub hy)).2.1⟩),
    max N (max Kz Kd),by omega,?_⟩
  intro n hn
  have hT := hdel n (by omega)
  apply D.zero_on_complex_deleted_slice ⟨b,hb⟩ (δ/2) δ (by positivity) n g (hg.mono hsub) hgW hT
  intro y hy hyReal
  have hty := hT hy
  have hi := hdata (sourceDeleteResonance n y) (hsub hty)
  have hreal := hi.2.2.1 (sourceDeleteResonance_realType n y hyReal)
  have hc := (hi.2.2.2 n (by omega)).2
    (by simp) (by simp)
  exact hzero _ (hgUV _ hty).1 hreal n (by omega) _ hc.1

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
