import NLS.ZakharovShabat.NormalizedWeightedClosingInverse
import NLS.ZakharovShabat.NormalizedWeightedClosingReality
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.ComplexAnalysis.NearIdentityClosedSubspaceInverse

/-! # Real inverse branches with full weighted norm control

The inverse displacement is measured in normalized weighted coordinates.
Real targets give real sources, and their high coefficients are exactly
the weighted moving-center closing equations.
-/

noncomputable section
open Set Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform analytic inverse branches preserve real type at a real
base source and retain the actual spectral closing implications. -/
theorem exists_uniform_real_normalizedWeightedClosingInverse
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
          ∀ n : ℤ, N ≤ n.natAbs →
            let ζ := weightedResonantDiagonalCenter hp w (normalizedWeightedPeriodOne w (g y)) n;
            (w (2*n) : ℂ)*weightedResonantBMinusExtension hp w (normalizedWeightedPeriodOne w (g y)) n ζ = y.fst (-n) ∧
            (w (2*n) : ℂ)*weightedResonantBPlusExtension hp w (normalizedWeightedPeriodOne w (g y)) n ζ = y.snd n := by
  let K := resonantCenterRemainderBallConstant p (‖φ‖+1)
  have hK : 0 < K := resonantCenterRemainderBallConstant_pos _ (by positivity)
  obtain ⟨r,hr,N₁,hN₁,_,hG⟩ := exists_uniform_normalizedWeightedClosingInverse_within
    hp hp1 w φ Set.univ isOpen_univ (mem_univ _)
  obtain ⟨rD,hrD,N₂,_,hD⟩ := exists_fixedBall_normalizedWeightedClosingMap_derivative hp hp1 w φ (1/4) (by norm_num)
  obtain ⟨N₃,_,U,ho,hφ,hReal⟩ := exists_uniform_normalizedWeightedClosingMap_realType hp hp1 w φ
  obtain ⟨s,hs,hsU⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hφ)
  let R := min rD (s/2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRD : R ≤ rD := min_le_left _ _
  have hRU : ball φ R ⊆ U := fun _ hx => hsU (ball_subset_ball
    ((min_le_right rD (s/2)).trans (by linarith)) hx)
  let δI := quantitativeInverseImageRadius r 2 (4*K)
  have hδI : 0 < δI := quantitativeInverseImageRadius_pos hr (by norm_num) (by positivity)
  let δ := min δI (R/16)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδIle : δ ≤ δI := min_le_left _ _
  have hδR : δ ≤ R/16 := min_le_right _ _
  refine ⟨δ,hδ,max N₁ (max N₂ N₃),hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  obtain ⟨hmem,g,hg,hgφ,hgData⟩ := hG N (by omega)
  have hd := hD N (by omega)
  have houter : ball φ R ⊆ ball φ (4*rD) := ball_subset_ball (by linarith)
  have hinner : ball φ R ⊆ ball φ (3*rD) := ball_subset_ball (by linarith)
  have hA : AnalyticOnNhd ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ N) (ball φ R) :=
    fun ψ hψ => hd.1 ψ (houter hψ)
  have hnear (ψ : CoeffPair p) (hψ : ψ ∈ ball φ R) :
      ‖fderiv ℂ (fun χ => normalizedWeightedClosingMap hp w χ N) ψ-ContinuousLinearMap.id ℂ (CoeffPair p)‖ ≤ (1/2 : ℝ) :=
    (hd.2.2.1 ψ (hinner hψ)).le.trans (by norm_num)
  refine ⟨g,(fun y hy => hg y (ball_subset_ball hδIle hy)),hgφ,?_⟩
  intro y hy
  have hi := hgData y (ball_subset_ball hδIle hy)
  have hyδ : ‖y-normalizedWeightedClosingMap hp w φ N‖ < δ := by
    simpa only [mem_ball,dist_eq_norm] using hy
  have hρ : quantitativeInverseJointRadius r 2 (4*K) < r :=
    (min_le_left _ _).trans_lt (half_lt_self hr)
  have hc := normalizedWeightedClosingInverse_coefficients hp w (g y) y N
    (hmem (g y) (ball_subset_ball hρ.le hi.1)) hi.2.1
  refine ⟨hi.2.1,hi.2.2.1,?_,hc⟩
  intro hyReal
  have hgy : g y ∈ ball φ R := by
    rw [mem_ball,dist_eq_norm]
    have hb := hi.2.2.1
    linarith
  exact mem_closedSubmodule_of_near_identity_inverse
    (fun ψ => normalizedWeightedClosingMap hp w ψ N) φ R (R/2) (by positivity) (by linarith)
    hA hnear (realTypeSourceSubmodule p) isClosed_realTypeSourceSubmodule hreal
    (fun ψ hψ hrψ => hReal N (by omega) ψ (hRU hψ) hrψ)
    y hyReal (by linarith) (g y) hgy hi.2.1

end NLS.ZakharovShabat
