import NLS.ZakharovShabat.SourceAdaptedClosingInverse
import NLS.ZakharovShabat.SourceAdaptedClosingMapReality
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.ComplexAnalysis.NearIdentityClosedSubspaceInverse

/-!
# Real-type inverse branches of the actual adapted map

A smaller common image radius keeps every inverse source in a ball
where the actual adapted map preserves real type. Closed-subspace
inversion then proves that real targets have real inverse sources.
The actual closing equations and original-spectrum conclusions remain
valid on the same image balls for every larger cutoff.
-/

noncomputable section
open Set Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform analytic inverse branches preserve real type at a real
base source and retain the actual spectral closing implications. -/
theorem exists_uniform_real_sourceAdaptedClosingInverse
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ g : CoeffPair p → CoeffPair p,
        AnalyticOnNhd ℂ g (ball (sourceAdaptedClosingMap hp φ N) δ) ∧
        g (sourceAdaptedClosingMap hp φ N) = φ ∧
        ∀ y ∈ ball (sourceAdaptedClosingMap hp φ N) δ,
          sourceAdaptedClosingMap hp (g y) N = y ∧
          ‖g y-φ‖ ≤ 2*‖y-sourceAdaptedClosingMap hp φ N‖ ∧
          (IsRealType (CoeffPair.toMax p y) → IsRealType (CoeffPair.toMax p (g y))) ∧
          ∀ n : ℤ, N ≤ n.natAbs →
            let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne (g y)) n;
            (weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne (g y)) n ζ = y.fst (-n) ∧
              weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne (g y)) n ζ = y.snd n) ∧
            (y.fst (-n) = 0 → y.snd n = 0 →
              (∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp (periodOnePotential (g y)) ↔ z = ζ) ∧
              ∀ z ∈ resonantStrip n,
                analyticOrderNatAt (resonantDeterminantExtension hp SpectralWeight.one
                  (sourceWeightedPeriodOne (g y)) n) z = if z = ζ then 2 else 0) := by
  let K := resonantCenterRemainderBallConstant p (‖φ‖+1)
  have hK : 0 < K := resonantCenterRemainderBallConstant_pos _ (by positivity)
  obtain ⟨r,hr,N₁,hN₁,hG⟩ := exists_uniform_sourceAdaptedClosingInverse hp hp1 φ
  obtain ⟨rD,hrD,N₂,_,hD⟩ := exists_fixedBall_sourceAdaptedClosingMap_derivative hp hp1 φ (1/4) (by norm_num)
  obtain ⟨N₃,_,U,ho,hφ,hReal⟩ := exists_uniform_sourceAdaptedClosingMap_realType hp hp1 φ
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
  obtain ⟨g,hg,hgφ,hgData⟩ := hG N (by omega)
  have hd := hD N (by omega)
  have houter : ball φ R ⊆ ball φ (4*rD) := ball_subset_ball (by linarith)
  have hinner : ball φ R ⊆ ball φ (3*rD) := ball_subset_ball (by linarith)
  have hA : AnalyticOnNhd ℂ (fun ψ => sourceAdaptedClosingMap hp ψ N) (ball φ R) :=
    fun ψ hψ => hd.1 ψ (houter hψ)
  have hnear (ψ : CoeffPair p) (hψ : ψ ∈ ball φ R) :
      ‖fderiv ℂ (fun χ => sourceAdaptedClosingMap hp χ N) ψ-ContinuousLinearMap.id ℂ (CoeffPair p)‖ ≤ (1/2 : ℝ) :=
    (hd.2.2.1 ψ (hinner hψ)).le.trans (by norm_num)
  refine ⟨g,(fun y hy => hg y (ball_subset_ball hδIle hy)),hgφ,?_⟩
  intro y hy
  have hi := hgData y (ball_subset_ball hδIle hy)
  have hyδ : ‖y-sourceAdaptedClosingMap hp φ N‖ < δ := by
    simpa only [mem_ball,dist_eq_norm] using hy
  refine ⟨hi.2.1,hi.2.2.1,?_,hi.2.2.2.2⟩
  intro hyReal
  have hgy : g y ∈ ball φ R := by
    rw [mem_ball,dist_eq_norm]
    have hb := hi.2.2.1
    linarith
  exact mem_closedSubmodule_of_near_identity_inverse
    (fun ψ => sourceAdaptedClosingMap hp ψ N) φ R (R/2) (by positivity) (by linarith)
    hA hnear (realTypeSourceSubmodule p) isClosed_realTypeSourceSubmodule hreal
    (fun ψ hψ hrψ => hReal N (by omega) ψ (hRU hψ) hrψ)
    y hyReal (by linarith) (g y) hgy hi.2.1

end NLS.ZakharovShabat
