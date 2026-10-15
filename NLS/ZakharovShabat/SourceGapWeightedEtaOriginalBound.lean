import NLS.ZakharovShabat.SourceAngularOriginalDiagonalBound
import NLS.ZakharovShabat.SourceAngularOriginalAnnulusTail
import NLS.ZakharovShabat.SourceGapWeightedEtaOriginal
import NLS.ZakharovShabat.SourceGapWeightedEtaBound

/-!
# Lemma 15.1's estimate on the original complex domain

Fixed tail annuli and the original diagonal estimate control every distant
index. Finitely many selected annulus charts handle the head. The same
neighborhood and constant work for all indices and signs of norm at most one.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The original tail annuli give one bound for all distant indices and both signs. -/
theorem gapWeighted_original_tail_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n : ℤ, K < n.natAbs →
        ∀ σ : ℂ, ‖σ‖ ≤ 1 → ‖sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
              sourceStandardRootMidpoint hp hp1 ψ n‖) := by
  obtain ⟨Vt,hVt,hφt,hVtW,Kt,c,T,hcharts⟩ := H.angular_original_annulus_tail φ hφ
  obtain ⟨Vd,hVd,hφd,_,D,Cd,hD,_⟩ := H.angular_original_disks φ hφ
  obtain ⟨Vq,hVq,hφq,_,M,hM,hnum⟩ := angular_original_diagonal_bound H hD hVd φ hφ hφd
  obtain ⟨Kd,htail⟩ := hD.tail
  let K := max Kt Kd
  let ρ := 3*Real.pi/32
  have hrρ : Real.pi/16 < ρ := by dsimp only [ρ]; linarith [Real.pi_pos]
  have hρR : ρ < Real.pi/8 := by dsimp only [ρ]; linarith [Real.pi_pos]
  let A := 3*(Real.pi/16)*(Real.pi*ρ^2*M/(ρ-Real.pi/16)^3)
  refine ⟨Vt ∩ Vq,hVt.inter hVq,⟨hφt,hφq⟩,inter_subset_left.trans hVtW,
    K,4*Real.exp A,by positivity,?_⟩
  intro ψ hψ n hn σ hσ
  obtain ⟨hc,_,E⟩ := hcharts n ((le_max_left Kt Kd).trans_lt hn)
  have hrem : ‖sourceAngularEtaRemainder hp hp1 n s ψ‖ ≤ A := by
    apply E.norm_etaRemainder_le_of_chart_bound ψ hψ.1 ρ M hrρ hρR hM
    intro z hz
    apply hnum ψ hψ.2 n z
    rw [htail n ((le_max_right Kt Kd).trans_lt hn)]
    change z ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4)
    rw [← hc]
    exact mem_ball.mpr ((mem_sphere.mp hz).trans_lt (by dsimp only [ρ]; linarith [Real.pi_pos]))
  exact norm_sourceGapWeightedEtaCoordinate_le_of_remainder_bound hp hp1 n s ψ
    (((E.disc_family ψ hψ.1).contour_family.2 n).2.2.1
      (ball_subset_closedBall ((E.disc_family ψ hψ.1).dirichlet_mem_ball n))) σ hσ A hrem

/-- Lemma 15.1: one local bound for all indices at every complex source in the original W. -/
theorem gapWeighted_original_uniform_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n : ℤ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ‖sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
              sourceStandardRootMidpoint hp hp1 ψ n‖) := by
  classical
  obtain ⟨Ut,hUt,hφt,hUtW,K,Ct,hCt,htail⟩ := gapWeighted_original_tail_bound H φ hφ
  choose Vn cn Tn rn Rn zn hφn En _ _ using H.angular_original_annulus_chart φ hφ
  have hbound (n : ℤ) := (En n).exists_local_gapWeightedEtaCoordinate_bound
    ((rn n+Rn n)/2) (by linarith [(En n).inner_lt_outer])
    (by linarith [(En n).inner_lt_outer])
    ((H.original_theta_common_domain.roots_analytic .dirichlet n).mono (En n).source_subset) φ (hφn n)
  choose Un hUn hφUn _ Cn hCn hnBound using hbound
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ n ∈ S, ψ ∈ Un n := by
    rw [Finset.eventually_all]
    intro n _
    exact (hUn n).mem_nhds (hφUn n)
  obtain ⟨Z,hZsub,hZ,hφZ⟩ := _root_.mem_nhds_iff.mp hevent
  let Ch := ∑ n ∈ S, Cn n
  have hCh : 0 ≤ Ch := Finset.sum_nonneg (fun n _ => (hCn n).le)
  refine ⟨Ut ∩ Z,hUt.inter hZ,⟨hφt,hφZ⟩,inter_subset_left.trans hUtW,Ct+Ch,by positivity,?_⟩
  intro ψ hψ n σ hσ
  by_cases hn : K < n.natAbs
  · exact (htail ψ hψ.1 n hn σ hσ).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCh) (by positivity))
  · have hnS : n ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hnCh : Cn n ≤ Ch := Finset.single_le_sum (fun k _ => (hCn k).le) hnS
    exact (hnBound n ψ (hZsub hψ.2 n hnS) σ hσ).trans
      (mul_le_mul_of_nonneg_right (hnCh.trans (le_add_of_nonneg_left hCt.le)) (by positivity))

end SourceLemma12_12Data
end NLS.ZakharovShabat
