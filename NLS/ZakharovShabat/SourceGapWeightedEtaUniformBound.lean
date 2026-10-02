import NLS.ZakharovShabat.SourceGapWeightedEtaBound
import NLS.ZakharovShabat.SourceAngularEtaDiagonalBound

/-! # Index-uniform gap-weighted eta bounds near every real source

Fixed-radius tail annuli and the diagonal quotient bound control all
distant indices on one neighborhood. Analyticity controls the finite
head. A finite intersection and sum of constants prove the quantitative
estimate of Lemma 15.1 for the actual coordinates of both signs.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem exists_local_uniform_gapWeightedEtaCoordinate_bound
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (hB : IsOpen B) (hBW₀ : B ⊆ W₀)
    (φ : CoeffPair p) (hφ : φ ∈ B) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ B ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n : ℤ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ‖sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
              sourceStandardRootMidpoint hp hp1 ψ n‖) := by
  classical
  obtain ⟨Vt,hVt,hφt,hVtB,Kt,c,T,hcharts⟩ :=
    D.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives_tail
      B hB hBW₀ D.symmetric_analytic φ hφ hreal
  obtain ⟨Vq,hVq,hφq,_,Kq,M,hM,hnum⟩ :=
    D.psi.exists_local_uniform_diagonal_gapNumerator_tail_bound φ (hBW₀ hφ) hreal
  let K := max Kt Kq
  let ρ := 3*Real.pi/32
  have hrρ : Real.pi/16 < ρ := by dsimp only [ρ]; linarith [Real.pi_pos]
  have hρR : ρ < Real.pi/8 := by dsimp only [ρ]; linarith [Real.pi_pos]
  let A := 3*(Real.pi/16)*(Real.pi*ρ^2*M/(ρ-Real.pi/16)^3)
  let Ct := 4*Real.exp A
  have hCt : 0 < Ct := by dsimp only [Ct]; positivity
  have htail (ψ : CoeffPair p) (hψ : ψ ∈ Vt ∩ Vq) (n : ℤ) (hn : K < n.natAbs)
      (σ : ℂ) (hσ : ‖σ‖ ≤ 1) :
      ‖sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ‖ ≤ Ct *
        (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ +
          ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
            sourceStandardRootMidpoint hp hp1 ψ n‖) := by
    obtain ⟨hc,_,E⟩ := hcharts n ((le_max_left Kt Kq).trans_lt hn)
    have hrem : ‖sourceAngularEtaRemainder hp hp1 n s ψ‖ ≤ A := by
      apply E.norm_etaRemainder_le_of_chart_bound ψ hψ.1 ρ M hrρ hρR hM
      intro z hz
      apply hnum ψ hψ.2 n ((le_max_right Kt Kq).trans hn.le) z
      rw [← hc]
      exact mem_closedBall.mpr ((mem_sphere.mp hz).trans_le hρR.le)
    exact norm_sourceGapWeightedEtaCoordinate_le_of_remainder_bound hp hp1 n s ψ
      (((E.disc_family ψ hψ.1).contour_family.2 n).2.2.1
        (ball_subset_closedBall ((E.disc_family ψ hψ.1).dirichlet_mem_ball n))) σ hσ A hrem
  have hlocal (n : ℤ) := D.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives
    B hB hBW₀ D.symmetric_analytic φ hφ hreal n
  choose Vn cn Tn rn Rn zn hφn En using hlocal
  have hbound (n : ℤ) := (En n).exists_local_gapWeightedEtaCoordinate_bound
    ((rn n+Rn n)/2) (by linarith [(En n).inner_lt_outer])
    (by linarith [(En n).inner_lt_outer])
    ((D.roots_analytic .dirichlet n).mono (En n).source_subset) φ (hφn n)
  choose Un hUn hφUn _ Cn hCn hnBound using hbound
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ n ∈ S, ψ ∈ Un n := by
    rw [Finset.eventually_all]
    intro n _
    exact (hUn n).mem_nhds (hφUn n)
  obtain ⟨H,hHsub,hH,hφH⟩ := _root_.mem_nhds_iff.mp hevent
  let Ch := ∑ n ∈ S, Cn n
  have hCh : 0 ≤ Ch := Finset.sum_nonneg (fun n _ => (hCn n).le)
  refine ⟨(Vt ∩ Vq) ∩ H,(hVt.inter hVq).inter hH,⟨⟨hφt,hφq⟩,hφH⟩,
    (fun ψ hψ => hVtB hψ.1.1),Ct+Ch,by positivity,?_⟩
  intro ψ hψ n σ hσ
  by_cases hn : K < n.natAbs
  · exact (htail ψ hψ.1 n hn σ hσ).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCh) (by positivity))
  · have hnS : n ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hnCh : Cn n ≤ Ch := Finset.single_le_sum (fun k _ => (hCn k).le) hnS
    exact (hnBound n ψ (hHsub hψ.2 n hnS) σ hσ).trans
      (mul_le_mul_of_nonneg_right (hnCh.trans (le_add_of_nonneg_left hCt.le)) (by positivity))

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
