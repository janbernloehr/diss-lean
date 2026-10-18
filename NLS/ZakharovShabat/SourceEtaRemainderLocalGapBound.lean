import NLS.ZakharovShabat.SourceBirkhoffMapAnalytic
import NLS.ZakharovShabat.SourceAngularEtaRemainderBound
import NLS.ZakharovShabat.SourceAngularEtaDiagonalBound

/-! # Local gap bounds for the actual eta remainder

Analytic terminal evaluation bounds each finite central chart. Fixed
tail annuli and the diagonal numerator bound then give one constant for
all indices on a complex neighborhood of each real source, at every
finite source exponent greater than one.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceAngularJointAnnulusChartData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The actual eta remainder is locally bounded by its terminal displacement and half gap. -/
theorem exists_local_etaRemainder_gap_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) V)
    (φ : CoeffPair p) (hφ : φ ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U,
        ‖sourceAngularEtaRemainder hp hp1 n s ψ‖ ≤ C*
          (‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-sourceStandardRootMidpoint hp hp1 ψ n‖+
            ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖/2) := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  let F : CoeffPair p → ℂ := fun ψ =>
    sourceAngularEtaQuotientCauchyCandidate hp hp1 n s (c n) r R z₀ ρ (μ ψ,ψ)
  have hterminal : μ φ ∈ ball (c n) ρ := ball_subset_ball hrρ.le (D.terminal_enclosed φ hφ)
  have hF : AnalyticAt ℂ F φ :=
    (D.analyticOnNhd_etaQuotientCauchyCandidate ρ hrρ hρR (μ φ,φ) ⟨hterminal,hφ⟩).comp
      (x := φ) (f := fun ψ : CoeffPair p => (μ ψ,ψ)) ((hμ φ hφ).prod analyticAt_id)
  let C := ‖F φ‖+1
  have hevent : ∀ᶠ ψ in 𝓝 φ, ‖F ψ‖ < C :=
    hF.continuousAt.norm.eventually (gt_mem_nhds (by dsimp only [C]; linarith))
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp hevent
  refine ⟨U ∩ V,hU.inter D.source_open,⟨hφU,hφ⟩,inter_subset_right,C,by dsimp [C]; positivity,?_⟩
  intro ψ hψ
  rw [D.etaRemainder_eq_cauchyCandidate ρ hrρ hρR ψ hψ.2]
  dsimp only [sourceAngularEtaRemainderCauchyCandidate]
  rw [norm_mul]
  have hb := norm_sourceDirichletRootCoefficient_le hp hp1 ψ n
    (((D.disc_family ψ hψ.2).contour_family.2 n).2.2.1
      (ball_subset_closedBall ((D.disc_family ψ hψ.2).dirichlet_mem_ball n)))
  have hbound := mul_le_mul hb (hUsub hψ.1).le (norm_nonneg (F ψ)) (by positivity)
  simpa only [mul_comm] using hbound

end NLS.ZakharovShabat.SourceAngularJointAnnulusChartData

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- The retained original family has one local eta-remainder gap bound at every real source. -/
theorem exists_local_uniform_etaRemainder_gap_bound
    (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        ‖sourceAngularEtaRemainder hp hp1 n s ψ‖ ≤ C*
          (‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-sourceStandardRootMidpoint hp hp1 ψ n‖+
            ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖/2) := by
  classical
  obtain ⟨a,ha,_,_,_,_,hball,_⟩ := D.angular.psi.isolation φ
  let O := W ∩ ball φ.val a
  have hO : IsOpen O := D.source_open.inter isOpen_ball
  have hφO : φ.val ∈ O := ⟨D.real_subset φ.property,mem_ball_self ha⟩
  have hOW₀ : O ⊆ W₀ := fun _ h => hball h.2
  have hOB : O ⊆ B := fun _ h => D.source_subset h.1
  have hsym : ∀ ψ ∈ O, ∀ n : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) n)^2) ψ :=
    fun ψ hψ => D.angular.symmetric_analytic ψ (hOB hψ)
  obtain ⟨Vt,hVt,hφt,hVtO,Kt,c,T,hcharts⟩ :=
    D.angular.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives_tail
      O hO hOW₀ hsym φ.val hφO φ.property
  obtain ⟨Vq,hVq,hφq,_,Kq,M,hM,hnum⟩ :=
    D.angular.psi.exists_local_uniform_diagonal_gapNumerator_tail_bound φ.val (hOW₀ hφO) φ.property
  let K := max Kt Kq
  let ρ := 3*Real.pi/32
  have hrρ : Real.pi/16 < ρ := by dsimp only [ρ]; linarith [Real.pi_pos]
  have hρR : ρ < Real.pi/8 := by dsimp only [ρ]; linarith [Real.pi_pos]
  let Ct := Real.pi*ρ^2*M/(ρ-Real.pi/16)^3
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have htail (ψ : CoeffPair p) (hψ : ψ ∈ Vt ∩ Vq) (n : ℤ) (hn : K < n.natAbs) :
      ‖sourceAngularEtaRemainder hp hp1 n s ψ‖ ≤ Ct*
        (‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-sourceStandardRootMidpoint hp hp1 ψ n‖+
          ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖/2) := by
    obtain ⟨hc,_,E⟩ := hcharts n ((le_max_left Kt Kq).trans_lt hn)
    have h := E.norm_etaRemainder_le_of_gapNumerator_bound ψ hψ.1 ρ M hrρ hρR hM (by
      intro z hz
      apply hnum ψ hψ.2 n ((le_max_right Kt Kq).trans hn.le) z
      rw [← hc]
      exact mem_closedBall.mpr ((mem_sphere.mp hz).trans_le hρR.le))
    simpa only [Ct,mul_comm] using h
  have hlocal (n : ℤ) := D.angular.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives
    O hO hOW₀ hsym φ.val hφO φ.property n
  choose Vn cn Tn rn Rn zn hφn En using hlocal
  have hbound (n : ℤ) := (En n).exists_local_etaRemainder_gap_bound
    ((rn n+Rn n)/2) (by linarith [(En n).inner_lt_outer])
    (by linarith [(En n).inner_lt_outer])
    ((D.angular.roots_analytic .dirichlet n).mono ((En n).source_subset.trans hOB)) φ.val (hφn n)
  choose Un hUn hφUn _ Cn hCn hnBound using hbound
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ.val, ∀ n ∈ S, ψ ∈ Un n := by
    rw [Finset.eventually_all]
    intro n _
    exact (hUn n).mem_nhds (hφUn n)
  obtain ⟨H,hHsub,hH,hφH⟩ := _root_.mem_nhds_iff.mp hevent
  let Ch := ∑ n ∈ S, Cn n
  have hCh : 0 ≤ Ch := Finset.sum_nonneg (fun n _ => (hCn n).le)
  refine ⟨(Vt ∩ Vq) ∩ H,(hVt.inter hVq).inter hH,⟨⟨hφt,hφq⟩,hφH⟩,
    (fun ψ hψ => (hVtO hψ.1.1).1),Ct+Ch,add_nonneg hCt hCh,?_⟩
  intro ψ hψ n
  by_cases hn : K < n.natAbs
  · exact (htail ψ hψ.1 n hn).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCh) (by positivity))
  · have hnS : n ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hnCh : Cn n ≤ Ch := Finset.single_le_sum (fun k _ => (hCn k).le) hnS
    exact (hnBound n ψ (hHsub hψ.2 n hnS)).trans
      (mul_le_mul_of_nonneg_right (hnCh.trans (le_add_of_nonneg_left hCt)) (by positivity))

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
