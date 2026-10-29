import NLS.ZakharovShabat.SourceSection10PowerContours
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! Analytic dependence of the literal Lemma 10.2 contours, on the
unchanged common source domain and with one fixed family of circles. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original common isolating circle avoids every periodic zero
simultaneously for all sources in its given neighborhood. -/
theorem SourceIsolatingNeighborhoods.discriminant_nonzero_on_sphere
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (H : SourceIsolatingNeighborhoods hp hp1 V D C)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hD : D n = ball c r) (z : ℂ) (hz : z ∈ sphere c r) :
    (canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4 ≠ 0 := by
  intro hzero
  have hspec := (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) z).mp (sub_eq_zero.mp hzero)
  obtain ⟨m,hm⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) z).mp hspec
  have hzm : z ∈ D m := hm.elim
    (fun h => h ▸ H.cluster ψ hψ m (Or.inl rfl))
    (fun h => h ▸ H.cluster ψ hψ m (Or.inr (Or.inl rfl)))
  by_cases hmn : m = n
  · subst m
    rw [hD] at hzm
    exact sphere_disjoint_ball.le_bot ⟨hz,hzm⟩
  · obtain ⟨u,s,_,hs⟩ := H.discs m
    have hopen : IsOpen (D m) := hs ▸ isOpen_ball
    have hzcl : z ∈ closure (D n) := by
      rw [hD,closure_ball _ hr.ne']
      exact sphere_subset_closedBall hz
    exact Set.disjoint_left.mp ((H.disjoint n m (Ne.symm hmn)).closure_left hopen) hzcl hzm

/-- Joint analytic integration proves analyticity of the displayed
contour directly, without using endpoint-label analyticity. -/
theorem SourceIsolatingNeighborhoods.analyticOnNhd_power_sum_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (H : SourceIsolatingNeighborhoods hp hp1 V D C)
    (hV : IsOpen V) (n : ℤ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hD : D n = ball c r) (k : ℕ) :
    AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
      (2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r),
        (2*canonicalDiscriminant hp (periodOnePotential ψ) z*
          deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          ((canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4))*z^k)) V := by
  let F : ℂ × CoeffPair p → ℂ := fun t => canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hF : AnalyticOnNhd ℂ F univ := analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  have hder : AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1) univ := by
    let ev : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1,0)
    have he : (fun t : ℂ × CoeffPair p =>
        deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1) =
        (fun t => (fderiv ℂ F t) (1,0)) := by
      funext t
      exact deriv_spectral_section_eq_fderiv F t.1 t.2 (hF t (mem_univ _)).differentiableAt
    rw [he]
    exact ev.comp_analyticOnNhd hF.fderiv
  let O : Set (ℂ × CoeffPair p) := {t | (F t)^2-4 ≠ 0}
  have hO : IsOpen O := isOpen_ne_fun
    (((continuousOn_univ.mp hF.continuousOn).pow 2).sub continuous_const) continuous_const
  let G : ℂ × CoeffPair p → ℂ := fun t =>
    (2*F t*deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1 / ((F t)^2-4))*t.1^k
  have hG : AnalyticOnNhd ℂ G O := by
    intro t ht
    exact (((analyticAt_const.mul (hF t (mem_univ _))).mul (hder t (mem_univ _))).div
      (((hF t (mem_univ _)).pow 2).sub analyticAt_const) ht).mul (analyticAt_fst.pow k)
  have hc : ∀ ψ ∈ V, ∀ z ∈ sphere c r, (z,ψ) ∈ O :=
    fun ψ hψ z hz => H.discriminant_nonzero_on_sphere ψ hψ n c r hr hD z hz
  have hraw := analyticOnNhd_circleIntegral_of_jointAnalytic G hO hG c r hr.le hV hc
  exact analyticOnNhd_const.mul hraw

/-- All indices and powers use the same fixed circle family near each
source in an existing Lemma 10.2 domain; that domain is not shrunk. -/
theorem SourceLemma10_2Data.exists_power_sum_contours
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma10_2Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ D : ℤ → Set ℂ, ∃ C : ℝ, ∃ a r : ℤ → ℝ, SourceIsolatingNeighborhoods hp hp1 V D C ∧
        ∀ n : ℤ, 0 < r n ∧ D n = ball (a n : ℂ) (r n) ∧
          (∀ ψ ∈ V, ∀ z ∈ sphere (a n : ℂ) (r n),
            (canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4 ≠ 0) ∧
          ∀ k : ℕ,
            AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
              (2*Real.pi*I : ℂ)⁻¹ * (∮ z in C((a n : ℂ),r n),
                (2*canonicalDiscriminant hp (periodOnePotential ψ) z*
                  deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
                  ((canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4))*z^k)) V ∧
            ∀ ψ ∈ V,
              (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^k+
                (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^k =
                (2*Real.pi*I : ℂ)⁻¹ * (∮ z in C((a n : ℂ),r n),
                  (2*canonicalDiscriminant hp (periodOnePotential ψ) z*
                    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
                    ((canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4))*z^k) := by
  obtain ⟨V,hVo,hVc,hφV,hVW,D,C,hD⟩ := H.isolation φ hφ
  choose a r hr hdisc using hD.discs
  refine ⟨V,hVo,hVc,hφV,hVW,D,C,a,r,hD,?_⟩
  intro n
  refine ⟨hr n,hdisc n,fun ψ hψ z hz =>
    hD.discriminant_nonzero_on_sphere ψ hψ n _ _ (hr n) (hdisc n) z hz,?_⟩
  intro k
  exact ⟨hD.analyticOnNhd_power_sum_contour hVo n _ _ (hr n) (hdisc n) k,
    fun ψ hψ => hD.power_sum_contour ψ hψ n _ _ (hr n) (hdisc n) k⟩

end NLS.ZakharovShabat
