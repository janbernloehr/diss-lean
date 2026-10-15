import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic
import NLS.ZakharovShabat.SourceFullAbelianSymmetricAnalytic

/-! # Original higher actions on full Cauchy source balls

The original contour definition and symmetric boundary integral agree
throughout the entire common complex ball, for every index and level.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- An intermediate Cauchy circle has the original isolating-circle geometry. -/
def periodCircle (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (n : ℤ) (R : ℝ) (hi : C.discs.inner n ≤ R) (ho : R < C.discs.outer n) :
    SourceCriticalRootPeriodCircle hp hp1 ψ n where
  center := (C.discs.center n).re
  radius := R
  radius_pos := (C.discs.inner_pos n).trans_le hi
  gap := by
    have he : ((C.discs.center n).re : ℂ) = C.discs.center n :=
      Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real n).symm)
    rw [he]
    exact (C.discs.segment_subset ψ hψ n).trans (ball_subset_ball hi)
  other := by
    intro m hm w hw
    have hn : ((C.discs.center n).re : ℂ) = C.discs.center n :=
      Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real n).symm)
    have hm' : ((C.discs.center m).re : ℂ) = C.discs.center m :=
      Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real m).symm)
    have hd : Disjoint (ball ((C.discs.center n).re : ℂ) (C.discs.outer n))
        (ball ((C.discs.center m).re : ℂ) (C.discs.outer m)) := by
      rw [hn,hm']; exact C.discs.disjoint n m hm.symm
    have h := re_separated_of_disjoint_realCenteredBalls
      ((C.discs.inner_pos n).trans (C.discs.inner_lt n))
      ((C.discs.inner_pos m).trans (C.discs.inner_lt m)) hd
      (by rw [hm']; exact C.segment_subset_outer m ψ hψ hw)
    rcases h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

/-- The original higher action is analytic on the whole Cauchy source ball. -/
theorem analytic_indexedHigherAction (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (k : ℕ) : AnalyticOnNhd ℂ (sourceIndexedHigherAction hp hp1 n k)
      (ball C.discs.source.val C.discs.sourceRadius) := by
  let R := (C.discs.inner n + C.discs.outer n)/2
  have hi : C.discs.inner n < R := by dsimp [R]; linarith [C.discs.inner_lt n]
  have ho : R < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
  have hR : 0 < R := (C.discs.inner_pos n).trans hi
  have he : ((C.discs.center n).re : ℂ) = C.discs.center n :=
    Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real n).symm)
  have ha := analyticOnNhd_circleIntegral_of_jointAnalytic
    (fun t : ℂ × CoeffPair p => t.1^k*sourceFullAbelianPrimitive hp hp1 W 0 t)
    (C.discs.isOpen_exterior.prod isOpen_ball)
    (fun t ht => (analyticAt_fst.pow k).mul (C.full_analytic 0 t
      ⟨ht.2,(sourceAbelianProjectedDomain_end hp hp1 W (C.discs.exterior_product_subset_projected ht)).2⟩))
    (C.discs.center n) R hR.le isOpen_ball (by
      intro ψ hψ z hz
      refine ⟨C.discs.collar_subset_exterior n ?_,hψ⟩
      simp only [Set.mem_sdiff,mem_ball,mem_closedBall,not_le,mem_sphere.mp hz]
      exact ⟨ho,hi⟩)
  intro ψ hψ
  have ha' : AnalyticAt ℂ (fun χ => -(Real.pi:ℂ)⁻¹ *
      ∮ z in C(C.discs.center n,R), z^k*sourceFullAbelianPrimitive hp hp1 W 0 (z,χ)) ψ :=
    analyticAt_const.mul (ha ψ hψ)
  apply ha'.congr
  filter_upwards [isOpen_ball.mem_nhds hψ] with χ hχ
  obtain ⟨D⟩ := C.charts χ hχ
  have h := sourceIndexedHigherAction_eq_primitive (C.periodCircle χ hχ n R hi.le ho) D k 0
  simpa only [periodCircle,he] using h.symm

/-- The gap-boundary formula holds on the whole ball, without shrinking by index or level. -/
theorem indexedHigherAction_eq_boundaryIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (n : ℤ) (k : ℕ) : sourceIndexedHigherAction hp hp1 n k ψ =
      (2/Real.pi:ℂ)*∫ θ in (0:ℝ)..Real.pi,
        (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^k *
        ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*C.gapBoundary n ψ θ true) := by
  let U := ball C.discs.source.val C.discs.sourceRadius
  let G : CoeffPair p → ℂ := fun χ =>
    (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n (fun t => t.1^k*C.powerNumerator n 0 t.2 t.1) χ
  have hG : AnalyticOnNhd ℂ G U := fun χ hχ => analyticAt_const.mul
    (C.higherActionCosineMean_analytic U isOpen_ball (fun _ h => h) n k
      (C.symmetric_analytic n).1 (C.symmetric_analytic n).2 χ hχ)
  have hid := eqOn_sourceRealCenteredBalls_of_real_agreement hp
    C.discs.source C.discs.source C.discs.sourceRadius C.discs.sourceRadius
    (sourceIndexedHigherAction hp hp1 n k) G
    (C.analytic_indexedHigherAction n k).differentiableOn hG.differentiableOn (by
      intro χ hχ
      change sourceIndexedHigherAction hp hp1 n k χ.val = (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n _ χ.val
      rw [C.higherActionCosineMean_eq_boundaryIntegral]
      let R := (C.discs.inner n+C.discs.outer n)/2
      have hi : C.discs.inner n ≤ R := by dsimp [R]; linarith [C.discs.inner_lt n]
      have ho : R < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
      rw [sourceIndexedHigherAction_eq_real hp hp1 ⟨χ.val,χ.property⟩ n k,
        ← C.higherActionCircle_eq_real n k ⟨χ.val,χ.property⟩ hχ.1 R hi ho]
      by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential χ.val) (periodOnePotential_mem χ.val) n = 0
      · rw [C.higherActionCircle_eq_zero_of_collapsed n k ⟨χ.val,χ.property⟩ hχ.1 hgap R hi ho]
        simp only [C.gapBoundary_eq_zero_of_collapsed n χ.val hgap,mul_zero,intervalIntegral.integral_zero]
      · exact C.higherActionCircle_eq_boundaryIntegral n k ⟨χ.val,χ.property⟩ hχ.1 hgap R hi ho)
  exact (hid ⟨hψ,hψ⟩).trans (C.higherActionCosineMean_eq_boundaryIntegral n k ψ)
end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
