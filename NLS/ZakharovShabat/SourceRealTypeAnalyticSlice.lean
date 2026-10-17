import NLS.ZakharovShabat.SourceRealTypeIdentity

/-! # Holomorphic vanishing after a linear source projection

A real slice determines a holomorphic observation after an analytic change
of source coordinates and a bounded linear projection. The result is uniform
on the whole connected ball, rather than just a germ at its center.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem analytic_observation_comp_linear
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : E → F) (g : E → E) (T : E →L[ℂ] E) (L : F →L[ℂ] G)
    (U V W : Set E) (hf : AnalyticOnNhd ℂ f W) (hg : AnalyticOnNhd ℂ g V)
    (hgW : MapsTo g V W) (hT : MapsTo T U V) :
    AnalyticOnNhd ℂ (fun y => L (f (g (T y)))) U := by
  intro y hy
  exact (L.analyticAt _).comp (f := fun z => f (g (T z)))
    ((hf _ (hgW (hT hy))).comp (f := fun z => g (T z))
      ((hg _ (hT hy)).compContinuousLinearMap (u := T)))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Real vanishing of a projected analytic observation implies complex vanishing. -/
theorem eqOn_zero_of_realType_projected_observation
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (hp : p ≠ ⊤) (b : realTypeSourceLocus p) (r : ℝ) (hr : 0 < r)
    (f : CoeffPair p → F) (g : CoeffPair p → CoeffPair p)
    (T : CoeffPair p →L[ℂ] CoeffPair p) (L : F →L[ℂ] G)
    (V W : Set (CoeffPair p)) (hf : AnalyticOnNhd ℂ f W) (hg : AnalyticOnNhd ℂ g V)
    (hgW : MapsTo g V W) (hT : MapsTo T (ball b.val r) V)
    (hzero : ∀ y ∈ ball b.val r, IsRealType (CoeffPair.toMax p y) → L (f (g (T y))) = 0) :
    ∀ y ∈ ball b.val r, L (f (g (T y))) = 0 := by
  exact sourceLemmaE2_realType hp (ball b.val r) isOpen_ball (isConnected_ball hr)
    ⟨b.val,mem_ball_self hr,b.property⟩ (fun y => L (f (g (T y))))
    (analytic_observation_comp_linear f g T L (ball b.val r) V W hf hg hgW hT)
    (fun _ hy => hzero _ hy.1 hy.2)

end NLS.ZakharovShabat
