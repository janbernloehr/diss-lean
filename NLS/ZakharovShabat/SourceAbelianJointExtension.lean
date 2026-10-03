import NLS.ZakharovShabat.SourceAbelianSourceContinuity

/-! # Actual joint abelian integral charts at every point off the cuts

Continuity of the normalized real-source value fixes the local
logarithm at every spectral anchor. Its normalization then agrees
with the actual primitive on every nearby real-source slice of one
product neighborhood. The charts retain the exact joint differential.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At every spectral anchor off the cuts, joint analytic charts
extend the actual normalized primitive for every nearby real source.
One product neighborhood works for all signed normalization indices. -/
theorem exists_sourceAbelianLogChart_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (a : ℂ)
    (ha : a ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t ∈ Metric.ball a r ×ˢ Metric.ball φ.val r,
        t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2) ∧
      ∀ n : ℤ,
        AnalyticOnNhd ℂ (sourceAbelianLogChart hp hp1 φ.val φ.property a n)
          (Metric.ball a r ×ˢ Metric.ball φ.val r) ∧
        (∀ t ∈ Metric.ball a r ×ˢ Metric.ball φ.val r,
          HasFDerivAt (sourceAbelianLogChart hp hp1 φ.val φ.property a n)
            ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
              fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t) ∧
        ∀ (ψ : realTypeSourceSubmodule p), ψ.val ∈ Metric.ball φ.val r →
          ∀ z ∈ Metric.ball a r,
            sourceAbelianLogChart hp hp1 φ.val φ.property a n (z,ψ.val) =
              sourceAbelianPrimitive hp hp1 ψ.val ψ.property z+I*(Real.pi : ℂ)*n := by
  obtain ⟨V,hV,hbase,hroot,hcharts⟩ := exists_sourceAbelianLogChart_joint_neighborhood
    hp hp1 φ.val φ.property a ha
  obtain ⟨R,hR,hRV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hbase)
  let F := fun ψ : realTypeSourceSubmodule p => sourceAbelianPrimitive hp hp1 ψ.val ψ.property a
  let M := fun ψ : realTypeSourceSubmodule p => sourceFloquetMultiplier hp hp1 ψ.val a
  have heExp : (fun ψ => exp (F ψ)) =ᶠ[𝓝 φ] M := by
    have hm : Continuous (fun ψ : realTypeSourceSubmodule p => (a,ψ.val)) :=
      continuous_const.prodMk continuous_subtype_val
    filter_upwards [(hm.continuousAt (x := φ)).tendsto.eventually (hV.mem_nhds hbase)] with ψ hψ
    exact sourceAbelianPrimitive_exp hp hp1 ψ.val ψ.property a
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ.val (hroot (a,ψ.val) hψ))
  have heLog := normalizedLogChart_eventually_eq M F φ
    (continuousAt_sourceAbelianPrimitive_source hp hp1 φ a ha) heExp
  have he : ∀ᶠ ψ : realTypeSourceSubmodule p in 𝓝 φ, ∀ n : ℤ,
      sourceAbelianLogChart hp hp1 φ.val φ.property a n (a,ψ.val) = F ψ+I*(Real.pi : ℂ)*n := by
    filter_upwards [heLog] with ψ hψ
    intro n
    change F φ+log (M ψ/M φ) = F ψ at hψ
    change (F φ+I*(Real.pi : ℂ)*n)+log (M ψ/M φ) = F ψ+I*(Real.pi : ℂ)*n
    linear_combination hψ
  obtain ⟨δ,hδ,hδeq⟩ := Metric.mem_nhds_iff.mp he
  let r := min R δ
  have hr : 0 < r := lt_min hR hδ
  have hsub : Metric.ball a r ×ˢ Metric.ball φ.val r ⊆ V := by
    rw [ball_prod_same]
    exact (Metric.ball_subset_ball (min_le_left R δ)).trans hRV
  refine ⟨r,hr,fun t ht => hroot t (hsub ht),?_⟩
  intro n
  refine ⟨(hcharts n).1.mono hsub,fun t ht => (hcharts n).2 t (hsub ht),?_⟩
  intro ψ hψ
  have hψδ : ψ ∈ Metric.ball φ δ :=
    lt_of_lt_of_le hψ (min_le_right R δ)
  have heq : sourceAbelianLogChart hp hp1 φ.val φ.property a n (a,ψ.val) =
      sourceAbelianPrimitive hp hp1 ψ.val ψ.property a+I*(Real.pi : ℂ)*n := hδeq hψδ n
  have hd (z : ℂ) (hz : z ∈ Metric.ball a r) :
      DifferentiableAt ℂ (fun w : ℂ => sourceAbelianLogChart hp hp1 φ.val φ.property a n (w,ψ.val)) z := by
    have hc := ((hcharts n).1 (z,ψ.val) (hsub ⟨hz,hψ⟩)).differentiableAt
    simpa only [Function.comp_def] using! hc.comp z (differentiableAt_id.prodMk (differentiableAt_const ψ.val))
  have hF (z : ℂ) (hz : z ∈ Metric.ball a r) :=
    (sourceAbelianPrimitive_hasDerivAt_quotient hp hp1 ψ.val ψ.property z
      (hroot (z,ψ.val) (hsub ⟨hz,hψ⟩))).add_const (I*(Real.pi : ℂ)*n)
  apply Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball a r).isPreconnected
    (fun z hz => (hd z hz).differentiableWithinAt)
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => ?_) (Metric.mem_ball_self hr) heq
  rw [(hF z hz).deriv]
  exact sourceAbelianLogChart_spectral_deriv hp hp1 φ.val φ.property a n z ψ.val
    (by simpa only using! (hcharts n).2 (z,ψ.val) (hsub ⟨hz,hψ⟩))

/-- The actual normalized primitive is jointly continuous in complex
spectral coordinate and real source at every point off the cuts. -/
theorem continuousAt_sourceAbelianPrimitive_joint_real_source
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (a : ℂ)
    (ha : a ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    ContinuousAt (fun t : ℂ × realTypeSourceSubmodule p =>
      sourceAbelianPrimitive hp hp1 t.2.val t.2.property t.1) (a,φ) := by
  obtain ⟨r,hr,_,hcharts⟩ := exists_sourceAbelianLogChart_product hp hp1 φ a ha
  have hm : Continuous (fun t : ℂ × realTypeSourceSubmodule p => (t.1,t.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hbase : (a,φ.val) ∈ Metric.ball a r ×ˢ Metric.ball φ.val r :=
    ⟨Metric.mem_ball_self hr,Metric.mem_ball_self hr⟩
  have hc : ContinuousAt (fun t : ℂ × realTypeSourceSubmodule p =>
      sourceAbelianLogChart hp hp1 φ.val φ.property a 0 (t.1,t.2.val)) (a,φ) := by
    simpa only [Function.comp_def] using!
      (((hcharts 0).1 (a,φ.val) hbase).continuousAt.comp
        (f := fun t : ℂ × realTypeSourceSubmodule p => (t.1,t.2.val))
        (hm.continuousAt (x := (a,φ))))
  apply hc.congr_of_eventuallyEq
  have hb := (hm.continuousAt (x := (a,φ))).tendsto.eventually
    ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hbase)
  filter_upwards [hb] with t ht
  simpa only [Int.cast_zero,mul_zero,add_zero] using
    ((hcharts 0).2.2 t.2 ht.2 t.1 ht.1).symm

end NLS.ZakharovShabat
