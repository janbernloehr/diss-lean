import NLS.KdV.HillHminusOneRealGapRoot

/-! # Actual upper and lower real-gap primitive boundary values

The physical half-plane signs and continuity of the filled square give
the boundary values at every point of the closed gap. Endpoints and
collapsed gaps are included, with no division by the gap length.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem tendsto_hillHminusShiftedPrimitive_sqrt_boundaries
    (n : ℕ+) (r : ℝ) (V : Set PeriodOneHminusOne)
    (K : ℂ × PeriodOneHminusOne → ℂ)
    (hK : AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V))
    (hmatch : ∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
      K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2)
    (q : PeriodOneHminusOne) (hqV : q ∈ V) (hq : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : (x : ℂ) ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r))
    (hcont : ContinuousAt Complex.sqrt (K ((x : ℂ),q))) :
    Tendsto (fun y : ℝ => hillHminusContinuedPrimitive ((x : ℂ)+(y : ℂ)*I,q)+I*(n : ℂ)*Real.pi)
      (𝓝[>] 0) (𝓝 (Complex.sqrt (K ((x : ℂ),q)))) ∧
    Tendsto (fun y : ℝ => hillHminusContinuedPrimitive ((x : ℂ)-(y : ℂ)*I,q)+I*(n : ℂ)*Real.pi)
      (𝓝[>] 0) (𝓝 (-Complex.sqrt (K ((x : ℂ),q)))) := by
  have hc : ContinuousAt (fun z : ℂ => Complex.sqrt (K (z,q))) (x : ℂ) :=
    hcont.comp (f := fun z : ℂ => K (z,q)) (((hK ((x : ℂ),q) ⟨ball_subset_closedBall hx,hqV⟩).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)).continuousAt)
  constructor
  · have hp : Tendsto (fun y : ℝ => (x : ℂ)+(y : ℂ)*I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have hh : ContinuousAt (fun y : ℝ => (x : ℂ)+(y : ℂ)*I) 0 := by fun_prop
      simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
    have he : (fun y : ℝ => hillHminusContinuedPrimitive ((x : ℂ)+(y : ℂ)*I,q)+I*(n : ℂ)*Real.pi)
        =ᶠ[𝓝[>] 0] (fun y => Complex.sqrt (K ((x : ℂ)+(y : ℂ)*I,q))) := by
      filter_upwards [hp.eventually (isOpen_ball.mem_nhds hx),self_mem_nhdsWithin] with y hy hypos
      change 0 < y at hypos
      have him : 0 < ((x : ℂ)+(y : ℂ)*I).im := by simpa using hypos
      apply hillHminusShiftedPrimitive_eq_principalSqrt q hq n _ _ him
      exact (hmatch ((x : ℂ)+(y : ℂ)*I,q) ⟨⟨ball_subset_closedBall hy,hqV⟩,
        mem_hillHminusContinuationDomain_of_im_ne_zero q hq _ him.ne'⟩).symm
    exact (hc.tendsto.comp hp).congr' he.symm
  · have hp : Tendsto (fun y : ℝ => (x : ℂ)-(y : ℂ)*I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have hh : ContinuousAt (fun y : ℝ => (x : ℂ)-(y : ℂ)*I) 0 := by fun_prop
      simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
    have he : (fun y : ℝ => hillHminusContinuedPrimitive ((x : ℂ)-(y : ℂ)*I,q)+I*(n : ℂ)*Real.pi)
        =ᶠ[𝓝[>] 0] (fun y => -Complex.sqrt (K ((x : ℂ)-(y : ℂ)*I,q))) := by
      filter_upwards [hp.eventually (isOpen_ball.mem_nhds hx),self_mem_nhdsWithin] with y hy hypos
      change 0 < y at hypos
      have him : ((x : ℂ)-(y : ℂ)*I).im < 0 := by simpa using (show -y < 0 by linarith)
      apply hillHminusShiftedPrimitive_eq_neg_principalSqrt q hq n _ _ him
      exact (hmatch ((x : ℂ)-(y : ℂ)*I,q) ⟨⟨ball_subset_closedBall hy,hqV⟩,
        mem_hillHminusContinuationDomain_of_im_ne_zero q hq _ him.ne⟩).symm
    exact (hc.neg.tendsto.comp hp).congr' he.symm

/-- The exact normalized endpoint profile is the boundary value of the
ACTUAL source primitive on BOTH sides of the entire actual real gap. -/
theorem tendsto_hillHminusShiftedPrimitive_real_gap_boundaries
    (n : ℕ+) (r epsilon : ℝ) (hr : 0 < r) (hepsilon : epsilon < 1)
    (V : Set PeriodOneHminusOne) (K : ℂ × PeriodOneHminusOne → ℂ)
    (hK : AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V))
    (hmatch : ∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
      K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2)
    (q : PeriodOneHminusOne) (hqV : q ∈ V) (hq : IsRealPeriodOneHminusOne q) (l u : ℝ)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ ≤ epsilon)
    (x : ℝ) (hx : x ∈ Icc l u) :
    let B := (((Real.sqrt ((x-l)*(u-x))/(2*(Real.pi*(n : ℕ))) : ℝ) : ℂ)) *
      hillHminusJointNormalizedGapRoot n r K ((x : ℂ),q)
    Tendsto (fun y : ℝ => hillHminusContinuedPrimitive ((x : ℂ)+(y : ℂ)*I,q)+I*(n : ℂ)*Real.pi)
      (𝓝[>] 0) (𝓝 B) ∧
    Tendsto (fun y : ℝ => hillHminusContinuedPrimitive ((x : ℂ)-(y : ℂ)*I,q)+I*(n : ℂ)*Real.pi)
      (𝓝[>] 0) (𝓝 (-B)) := by
  have he := tendsto_hillHminusShiftedPrimitive_sqrt_boundaries n r V K hK hmatch q hqV hq x
    (hpair.real_gap_mem_ball x hx)
    (hillHminus_real_gap_sqrt_continuousAt n r epsilon hr hepsilon K q l u hpair hf hnorm x hx)
  rw [hillHminus_real_gap_sqrt_value n r epsilon hr hepsilon K q l u hpair hf hnorm x hx] at he
  exact he

end NLS.KdV
