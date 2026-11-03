import NLS.KdV.HillHminusOneRealGapContours

/-! # Continuity of the canonical H^-1 gap circles

Intrinsic label continuity includes collisions, so the canonical center,
half-length, collar and radius remain continuous there. A complex-open
neighborhood controls the circle perturbation for every real input.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

theorem continuous_hillHminusRealGapCenter (n : ℕ) :
    Continuous (fun q : PeriodOneRealHminusOne => hillHminusRealGapCenter q.val q.property n) :=
  ((continuous_hillHminusRealLabels (2*n-1)).add (continuous_hillHminusRealLabels (2*n))).div_const 2

theorem continuous_hillHminusRealGapHalfLength (n : ℕ) :
    Continuous (fun q : PeriodOneRealHminusOne => hillHminusRealGapHalfLength q.val q.property n) :=
  ((continuous_hillHminusRealLabels (2*n)).sub (continuous_hillHminusRealLabels (2*n-1))).div_const 2

theorem continuous_hillHminusRealGapCollar (n : ℕ) :
    Continuous (fun q : PeriodOneRealHminusOne => hillHminusRealGapCollar q.val q.property n) :=
  (((continuous_hillHminusRealLabels (2*n-1)).sub (continuous_hillHminusRealLabels (2*n-2))).min
    ((continuous_hillHminusRealLabels (2*n+1)).sub (continuous_hillHminusRealLabels (2*n)))).div_const 4

theorem exists_hillHminus_gap_circle_close_neighborhood
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
      ∀ p ∈ V, ∀ hp : IsRealPeriodOneHminusOne p,
        dist (hillHminusRealGapCenter p hp n : ℂ) (hillHminusRealGapCenter q hr n : ℂ) +
          |(hillHminusRealGapHalfLength p hp n+hillHminusRealGapCollar p hp n) -
            (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n)| < ε := by
  let c := hillHminusRealGapCenter q hr n
  let r := hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n
  let D : PeriodOneRealHminusOne → ℝ := fun p =>
    dist (hillHminusRealGapCenter p.val p.property n : ℂ) (c : ℂ) +
      |(hillHminusRealGapHalfLength p.val p.property n+hillHminusRealGapCollar p.val p.property n)-r|
  have hc : Continuous (fun p : PeriodOneRealHminusOne => (hillHminusRealGapCenter p.val p.property n : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_hillHminusRealGapCenter n)
  have hR := (continuous_hillHminusRealGapHalfLength n).add (continuous_hillHminusRealGapCollar n)
  have hD : Continuous D := (hc.dist continuous_const).add ((hR.sub continuous_const).abs)
  have hbase : D ⟨q,hr⟩ = 0 := by simp only [D,c,r,dist_self,sub_self,abs_zero,add_zero]
  have hlim : Tendsto D (𝓝 (⟨q,hr⟩ : PeriodOneRealHminusOne)) (𝓝 0) := by
    rw [← hbase]
    exact hD.tendsto ⟨q,hr⟩
  have hnear : ∀ᶠ p in 𝓝 (⟨q,hr⟩ : PeriodOneRealHminusOne), D p < ε :=
    hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ball q δ,isOpen_ball,mem_ball_self hδ,?_⟩
  intro p hp hpr
  have hpR : (⟨p,hpr⟩ : PeriodOneRealHminusOne) ∈ ball ⟨q,hr⟩ δ := hp
  have hresult := hball hpR
  simpa only [mem_ofPred_eq,D,c,r] using hresult

end NLS.KdV
