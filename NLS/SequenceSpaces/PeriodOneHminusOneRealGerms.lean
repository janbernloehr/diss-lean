import NLS.SequenceSpaces.PeriodOneHminusOneRealForm

/-! # Analytic H^-1 germs are determined by their actual real restrictions -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS

theorem eventuallyEq_of_analyticAt_of_realHminus_agreement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f g : PeriodOneHminusOne → F) (q : PeriodOneRealHminusOne)
    (hf : AnalyticAt ℂ f q.val) (hg : AnalyticAt ℂ g q.val)
    (he : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q, f p.val = g p.val) :
    f =ᶠ[𝓝 q.val] g := by
  obtain ⟨r,hr,hreal⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨d,hd,hcomplex⟩ := Metric.mem_nhds_iff.mp (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  let radius : ℝ := min r d
  have hpos : 0 < radius := lt_min hr hd
  let A : Bool → PeriodOneRealHminusOne := fun _ => q
  let R : Bool → ℝ := fun _ => radius
  let H : Bool → PeriodOneHminusOne → F := fun b => if b then f else g
  have hH (b : Bool) : AnalyticOnNhd ℂ (H b) (ball (A b).val (R b)) := by
    intro p hp
    have hp' : p ∈ ball q.val d := ball_subset_ball (min_le_right r d) hp
    cases b
    · exact (hcomplex hp').2
    · exact (hcomplex hp').1
  have hfg (p : PeriodOneHminusOne) (hp : p ∈ ball q.val radius)
      (hpr : IsRealPeriodOneHminusOne p) : f p = g p := by
    have hp' : (⟨p,hpr⟩ : PeriodOneRealHminusOne) ∈ ball q r :=
      ball_subset_ball (min_le_left r d) hp
    exact hreal hp'
  obtain ⟨G,_,hloc,_⟩ := exists_analyticOnNhd_gluing_realHminus A R H hH (by
    intro i j p hp hpr
    have h := hfg p hp.1 hpr
    cases i <;> cases j
    · rfl
    · exact h.symm
    · exact h
    · rfl)
  filter_upwards [ball_mem_nhds q.val hpos] with p hp
  exact (hloc true hp).symm.trans (hloc false hp)

end NLS
