import NLS.ComplexAnalysis.LocalAnalyticSquareRoot
import NLS.ComplexAnalysis.EntireEvenSquareDescent

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



private theorem continuousAt_root_selection_zero (d : ℂ → ℂ) (hd : ∀ z, (d z)^2=z) :
    ContinuousAt d 0 := by
  have h0 : d 0=0 := (sq_eq_zero_iff).mp (hd 0)
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨ε^2,sq_pos_of_pos hε,?_⟩
  intro z hz
  rw [dist_zero_right] at hz
  rw [h0,dist_zero_right]
  have hn : ‖d z‖^2=‖z‖ := by rw [← norm_pow,hd]
  nlinarith [norm_nonneg (d z)]

/-- Continuous even families with values in any topological space descend
through the square map, including zero and every root-selection cut. -/
theorem continuous_even_square_descent
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (F : ℂ × A → B) (hF : Continuous F)
    (heven : ∀ a z, F (-z,a)=F (z,a))
    (d : ℂ → ℂ) (hd : ∀ z, (d z)^2=z) :
    Continuous (fun p : ℂ × A => F (d p.1,p.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.1=0
  · have hc : ContinuousAt d p.1 := by rw [hp];exact continuousAt_root_selection_zero d hd
    exact hF.continuousAt.comp ((hc.comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt)
  · have hdp : d p.1≠0 := by intro h;have hh := hd p.1;rw [h,zero_pow (by decide : 2≠0)] at hh;exact hp hh.symm
    obtain ⟨V,hV,hpV,r,hr,_,hsq⟩ := exists_local_analytic_squareRoot (fun z : ℂ => z) p.1 (d p.1)
      analyticAt_id hdp (hd p.1).symm
    have hc : ContinuousAt (fun x : ℂ × A => F (r x.1,x.2)) p :=
      hF.continuousAt.comp ((((hr _ hpV).continuousAt).comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt)
    apply hc.congr
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hV.mem_nhds hpV)] with x hx
    have hh : (d x.1)^2=(r x.1)^2 := (hd x.1).trans (hsq x.1 hx).2.symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with he | he
    · rw [he]
    · rw [he,heven]

end NLS.ComplexAnalysis
