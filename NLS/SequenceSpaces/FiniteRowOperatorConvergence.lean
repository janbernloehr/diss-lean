import NLS.SequenceSpaces.UniformOperatorOutputTails
import NLS.SequenceSpaces.SourceCompactProjection
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.Coeff



variable {p : ℝ≥0∞} [Fact (1≤p)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem truncateCLM_comp_eq_sum_rows (s : Finset ℤ) (T : E →L[ℂ] Coeff p) :
    (truncateCLM s).comp T=∑ m∈s,
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p m).comp
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp T) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,truncateCLM_apply,truncate,sum_apply]
  rfl

theorem tendsto_truncate_operator_of_rowFunctionals
    {ι : Type*} {l : Filter ι} (T : ι → E →L[ℂ] Coeff p) (S : E →L[ℂ] Coeff p)
    (s : Finset ℤ)
    (hrow : ∀ m∈s, Tendsto (fun i => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp (T i)) l
      (𝓝 ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp S))) :
    Tendsto (fun i => (truncateCLM s).comp (T i)) l (𝓝 ((truncateCLM s).comp S)) := by
  simp_rw [truncateCLM_comp_eq_sum_rows]
  apply tendsto_finsetSum s
  intro m hm
  have hc := (((ContinuousLinearMap.compL ℂ E ℂ (Coeff p))
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p m)).continuous.continuousAt.tendsto).comp (hrow m hm)
  simpa only [Function.comp_def,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_assoc] using hc

/-- Full row-functional convergence and uniform finite-output
approximation imply convergence of the whole operator in norm. -/
theorem tendsto_operator_of_rows_and_uniform_outputTails
    (hp : p≠⊤) {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℂ] Coeff p) (S : E →L[ℂ] Coeff p) (hS : IsCompactOperator S)
    (hrow : ∀ m, Tendsto (fun i => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp (T i)) l
      (𝓝 ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp S)))
    (htail : ∀ ε : ℝ, 0<ε → ∃ s : Finset ℤ, ∀ t : Finset ℤ, s⊆t →
      ∀ᶠ i in l, ‖T i-(truncateCLM t).comp (T i)‖<ε) :
    Tendsto T l (𝓝 S) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s,hs⟩ := htail (ε/3) (by positivity)
  obtain ⟨M,_,hM⟩ := exists_sourceI3Tail_comp_norm_le hp S hS (ε := ε/3) (by positivity)
  let t := s∪Finset.Icc (-(M : ℤ)) M
  have hsmallS : ‖S-(truncateCLM t).comp S‖≤ε/3 := by
    apply (norm_outputTail_operator_mono S (Finset.Icc (-(M : ℤ)) M) t Finset.subset_union_right).trans
    simpa only [sourceI3Tail,sourceI3Projection,ContinuousLinearMap.sub_comp,ContinuousLinearMap.id_comp] using hM M le_rfl
  have hhead := tendsto_truncate_operator_of_rowFunctionals T S t (fun m _ => hrow m)
  filter_upwards [hs t Finset.subset_union_left,Metric.tendsto_nhds.mp hhead (ε/3) (by positivity)] with i hi hj
  rw [dist_eq_norm] at hj ⊢
  let A := T i-(truncateCLM t).comp (T i)
  let B := (truncateCLM t).comp (T i)-(truncateCLM t).comp S
  let C := (truncateCLM t).comp S-S
  have he : T i-S=A+B+C := by dsimp only [A,B,C];abel
  have htri : ‖T i-S‖≤‖A‖+‖B‖+‖C‖ := by
    rw [he]
    exact norm_add₃_le
  have hC : ‖C‖≤ε/3 := by simpa only [C,norm_sub_rev] using hsmallS
  have hA : ‖A‖<ε/3 := hi
  have hB : ‖B‖<ε/3 := hj
  linarith

/-- The same norm-convergence criterion after subtracting a fixed
noncompact common operator, such as minus the positive projection. -/
theorem tendsto_operator_of_rows_and_uniform_remainder_outputTails
    (hp : p≠⊤) {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℂ] Coeff p) (S D : E →L[ℂ] Coeff p) (hS : IsCompactOperator (S-D))
    (hrow : ∀ m, Tendsto (fun i => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp (T i)) l
      (𝓝 ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp S)))
    (htail : ∀ ε : ℝ, 0<ε → ∃ s : Finset ℤ, ∀ t : Finset ℤ, s⊆t →
      ∀ᶠ i in l, ‖(T i-D)-(truncateCLM t).comp (T i-D)‖<ε) :
    Tendsto T l (𝓝 S) := by
  have hrows : ∀ m, Tendsto (fun i => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp (T i-D)) l
      (𝓝 ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp (S-D))) := by
    intro m
    simpa only [ContinuousLinearMap.comp_sub] using
      (hrow m).sub_const ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp D)
  have ht := tendsto_operator_of_rows_and_uniform_outputTails hp (fun i => T i-D) (S-D) hS hrows htail
  simpa only [sub_add_cancel] using ht.add_const D

end NLS.Coeff
