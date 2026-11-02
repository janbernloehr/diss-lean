import NLS.ComplexAnalysis.AppendixFProofEstimates
import NLS.ComplexAnalysis.IsolatedOrderStability
import NLS.ZakharovShabat.AppendixFDeletedPair
import NLS.ZakharovShabat.SourceLemmaF1

/-! # The half-gap Rouché count in the proof of F.1 -/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- Differentiating the quadratic factorization retains the exact normalization in F.1. -/
theorem appendixF_quadratic_derivative (F G : ℂ → ℂ) (τ γ z : ℂ)
    (hG : DifferentiableAt ℂ G z)
    (he : ∀ w, F w^2-4 = -4*((w-τ)^2-γ^2/4)*G w) :
    deriv (fun w => F w^2-4) z/4 =
      2*(τ-z)*G z-((z-τ)^2-γ^2/4)*deriv G z := by
  have hr := (((((hasDerivAt_id z).sub_const τ).pow 2).sub_const (γ^2/4)).mul
    hG.hasDerivAt).const_mul (-4)
  have hf : (fun w => F w^2-4) = fun w => -4*(((w-τ)^2-γ^2/4)*G w) := by
    funext w
    rw [he]
    ring
  change HasDerivAt (fun w => -4*(((w-τ)^2-γ^2/4)*G w)) _ z at hr
  rw [hf,hr.deriv]
  simp only [Pi.pow_apply,id_eq]
  ring

/-- The strict half-gap boundary estimate gives exactly one zero, counted with multiplicity. -/
theorem appendixF_half_gap_zero_count (G : ℂ → ℂ) (τ γ : ℂ) (r s : ℝ)
    (hγ : γ ≠ 0) (hs : 0 < s)
    (hG : AnalyticOnNhd ℂ G (closedBall τ (‖γ‖/2)))
    (hbound : ∀ z ∈ closedBall τ (‖γ‖/2), s ≤ ‖G z‖ ∧ ‖deriv G z‖ ≤ r)
    (hsmall : ‖γ‖*r ≤ s) :
    analyticZeroCount (fun z => 2*(τ-z)*G z-((z-τ)^2-γ^2/4)*deriv G z)
      (closedBall τ (‖γ‖/2)) = 1 := by
  let f : ℂ → ℂ := fun z => 2*(τ-z)*G z
  let g : ℂ → ℂ := fun z => f z-((z-τ)^2-γ^2/4)*deriv G z
  have hR : 0 < ‖γ‖/2 := div_pos (norm_pos_iff.mpr hγ) (by norm_num)
  have hτ : τ ∈ closedBall τ (‖γ‖/2) := mem_closedBall_self hR.le
  have hne (z : ℂ) (hz : z ∈ closedBall τ (‖γ‖/2)) : G z ≠ 0 :=
    norm_pos_iff.mp (hs.trans_le (hbound z hz).1)
  have hf : AnalyticOnNhd ℂ f (closedBall τ (‖γ‖/2)) := fun z hz =>
    (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).mul (hG z hz)
  have hg : AnalyticOnNhd ℂ g (closedBall τ (‖γ‖/2)) := fun z hz =>
    (hf z hz).sub ((((analyticAt_id.sub analyticAt_const).pow 2).sub analyticAt_const).mul
      (hG z hz).deriv)
  have hb (z : ℂ) (hz : z ∈ sphere τ (‖γ‖/2)) : ‖g z-f z‖ < ‖f z‖ := by
    have he := appendixF_quadratic_boundary_estimate (z-τ) γ (G z) (deriv G z) r s
      (by simpa only [mem_sphere,dist_eq_norm] using hz) hγ hs
      (hbound z (sphere_subset_closedBall hz)).1 (hbound z (sphere_subset_closedBall hz)).2 hsmall
    have hleft : g z-f z = -(((z-τ)^2-γ^2/4)*deriv G z) := by dsimp [g]; ring
    have hright : f z = -(2*(z-τ)*G z) := by dsimp [f]; ring
    rw [hleft,hright,norm_neg,norm_neg]
    exact (he.1.trans_lt he.2.1).trans_le he.2.2
  change analyticZeroCount g (closedBall τ (‖γ‖/2)) = 1
  rw [analyticZeroCount_eq_of_boundary_lt hR hf hg hb]
  rw [analyticZeroCount_eq_order_of_isolated f τ (‖γ‖/2) hR.le (by
    intro z hz he
    have hzero : 2*(τ-z) = 0 := (mul_eq_zero.mp he).resolve_right (hne z hz)
    have heq : τ-z = 0 := (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact (sub_eq_zero.mp heq).symm)]
  have hd : HasDerivAt f (-2*G τ) τ := by
    have hh := (((hasDerivAt_const τ τ).sub (hasDerivAt_id τ)).const_mul (2:ℂ)).mul
      (hG τ hτ).differentiableAt.hasDerivAt
    exact hh.congr_deriv (by simp)
  have hord := (hf τ hτ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (by simp [f]) (by rw [hd.deriv]; exact mul_ne_zero (by norm_num) (hne τ hτ))
  simp only [analyticOrderNatAt,hord,ENat.toNat_one]

end NLS.ComplexAnalysis

namespace NLS.ZakharovShabat
open NLS.ComplexAnalysis
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
variable {D : ℤ → Set ℂ} {c : ℝ}

/-- Near a collapsed source gap, the actual differentiated discriminant has one root
in every noncollapsed half-gap disc, by the source bounds and Rouché's theorem. -/
theorem SourceLemma10_5Data.appendixF_local_half_gap_zero_count
    (H : SourceLemma10_5Data hp hp1 W) (hW : IsOpen W)
    (hV : IsOpen V) (hVW : V ⊆ W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧ ∀ ψ ∈ U,
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 →
      analyticZeroCount (fun z => deriv (fun w =>
        (canonicalDiscriminant hp (periodOnePotential ψ) w)^2-4) z/4)
        (closedBall (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
          (‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖/2)) = 1 := by
  obtain ⟨U,hU,hφU,hUV,s,r,hs,_,hbound⟩ :=
    H.deletedPair_collapsed_disk_bounds hW hV hVW hD φ hφ n hgap
  let τ := fun ψ : CoeffPair p =>
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let γ := fun ψ : CoeffPair p =>
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hτ : ContinuousAt τ φ := (H.roots.symmetric.midpoint n φ (hVW hφ)).continuousAt
  have hγ : ContinuousAt (fun ψ => ‖γ ψ‖) φ := by
    simpa only [norm_pow,Real.sqrt_sq (norm_nonneg _)] using
      (H.roots.symmetric.squared_gap n φ (hVW hφ)).continuousAt.norm.sqrt
  have hτD : τ φ ∈ D n := hD.gap φ hφ n (sourcePeriodicMidpoint_mem_segment hp hp1 φ n)
  have hDn : IsOpen (D n) := by obtain ⟨a,R,_,he⟩ := hD.discs n; rw [he]; exact isOpen_ball
  obtain ⟨ε,hε,hεD⟩ := Metric.mem_nhds_iff.mp (hDn.mem_nhds hτD)
  have hnear : ∀ᶠ ψ in 𝓝 φ, dist (τ ψ) (τ φ)+‖γ ψ‖/2 < ε :=
    ((hτ.dist continuousAt_const).add (hγ.div_const 2)).eventually
      (gt_mem_nhds (by simpa only [γ,dist_self,hgap,norm_zero,zero_div,add_zero] using hε))
  obtain ⟨T,hTsub,hT,hφT⟩ := _root_.mem_nhds_iff.mp (hnear.and (hU.mem_nhds hφU))
  refine ⟨T,hT,hφT,fun ψ hψ => hUV (hTsub hψ).2,?_⟩
  intro ψ hψ hg
  have hψU := (hTsub hψ).2
  have hball : closedBall (τ ψ) (‖γ ψ‖/2) ⊆ closure (D n) := by
    intro z hz
    apply subset_closure (hεD ?_)
    apply mem_ball.mpr
    calc
      dist z (τ φ) ≤ dist z (τ ψ)+dist (τ ψ) (τ φ) := dist_triangle _ _ _
      _ ≤ ‖γ ψ‖/2+dist (τ ψ) (τ φ) := by linarith [mem_closedBall.mp hz]
      _ < ε := by linarith [(hTsub hψ).1]
  let P := canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hP : AnalyticOnNhd ℂ P univ :=
    analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1 _ (periodOnePotential_mem ψ) n
  have he : (fun z => deriv (fun w => (canonicalDiscriminant hp (periodOnePotential ψ) w)^2-4) z/4) =
      fun z => 2*(τ ψ-z)*P z-((z-τ ψ)^2-γ ψ^2/4)*deriv P z := by
    funext z
    exact appendixF_quadratic_derivative _ P (τ ψ) (γ ψ) z (hP z (mem_univ z)).differentiableAt
      (canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1 _ (periodOnePotential_mem ψ) n)
  rw [he]
  exact appendixF_half_gap_zero_count P (τ ψ) (γ ψ) r s hg hs
    (hP.mono (subset_univ _)) (fun z hz => (hbound ψ hψU).2 z (hball hz)) (hbound ψ hψU).1

end NLS.ZakharovShabat
