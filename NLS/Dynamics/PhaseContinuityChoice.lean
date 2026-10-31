import NLS.Dynamics.PhaseContinuityEstimate
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # Uniform continuity from a symmetric frequency cutoff

For every finite Banach exponent, first choose a symmetric tail cutoff,
then a positive time increment. Both choices work for all real time
origins, with the exact Section 22 pair norm and two-epsilon bound.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A symmetric cutoff at least one makes the weighted pair tail small. -/
theorem exists_symmetric_phase_tail_small (hp : p ≠ ⊤) (z : Coeff p × Coeff p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ (2 : ℝ) ^ p.toReal *
      ∑' n : {n : ℤ // n ∉ Finset.Icc (-(N : ℤ)) N},
        (‖z.1 n.val‖ ^ p.toReal+‖z.2 n.val‖ ^ p.toReal) ≤ ε ^ p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  let E : ℤ → ℝ := fun n => ‖z.1 n‖ ^ p.toReal+‖z.2 n‖ ^ p.toReal
  have hE : Summable E := (z.1.property.summable hp0).add (z.2.property.summable hp0)
  have hsum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, E n) atTop (𝓝 (∑' n, E n)) :=
    hE.hasSum.comp Finset.tendsto_Icc_neg
  have htail : Tendsto (fun N : ℕ => ∑' n : {n : ℤ // n ∉ Finset.Icc (-(N : ℤ)) N}, E n.val)
      atTop (𝓝 (0 : ℝ)) := by
    have he (N : ℕ) : (∑' n, E n)-(∑ n ∈ Finset.Icc (-(N : ℤ)) N, E n) =
        ∑' n : {n : ℤ // n ∉ Finset.Icc (-(N : ℤ)) N}, E n.val := by
      rw [← hE.sum_add_tsum_subtype_compl (Finset.Icc (-(N : ℤ)) N)]
      ring
    simpa only [sub_self,he] using (tendsto_const_nhds (x := ∑' n, E n)).sub hsum
  have ht := (tendsto_const_nhds (x := (2 : ℝ) ^ p.toReal)).mul htail
  have heps : 0 < ε ^ p.toReal := Real.rpow_pos_of_pos hε _
  have hb : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ p.toReal *
      ∑' n : {n : ℤ // n ∉ Finset.Icc (-(N : ℤ)) N}, E n.val < ε ^ p.toReal := by
    exact ht.eventually (gt_mem_nhds (by simpa only [mul_zero] using heps))
  obtain ⟨N,hN,hbound⟩ := ((eventually_ge_atTop (1 : ℕ)).and hb).exists
  exact ⟨N,hN,hbound.le⟩

/-- A finite head admits one time increment for every pair of real times.
Both the printed scalar bound and the finite-head energy are controlled. -/
theorem exists_phase_head_small (hp : p ≠ ⊤) (ω : ℤ → ℝ) (z : Coeff p × Coeff p)
    (S : Finset ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t u : ℝ, |t-u| < δ →
      (∀ n ∈ S, ‖Complex.exp ((((t-u)*ω n : ℝ) : ℂ)*Complex.I)-1‖ *
        ‖(CoeffPair.toMax p).symm z‖ ≤ ε) ∧
      (∑ n ∈ S, ‖Complex.exp ((((t-u)*ω n : ℝ) : ℂ)*Complex.I)-1‖ ^ p.toReal *
        (‖z.1 n‖ ^ p.toReal+‖z.2 n‖ ^ p.toReal)) ≤ ε ^ p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  let f : ℝ → ℤ → ℝ := fun d n => ‖Complex.exp (((d*ω n : ℝ) : ℂ)*Complex.I)-1‖
  have hc (n : ℤ) : ContinuousAt (fun d => f d n) 0 := by dsimp [f]; fun_prop
  have hz (n : ℤ) : f 0 n = 0 := by simp [f]
  have hscalar : ∀ᶠ d : ℝ in 𝓝 0, ∀ n ∈ S, f d n*‖(CoeffPair.toMax p).symm z‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro n _
    exact ((hc n).mul_const ‖(CoeffPair.toMax p).symm z‖).eventually
      (gt_mem_nhds (by simpa only [hz,zero_mul] using hε))
  have hsum : ContinuousAt (fun d : ℝ => ∑ n ∈ S,
      (f d n) ^ p.toReal * (‖z.1 n‖ ^ p.toReal+‖z.2 n‖ ^ p.toReal)) 0 :=
    tendsto_finsetSum S (fun n _ => ((hc n).rpow_const (Or.inr hp0.le)).mul_const _)
  have henergy : ∀ᶠ d : ℝ in 𝓝 0, (∑ n ∈ S,
      (f d n) ^ p.toReal * (‖z.1 n‖ ^ p.toReal+‖z.2 n‖ ^ p.toReal)) < ε ^ p.toReal := by
    exact hsum.eventually (gt_mem_nhds (by
      simpa only [hz,Real.zero_rpow hp0.ne',zero_mul,Finset.sum_const_zero] using
        Real.rpow_pos_of_pos hε p.toReal))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp (hscalar.and henergy)
  refine ⟨δ,hδ,?_⟩
  intro t u htu
  have h := hball (show dist (t-u) 0 < δ by simpa only [Real.dist_eq,sub_zero] using htu)
  exact ⟨fun n hn => (h.1 n hn).le,h.2.le⟩

/-- The printed cutoff-first, time-increment-second construction yields the
full pair-norm estimate, uniformly for all real time origins. -/
theorem exists_symmetric_phase_continuity_estimate (hp : p ≠ ⊤)
    (ω : ℤ → ℝ) (z : Coeff p × Coeff p) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ δ : ℝ, 0 < δ ∧
      ((2 : ℝ) ^ p.toReal * ∑' n : {n : ℤ // n ∉ Finset.Icc (-(N : ℤ)) N},
        (‖z.1 n.val‖ ^ p.toReal+‖z.2 n.val‖ ^ p.toReal) ≤ ε ^ p.toReal) ∧
      ∀ t u : ℝ, |t-u| < δ →
        (∀ n ∈ Finset.Icc (-(N : ℤ)) N,
          ‖Complex.exp ((((t-u)*ω n : ℝ) : ℂ)*Complex.I)-1‖ * ‖(CoeffPair.toMax p).symm z‖ ≤ ε) ∧
        ‖(CoeffPair.toMax p).symm (hamiltonianPhaseFlow ω t z-hamiltonianPhaseFlow ω u z)‖ ≤ 2*ε := by
  obtain ⟨N,hN,htail⟩ := exists_symmetric_phase_tail_small hp z ε hε
  obtain ⟨δ,hδ,hhead⟩ := exists_phase_head_small hp ω z (Finset.Icc (-(N : ℤ)) N) ε hε
  refine ⟨N,hN,δ,hδ,htail,?_⟩
  intro t u htu
  obtain ⟨hs,he⟩ := hhead t u htu
  exact ⟨hs,norm_hamiltonianPhaseFlow_sub_le_of_head_tail hp ω t u z _ ε hε.le he htail⟩

end NLS.Birkhoff
