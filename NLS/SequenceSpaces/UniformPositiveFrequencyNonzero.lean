import NLS.SequenceSpaces.LocallyUniformCoordinates

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS

/-- A continuous L2 displacement of the free frequencies has one
neighborhood where ALL positive coordinates stay nonzero, provided
that they are nonzero at the center. The full displacement is bounded. -/
theorem exists_local_uniform_positive_frequencies_ne_zero
    {X : Type*} [TopologicalSpace X] (d : X → Coeff 2) (q : X)
    (hd : ContinuousAt d q)
    (hbase : ∀ n : ℕ+, (Real.pi:ℂ)*(n:ℕ)+d q ((n:ℕ):ℤ)≠0) :
    ∃ R : ℝ, 0<R ∧ ∃ V : Set X, IsOpen V ∧ q∈V ∧
      (∀ a∈V, ‖d a‖≤R) ∧
      ∀ n : ℕ+, ∀ a∈V, (Real.pi:ℂ)*(n:ℕ)+d a ((n:ℕ):ℤ)≠0 := by
  let R : ℝ := ‖d q‖+1
  have hR : 0<R := by dsimp only [R]; positivity
  have hnorm : ∀ᶠ a in 𝓝 q, ‖d a‖<R :=
    hd.norm.eventually (gt_mem_nhds (by dsimp only [R]; linarith))
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp hnorm
  obtain ⟨N,hN⟩ := exists_nat_gt (R/Real.pi)
  have hcentral : ∀ᶠ a in 𝓝 q, ∀ n∈Finset.Icc 1 N,
      (Real.pi:ℂ)*n+d a (n:ℤ)≠0 := by
    rw [Finset.eventually_all]
    intro n hn
    have hnp : 0<n := by have := (Finset.mem_Icc.mp hn).1; omega
    have hc : ContinuousAt (fun a => (Real.pi:ℂ)*n+d a (n:ℤ)) q :=
      continuousAt_const.add ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n:ℤ)).continuous.continuousAt.comp hd)
    have hh := hc.norm.eventually (lt_mem_nhds (norm_pos_iff.mpr (hbase ⟨n,hnp⟩)))
    filter_upwards [hh] with a ha
    exact norm_pos_iff.mp ha
  obtain ⟨C,hCsub,hC,hqC⟩ := _root_.mem_nhds_iff.mp hcentral
  refine ⟨R,hR,W∩C,hW.inter hC,⟨hqW,hqC⟩,
    (fun a ha => (hWsub ha.1).le),?_⟩
  intro n a ha
  by_cases hnN : (n:ℕ)≤N
  · exact hCsub ha.2 (n:ℕ) (Finset.mem_Icc.mpr ⟨n.pos,hnN⟩)
  · intro hz
    have he : d a ((n:ℕ):ℤ)=-((Real.pi:ℂ)*(n:ℕ)) := by linear_combination hz
    have hcoord := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (d a) ((n:ℕ):ℤ)
    rw [he,norm_neg,norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_natCast] at hcoord
    have hNr : R<Real.pi*(N:ℝ) := by simpa only [mul_comm] using (div_lt_iff₀ Real.pi_pos).mp hN
    have hnm : (N:ℝ)≤(n:ℕ) := by exact_mod_cast (show N≤(n:ℕ) by omega)
    have hnorma : ‖d a‖<R := hWsub ha.1
    linarith [mul_le_mul_of_nonneg_left hnm Real.pi_pos.le]

end NLS
