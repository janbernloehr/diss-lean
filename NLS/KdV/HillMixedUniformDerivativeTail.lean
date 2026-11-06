import NLS.KdV.HillFreeUniformDerivativeTail
import NLS.KdV.HillMixedPeriodCompactError

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem norm_fderiv_hillMixedPeriod_sub_free_high_coordinate_le
    (N n : ℕ) (hn : 1≤n) (B D R : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (ha : ‖a‖≤R) (hp : ‖p‖≤B)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) univ)
    (m : ℤ) (hm : N≤m.natAbs) (h : Coeff 2) :
    ‖fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)-
      hillFreeScaledPeriodSequence h0q h0r n hn b) a h m‖≤
      (2*D*Real.exp ((8/Real.pi^2)*(R+2))*B)*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖*‖h‖ := by
  let f : Coeff 2 → Coeff 2 := fun b => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)-
    hillFreeScaledPeriodSequence h0q h0r n hn b
  have hdiff : AnalyticOnNhd ℂ f univ := hF.sub (analyticOnNhd_hillFreeScaledPeriodSequence h0q h0r n hn)
  have hbound : ∀ v∈ball a (1+1), ‖f v m‖≤
      (D*Real.exp ((8/Real.pi^2)*(R+2))*B)*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ := by
    intro v hv
    have hv2 : ‖v-a‖<2 := by simpa only [mem_ball,dist_eq_norm,show (1 : ℝ)+1=2 by norm_num] using hv
    have hvR : ‖v‖≤R+2 := by
      have hh := norm_le_norm_sub_add v a
      linarith
    apply (norm_hillMixedComplexPeriodSequence_sub_free_high_coordinate_le q hq hr h0q h0r N n hn B D hD hc v p hp m hm).trans
    gcongr
  have hcoord : DifferentiableOn ℂ (fun v : Coeff 2 => f v m) (ball a (1+1)) :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).differentiable.comp_differentiableOn
      (hdiff.differentiableOn.mono (subset_univ _)))
  have hder := norm_fderiv_le_of_ball_bound (fun v : Coeff 2 => f v m) a a 1 1 _ (by norm_num)
    hcoord hbound (mem_ball_self (by norm_num))
  rw [Coeff.fderiv_apply_of_differentiableAt f a h m (hdiff a (mem_univ _)).differentiableAt]
  apply ((fderiv ℂ (fun v : Coeff 2 => f v m) a).le_opNorm h).trans
  have hh := mul_le_mul_of_nonneg_right hder (norm_nonneg h)
  convert! hh using 1
  ring

/-- The original complex-minus-free derivative tails are uniformly small
on bounded root inputs and bounded source parameters, in every deleted index. -/
theorem exists_fderiv_hillMixedPeriod_sub_free_uniform_outputTail
    (N : ℕ) (B D R : ℝ) (hB : 0≤B) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (V : Set (Coeff 2))
    (hV : ∀ p∈V, ‖p‖≤B)
    (hF : ∀ n : ℕ, 1≤n → ∀ p∈V, AnalyticOnNhd ℂ
      (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) univ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ s : Finset ℤ, ∀ t : Finset ℤ, s⊆t → ∀ n : ℕ, ∀ hn : 1≤n,
      ∀ a : Coeff 2, ‖a‖≤R → ∀ p∈V,
      ‖fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)-
        hillFreeScaledPeriodSequence h0q h0r n hn b) a-
        (Coeff.truncateCLM t).comp (fderiv ℂ (fun b : Coeff 2 =>
          hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)-hillFreeScaledPeriodSequence h0q h0r n hn b) a)‖<ε := by
  let C : ℝ := 2*D*Real.exp ((8/Real.pi^2)*(R+2))*B
  have hC : 0≤C := by dsimp only [C];positivity
  let b : Coeff 2 := (C : ℂ) • Coeff.positivePuncturedLattice 2 (by norm_num)
  let ι := {v : ℕ × (Coeff 2 × Coeff 2) // 1≤v.1 ∧ ‖v.2.1‖≤R ∧ v.2.2∈V}
  let T : ι → Coeff 2 →L[ℂ] Coeff 2 := fun i => fderiv ℂ (fun x : Coeff 2 =>
    hillMixedComplexPeriodSequence q hq hr h0q h0r N i.val.1 (x,i.val.2.2)-
      hillFreeScaledPeriodSequence h0q h0r i.val.1 i.property.1 x) i.val.2.1
  have hrow : ∀ i : ι, ∀ m : ℤ, m∉Finset.Icc (-(N : ℤ)) N → ∀ h : Coeff 2,
      ‖T i h m‖≤‖b m‖*‖h‖ := by
    intro i m hm h
    have hcut : N≤m.natAbs := by simp only [Finset.mem_Icc] at hm;omega
    simpa only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hC] using
      norm_fderiv_hillMixedPeriod_sub_free_high_coordinate_le q hq hr h0q h0r N i.val.1 i.property.1 B D R hD hc
        i.val.2.1 i.val.2.2 i.property.2.1 (hV _ i.property.2.2)
        (hF _ i.property.1 _ i.property.2.2) m hcut h
  obtain ⟨s,_,hs⟩ := Coeff.exists_uniform_outputTail_operator_of_compact_rowMajorants
    (by norm_num : (2 : ℝ≥0∞)≠⊤) T (fun _ => b) {b} isCompact_singleton
    (fun _ => mem_singleton b) (Finset.Icc (-(N : ℤ)) N) hrow ε hε
  refine ⟨s,?_⟩
  intro t hst n hn a ha p hp
  exact hs t hst ⟨(n,(a,p)),hn,ha,hp⟩

/-- Uniform output approximation of the actual mixed derivative compact
remainders, simultaneously on a compact root set and one source set. -/
theorem exists_fderiv_hillMixedPeriod_add_projection_uniform_outputTail
    (N : ℕ) (B D : ℝ) (hB : 0≤B) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (V : Set (Coeff 2))
    (hV : ∀ p∈V, ‖p‖≤B)
    (hF : ∀ n : ℕ, 1≤n → ∀ p∈V, AnalyticOnNhd ℂ
      (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) univ)
    (K : Set (Coeff 2)) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∃ s : Finset ℤ, ∀ t : Finset ℤ, s⊆t → ∀ n : ℕ, 1≤n → ∀ a∈K, ∀ p∈V,
      ‖(fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a+
        Coeff.positiveDeletedProjection 2 (n : ℤ))-
        (Coeff.truncateCLM t).comp (fderiv ℂ (fun b : Coeff 2 =>
          hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a+Coeff.positiveDeletedProjection 2 (n : ℤ))‖<ε := by
  obtain ⟨R,_,hR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨s,hs⟩ := exists_fderiv_hillFreeScaledPeriodSequence_add_projection_uniform_outputTail h0q h0r K hK (ε/2) (by positivity)
  obtain ⟨u,hu⟩ := exists_fderiv_hillMixedPeriod_sub_free_uniform_outputTail q hq hr h0q h0r
    N B D R hB hD hc V hV hF (ε/2) (by positivity)
  refine ⟨s∪u,?_⟩
  intro t hst n hn a ha p hp
  let A := fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a
  let F := fderiv ℂ (hillFreeScaledPeriodSequence h0q h0r n hn) a
  let P := Coeff.positiveDeletedProjection 2 (n : ℤ)
  let Q := Coeff.truncateCLM (p := 2) t
  have hder : fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)-
      hillFreeScaledPeriodSequence h0q h0r n hn b) a=A-F := by
    exact fderiv_sub ((hF n hn p hp) a (mem_univ _)).differentiableAt
      ((analyticOnNhd_hillFreeScaledPeriodSequence h0q h0r n hn) a (mem_univ _)).differentiableAt
  have hfirst : ‖(F+P)-Q.comp (F+P)‖<ε/2 := hs t (Finset.Subset.trans Finset.subset_union_left hst) n hn a ha
  have hsecond : ‖(A-F)-Q.comp (A-F)‖<ε/2 := by
    rw [←hder]
    exact hu t (Finset.Subset.trans Finset.subset_union_right hst) n hn a (hR a ha) p hp
  have he : (A+P)-Q.comp (A+P)=((F+P)-Q.comp (F+P))+((A-F)-Q.comp (A-F)) := by
    rw [ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_sub]
    abel
  change ‖(A+P)-Q.comp (A+P)‖<ε
  rw [he]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- One original complex potential neighborhood gives uniform operator
output approximation of all actual finite-deleted mixed Jacobian remainders
on any prescribed compact root set. -/
theorem exists_hillMixedPeriod_common_uniform_jacobian_outputTails
    (K : Set (Coeff 2)) (hK : IsCompact K) :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ U : Set (Coeff 2),
      1≤N ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧ IsOpen U ∧
        SpectralWeight.one.toCoeff q∈U ∧ U⊆ball 0 B ∧
        (∀ n : ℕ, 1≤n → AnalyticOnNhd ℂ (hillMixedComplexPeriodSequence q hq hr h0q h0r N n) (univ ×ˢ U)) ∧
        ∀ ε : ℝ, 0<ε → ∃ s : Finset ℤ, ∀ t : Finset ℤ, s⊆t → ∀ n : ℕ, 1≤n →
          ∀ a∈K, ∀ p∈U,
          ‖(fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a+
            Coeff.positiveDeletedProjection 2 (n : ℤ))-
            (Coeff.truncateCLM t).comp (fderiv ℂ (fun b : Coeff 2 =>
              hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a+Coeff.positiveDeletedProjection 2 (n : ℤ))‖<ε := by
  obtain ⟨N,B,D,U,hN,hD,hc,hU,hqU,hsub,hA⟩ :=
    exists_hillMixedComplexPeriodSequence_analytic_neighborhood q hq hr h0q h0r
  have hB : 0≤B := by
    have hh : ‖SpectralWeight.one.toCoeff q‖<B := by simpa only [mem_ball,dist_zero_right] using hsub hqU
    exact (norm_nonneg _).trans hh.le
  have hV : ∀ p∈U, ‖p‖≤B := by
    intro p hp
    exact (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hsub hp).le
  have hF : ∀ n : ℕ, 1≤n → ∀ p∈U, AnalyticOnNhd ℂ
      (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) univ := by
    intro n hn p hp a _
    exact (hA n hn (a,p) ⟨mem_univ _,hp⟩).comp
      (f := fun b : Coeff 2 => (b,p)) (analyticAt_id.prod analyticAt_const)
  exact ⟨N,B,D,U,hN,hD,hc,hU,hqU,hsub,hA,
    fun ε hε => exists_fderiv_hillMixedPeriod_add_projection_uniform_outputTail q hq hr h0q h0r
      N B D hB hD.le hc U hV hF K hK ε hε⟩

end NLS.KdV
