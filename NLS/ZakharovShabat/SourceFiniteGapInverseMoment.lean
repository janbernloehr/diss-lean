import NLS.ZakharovShabat.SourceFullAbelianInverseGapCircle
import NLS.ZakharovShabat.SourceFiniteGapContourDecomposition

/-! The actual finite-gap inverse-frequency moment balance. The central
zero is filled BEFORE applying finite-hole Cauchy decomposition. Only
original OPEN gaps occur in the finite sum, and every local contour is
an actual indexed full primitive with the literal 1/z weight. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.ComplexAnalysis
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem sourceFiniteGap_inverse_moment_balance
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0=0)
    (h0 : (0:ℂ) ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0} : Set ℂ)) :
    (∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) =
      -∑ n ∈ hf.toFinset, (n:ℂ)*(∮ z in C(C.discs.center n,(C.discs.inner n+C.discs.outer n)/2),
        sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z) := by
  classical
  let ρ : ℤ → ℝ := fun n => (C.discs.inner n+C.discs.outer n)/2
  have hi (n : ℤ) : C.discs.inner n ≤ ρ n := by dsimp [ρ]; linarith [C.discs.inner_lt n]
  have ho (n : ℤ) : ρ n < C.discs.outer n := by dsimp [ρ]; linarith [C.discs.inner_lt n]
  have hr (n : ℤ) : 0 < ρ n := (C.discs.inner_pos n).trans_le (hi n)
  have hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ.val C.discs.center ρ := by
    refine ⟨C.discs.center_real,fun n => ⟨hr n,?_,?_,?_⟩⟩
    · exact (C.discs.segment_subset φ.val hφ n).trans (ball_subset_ball (hi n))
    · exact (closedBall_subset_closedBall (ho n).le).trans (C.discs.avoids_other φ.val hφ n)
    · exact C.intermediate_circle_root n φ.val hφ (ρ n) (hi n) (ho n)
  have hseg : (0:ℂ) ∈ sourcePeriodicSegment hp hp1 φ.val 0 := by
    change (0:ℂ) ∈ segment ℝ _ _
    rcases Set.mem_insert_iff.mp h0 with hl | hr
    · rw [hl]
      exact left_mem_segment ℝ _ _
    · rw [Set.mem_singleton_iff.mp hr]
      exact right_mem_segment ℝ _ _
  have hcentral : (0:ℂ) ∈ ball (C.discs.center 0) (C.discs.outer 0) :=
    ball_subset_ball (C.discs.inner_lt 0).le (C.discs.segment_subset φ.val hφ 0 hseg)
  have hzero (n : ℤ) (hn : n ∈ hf.toFinset) : (0:ℂ) ∉ closedBall (C.discs.center n) (ρ n) := by
    have hne : n ≠ 0 := by
      intro he
      subst n
      exact (Set.Finite.mem_toFinset hf).mp hn hgap
    intro hz
    exact Set.disjoint_left.mp (C.discs.disjoint n 0 hne)
      (closedBall_subset_ball (ho n) hz) hcentral
  let F : ℂ → ℂ := fun z => sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)
  let G : ℂ → ℂ := filledSquareOverZero F
  have hF0 : F 0=0 := (C.central_zero_value_and_mem φ.val hφ hgap h0).1
  have hG : AnalyticOnNhd ℂ G (sourceOpenGapComplement hp hp1 φ.val) :=
    C.analytic_filled_inverse_square_of_central_zero φ hφ hgap h0
  obtain ⟨S,hS,hdec⟩ := exists_sourceFiniteGap_contour_decomposition hp hp1 φ hf C.discs.center ρ hfamily
  obtain ⟨T,hT,hmass⟩ := exists_sourceFullAbelian_finiteGap_inverse_mass_contour C φ hφ hf
  let R := max S T
  have hR : 0 < R := hS.trans_le (le_max_left _ _)
  have houter : (∮ z in C(0,R), G z)=(2*Real.pi*I:ℂ)*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) := by
    rw [← hmass R (le_max_right _ _)]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hn : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
    exact filledSquareOverZero_eq_div F hF0 z (norm_pos_iff.mp (hn.symm ▸ hR))
  have hinner (n : ℤ) (hn : n ∈ hf.toFinset) :
      (∮ z in C(C.discs.center n,ρ n), G z)=
        (-2*I*(Real.pi:ℂ)*n)*(∮ z in C(C.discs.center n,ρ n),
          sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z) := by
    rw [← C.inverse_square_circle_eq_inverse_primitive n φ.val hφ (ρ n) (hi n) (ho n) (hzero n hn)]
    apply circleIntegral.integral_congr (hr n).le
    intro z hz
    have hz0 : z ≠ 0 := fun he => hzero n hn (he ▸ sphere_subset_closedBall hz)
    exact filledSquareOverZero_eq_div F hF0 z hz0
  have he := hdec R (le_max_left _ _) G hG
  rw [houter] at he
  have hs : (∑ n ∈ hf.toFinset, ∮ z in C(C.discs.center n,ρ n), G z)=
      (2*Real.pi*I:ℂ)*(-∑ n ∈ hf.toFinset, (n:ℂ)*(∮ z in C(C.discs.center n,ρ n),
        sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z)) := by
    rw [mul_neg,Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hinner n hn]
    ring
  rw [hs] at he
  exact mul_left_cancel₀ (by exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero) he

end NLS.ZakharovShabat
