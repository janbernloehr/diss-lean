import NLS.ZakharovShabat.SourceFullAbelianZeroMass

/-! # The exact inverse-frequency mass moment over actual open gaps

At a collapsed central gap located at zero, finite-hole Cauchy deformation
has no zero residue. The original physical mass is the sum of the signed
index-weighted inverse-frequency periods of the actual primitive.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem mass_eq_sum_inverse_frequency_periods
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (hl : canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (hr : canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0) :
    (∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) =
      -(∑ n ∈ hf.toFinset, (n : ℂ)*(∮ z in C(C.discs.center n,C.discs.inner n),
        sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z)) := by
  classical
  let s : Finset ℤ := hf.toFinset
  let R : ℤ → ℝ := fun n => (C.discs.inner n+C.discs.outer n)/2
  have hinner (n : ℤ) : C.discs.inner n < R n := by dsimp [R]; linarith [C.discs.inner_lt n]
  have houter (n : ℤ) : R n < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
  have hs (n : ℤ) : n ∈ s ↔ canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0 := Set.Finite.mem_toFinset hf
  have hgap0 : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0 := by
    rw [canonicalPeriodicGap,hl,hr,sub_self]
  have hnon (n : ℤ) (hn : n ∈ s) : n ≠ 0 := by rintro rfl; exact (hs 0).mp hn hgap0
  have hzero (n : ℤ) (hn : n ∈ s) : (0 : ℂ) ∉ ball (C.discs.center n) (C.discs.outer n) := by
    intro hz
    have ha := C.discs.avoids_other φ.val hφ n (ball_subset_closedBall hz) 0 (hnon n hn).symm
    apply ha
    rw [←hl]
    exact left_mem_segment ℝ _ _
  have hc : IsCompact (⋃ n ∈ s, closedBall (C.discs.center n) (R n)) :=
    s.finite_toSet.isCompact_biUnion fun n _ => isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := hc.isBounded.exists_norm_le
  obtain ⟨T,hT,hmass⟩ := exists_sourceFullAbelian_finiteGap_mass_contour C φ hφ hf
  let S := max B T+1
  have hTS : T ≤ S := by dsimp [S]; linarith [le_max_right B T]
  have hS : 0 < S := hT.trans_le hTS
  have henclosed (n : ℤ) (hn : n ∈ s) : closedBall (C.discs.center n) (R n) ⊆ ball 0 S := by
    intro z hz
    have hb := hB z (mem_iUnion₂.mpr ⟨n,hn,hz⟩)
    rw [mem_ball,dist_zero_right]
    dsimp [S]
    linarith [le_max_left B T]
  have hdisj (n : ℤ) (_hn : n ∈ s) (m : ℤ) (_hm : m ∈ s) (hnm : n ≠ m) :
      Disjoint (closedBall (C.discs.center n) (R n)) (closedBall (C.discs.center m) (R m)) :=
    (C.discs.disjoint n m hnm).mono (closedBall_subset_ball (houter n)) (closedBall_subset_ball (houter m))
  have ha : AnalyticOnNhd ℂ (fun z => (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^2/z)
      (circleHoleDomain 0 S s C.discs.center C.discs.inner) := by
    intro z hz
    apply C.square_over_frequency_analytic_of_central_endpoints φ hφ hl hr z
    intro n hn hzn
    exact hz.2 n ((hs n).mpr hn) (C.discs.segment_subset φ.val hφ n hzn)
  have hdec := circleIntegral_eq_sum_of_finite_holes 0 S hS.le s C.discs.center C.discs.inner R _
    (fun n _ => C.discs.inner_pos n) (fun n _ => hinner n) henclosed hdisj ha
  have he := hmass S hTS
  rw [hdec] at he
  have hlocal (n : ℤ) (hn : n ∈ s) := C.square_over_frequency_circle φ.val hφ n
    (C.discs.inner n) le_rfl (C.discs.inner_lt n) (hzero n hn)
  have he' : (2*Real.pi*I : ℂ)*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) =
      (2*Real.pi*I : ℂ)*(-(∑ n ∈ s, (n : ℂ)*(∮ z in C(C.discs.center n,C.discs.inner n),
        sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z))) := by
    rw [←he,mul_neg,Finset.mul_sum,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hlocal n hn]
    ring
  exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero) he'

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
