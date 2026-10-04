import NLS.ZakharovShabat.SourceFullAbelianCentralGapBound
import NLS.ZakharovShabat.SourceFullAbelianGapAllExponentTails

/-! # Locally uniform mixed majorants on every gap

A finitely supported nonnegative correction absorbs the central gaps
into the auxiliary Banach sequence. The half-exponent majorant is
unchanged. The source neighborhood works for all auxiliary exponents.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complete mixed boundary estimate, with no index cutoff and a
single local source neighborhood for every finite auxiliary exponent. -/
theorem exists_sourceFullAbelian_all_gap_majorants (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p,
        ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
        ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
          V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧
          ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V,
            ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
              ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧ ∀ j : ℤ, ∀ θ ∈ Icc (0:ℝ) Real.pi, ∀ upper : Bool,
                ‖C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper‖ ≤
                  ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖*(‖Bq j‖+‖Bg j‖) := by
  classical
  obtain ⟨W,hW,hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨Vt,hVt,hφt,K,ht⟩ := exists_local_sourceFullAbelian_gap_all_exponent_tails hp hp1 φ.val φ.property
  let s : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ)
  obtain ⟨Vc,hVc,hφc,hVcC,B,hB,hc⟩ := C.exists_local_finite_gap_comparison_bound φ.val hφC s
  refine ⟨C,Vt ∩ Vc,hVt.inter hVc,⟨hφt,hφc⟩,inter_subset_right.trans hVcC,?_⟩
  intro q hq hq1
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  obtain ⟨M,hM,hmajor⟩ := ht q hq hq1
  let u : Coeff q := ∑ j ∈ s, lp.single q j (B:ℂ)
  have hu (j : ℤ) : u j = if j ∈ s then (B:ℂ) else 0 := by
    simp only [u,lp.coeFn_sum,Finset.sum_apply,lp.single_apply]
    simp [Pi.single_apply]
  have hunorm : ‖u‖ ≤ s.card*B := by
    calc
      ‖u‖ ≤ ∑ j ∈ s, ‖(lp.single q j (B:ℂ) : Coeff q)‖ := by
        simpa only [u] using! norm_sum_le s (fun j => (lp.single q j (B:ℂ) : Coeff q))
      _ = ∑ _j ∈ s, B := by
        apply Finset.sum_congr rfl
        intro j _
        rw [lp.norm_single (zero_lt_one.trans hq1),Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
      _ = (s.card:ℝ)*B := by simp
  refine ⟨M+s.card*B,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hBq,hBg,hpoint⟩ := hmajor ψ hψ.1
  let Rq := Coeff.magnitude Bq+u
  have hRq (j : ℤ) : ‖Rq j‖ = ‖Bq j‖+(if j ∈ s then B else 0) := by
    simp only [Rq,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,hu]
    split_ifs <;> simp only [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ‖Bq j‖+B),add_zero,abs_of_nonneg (norm_nonneg _)]
  refine ⟨Rq,Bg,?_,?_,?_⟩
  · apply (norm_add_le _ _).trans
    rw [Coeff.norm_magnitude]
    exact add_le_add hBq hunorm
  · exact hBg.trans (by linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) s.card) hB])
  · intro j θ hθ upper
    by_cases hj : j ∈ s
    · apply (hc ψ hψ.2 j hj θ upper).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [hRq,if_pos hj]
      linarith [norm_nonneg (Bq j),norm_nonneg (Bg j)]
    · have hjK : K ≤ j.natAbs := by simp only [s,Finset.mem_Icc] at hj; omega
      have hb := hpoint W C (hVcC hψ.2) j hjK θ hθ upper
      simpa only [hRq,if_neg hj,add_zero] using hb

end NLS.ZakharovShabat
