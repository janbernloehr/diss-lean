import NLS.ZakharovShabat.SourceAngularBetaLocalBound
import NLS.ZakharovShabat.SourceAngularBetaRegularFactorBound
import NLS.ZakharovShabat.SourcePsiUniformRetainedRootBounds
import NLS.ZakharovShabat.SourcePsiExtensionUniformFilledStability
import NLS.ZakharovShabat.SourcePsiMidpointShiftedDiscBound
import NLS.ZakharovShabat.SourcePsiGapProductDiscBound

/-!
# All deleted indices on one fixed selected angular chart

Uniform filled-root stability and compact gap-product bounds control
chi on the selected contour for every distant deleted index. A finite
intersection of the actual local beta estimates handles the remaining
deleted indices. The resulting reciprocal-index estimate has one source
neighborhood and constant for the entire fixed selected chart, including
central gaps, collapsed gaps, and endpoint terminals.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W₀ W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- A compact selected disc has one actual chi bound for every distant
deleted index on a common complex source neighborhood. -/
theorem exists_local_distantDeleted_regularFactor_circle_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ))
    (ρ : ℝ) (_hrρ : r < ρ) (hρR : ρ < R) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ K : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ ψ ∈ U, ∀ n : ℤ, K < n.natAbs → m ≠ n →
        ∀ z ∈ sphere (c m) ρ,
          ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ z‖ ≤ M := by
  have hdom : closedBall (c m) ρ ⊆ sourceStandardRootOmittedDomain hp hp1 φ m := by
    intro z hz
    apply ((D.disc_family φ hφ).contour_family.2 m).2.2.1
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (hρR.trans D.outer_lt_assigned).le)
  obtain ⟨δ,Q,hδ,hQ,hquot⟩ := exists_sourcePsiQuotient_disc_bound_near_gapProduct hp hp1 ⟨φ,hreal⟩ m (c m) ρ hdom
  obtain ⟨η,hη,_,hgraph⟩ := hs.exists_uniform_midpointFilled_graph_radius ⟨φ,hreal⟩ δ hδ
  obtain ⟨_,_,Vm,hVm,hφm,L,hL,hmid⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : 0 < (1:ℝ))
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(L+‖c m-(Real.pi:ℂ)*m‖+ρ)/Real.pi)
  have hNπ : 2*(L+‖c m-(Real.pi:ℂ)*m‖+ρ) ≤ Real.pi*(N:ℝ) :=
    by simpa only [mul_comm] using ((div_lt_iff₀ Real.pi_pos).mp hN).le
  let U := (ball φ η ∩ Vm) ∩ V
  let K := N+m.natAbs
  refine ⟨U,(isOpen_ball.inter hVm).inter D.source_open,⟨⟨mem_ball_self hη,hφm⟩,hφ⟩,
    inter_subset_right,K,2*Q+1,by positivity,?_⟩
  intro ψ hψ n hn hmn z hz
  have hmidn : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi:ℂ)*n‖ ≤ L := by
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using
      (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ n).trans (hmid ψ hψ.1.2).1
  have htri : n.natAbs ≤ (n-m).natAbs+m.natAbs := by
    simpa only [sub_add_cancel] using Int.natAbs_add_le (n-m) m
  have hdist : N ≤ (n-m).natAbs := by dsimp only [K] at hn; omega
  have hdistReal : (N:ℝ) ≤ |((n-m : ℤ) : ℝ)| := by
    have h : (N:ℝ) ≤ ((n-m).natAbs:ℝ) := by exact_mod_cast hdist
    simpa only [Nat.cast_natAbs,Int.cast_abs] using h
  have hsep : (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖ := by
    apply shifted_root_shifted_disc_distance_lower n m _ (c m) ρ _ z (sphere_subset_closedBall hz)
    nlinarith [mul_le_mul_of_nonneg_left hdistReal Real.pi_pos.le]
  let q := (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ)
  let q₀ := (sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n ⟨φ,hreal⟩)
    (sourceStandardRootMidpoint hp hp1 φ n),φ)
  let A := sourcePeriodicGapRootSet hp hp1 φ ×ˢ {φ}
  have hq₀ : q₀ ∈ A := ⟨sourcePsiGapRoot_filled_mem_periodicGapRootSet hp hp1 ⟨φ,hreal⟩ n,rfl⟩
  have hnear := hgraph ψ hψ.1.1 n
  have hq : q ∈ cthickening δ A := mem_cthickening_of_dist_le q q₀ δ A hq₀ hnear.le
  have hQz := hquot q hq z (sphere_subset_closedBall hz)
  exact (norm_sourcePsiMidpointFilledRegularFactor_le_of_quotient_bound hp hp1 n m hmn (s n ψ) ψ z Q hQ hsep hQz).trans
    (by linarith)

/-- For a fixed selected chart, one beta constant works for every
sufficiently distant deleted index, preserving the actual gap weight. -/
theorem exists_local_distantDeleted_beta_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W₀ s) (hWW₀ : W ⊆ W₀)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n : ℤ, K < n.natAbs → m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
              sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  have hρ : 0 < ρ := D.inner_pos.trans hrρ
  obtain ⟨Uχ,hUχ,hφχ,hUχV,K,M,hM,hχ⟩ := D.exists_local_distantDeleted_regularFactor_circle_bound
    hs.toSourcePsiIsolatingComplexExtension φ hφ hreal ρ hrρ hρR
  obtain ⟨Ur,hUr,hφr,_,A,hA,hroots⟩ := hs.exists_local_uniform_retainedRoot_displacement_bound φ
    (hWW₀ (D.source_subset hφ))
  let B := A+‖(Real.pi:ℂ)*m-c m‖
  let C := ρ^2*(B+ρ)*M/(ρ-r)^3
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by have hd := sub_pos.mpr hrρ; dsimp only [C]; positivity
  refine ⟨Uχ ∩ Ur,hUχ.inter hUr,⟨hφχ,hφr⟩,inter_subset_left.trans hUχV,K,C,hC,?_⟩
  intro ψ hψ n hn hmn
  have hroot : ‖displacedRoots (s n ψ : Coeff p) m-c m‖ ≤ B := by
    rw [show displacedRoots (s n ψ : Coeff p) m-c m =
      (displacedRoots (s n ψ : Coeff p) m-(Real.pi:ℂ)*m)+((Real.pi:ℂ)*m-c m) by ring]
    exact (norm_add_le _ _).trans (add_le_add (hroots ψ hψ.2 n m hmn) le_rfl)
  have h := D.norm_beta_le_of_midpointFilledRegularFactor_bound ψ (hUχV hψ.1) n hmn ρ M hrρ hρR hM.le
    (hχ ψ hψ.1 n hn hmn)
  have hcoeff : ρ^2*(‖displacedRoots (s n ψ : Coeff p) m-c m‖+ρ)*M/(ρ-r)^3 ≤ C := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hroot (le_refl ρ)) (sq_nonneg _)) hM.le
  exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (abs_nonneg _))

/-- Every deleted index shares one local reciprocal-index beta estimate
on a fixed selected chart. Only a finite intersection of neighborhoods
is needed, so central selected gaps are fully covered. -/
theorem exists_local_uniform_deletedIndices_beta_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W₀ s) (hWW₀ : W ⊆ W₀)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n : ℤ, m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
              sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  classical
  obtain ⟨Ut,hUt,hφt,hUtV,K,Ct,hCt,htail⟩ := D.exists_local_distantDeleted_beta_bound hs hWW₀ φ hφ hreal
  have hlocal (n : ℤ) : ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-sourceStandardRootMidpoint hp hp1 ψ m‖) := by
    by_cases hmn : m = n
    · exact ⟨V,D.source_open,hφ,Subset.rfl,1,by norm_num,fun _ _ h => False.elim (h hmn)⟩
    · obtain ⟨U,hU,hφU,hUV,C,hC,hbound⟩ := D.exists_local_norm_beta_le_gap_weight φ hφ n hmn
      exact ⟨U,hU,hφU,hUV,C,hC,fun ψ hψ _ => hbound ψ hψ⟩
  choose Un hUn hφn _ Cn hCn hbound using hlocal
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ n ∈ S, ψ ∈ Un n := by
    rw [Finset.eventually_all]
    intro n _
    exact (hUn n).mem_nhds (hφn n)
  obtain ⟨H,hHsub,hH,hφH⟩ := _root_.mem_nhds_iff.mp hevent
  let J : ℝ := (K+m.natAbs+1:ℕ)
  let B := ∑ n ∈ S, Cn n
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hB : 0 ≤ B := Finset.sum_nonneg (fun n _ => (hCn n).le)
  let C := Ct+J*B
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨Ut ∩ H,hUt.inter hH,⟨hφt,hφH⟩,inter_subset_left.trans hUtV,C,hC,?_⟩
  intro ψ hψ n hmn
  by_cases hn : K < n.natAbs
  · exact (htail ψ hψ.1 n hn hmn).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hJ hB) : Ct ≤ C) (by positivity)) (abs_nonneg _))
  · have hnK : n.natAbs ≤ K := le_of_not_gt hn
    have hnS : n ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hnB : Cn n ≤ B := Finset.single_le_sum (fun k _ => (hCn k).le) hnS
    have hdJ : |((n-m : ℤ) : ℝ)| ≤ J := by
      have h : (n-m).natAbs ≤ K+m.natAbs+1 := by have ht := Int.natAbs_sub_le n m; omega
      have hcast : ((n-m).natAbs:ℝ) ≤ J := by dsimp only [J]; exact_mod_cast h
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hcast
    have hd : 0 < |((n-m : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hmn.symm)
    have hcoeff : Cn n*|((n-m : ℤ) : ℝ)| ≤ C := by
      have h := mul_le_mul hnB hdJ (abs_nonneg _) hB
      dsimp only [C]
      nlinarith
    apply (hbound n ψ (hHsub hψ.2 n hnS) hmn).trans
    apply (le_div_iff₀ hd).mpr
    calc
      _ = (Cn n*|((n-m : ℤ) : ℝ)|) * _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
