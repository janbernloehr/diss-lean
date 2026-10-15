import NLS.ZakharovShabat.SourceLemma12_11
import NLS.SequenceSpaces.DominatedCompactness

/-!
# The original family: squared-gap offsets and compactness

The literal all-index factorization retains exactly the preceding complex
domain and roots. Its common lp bounds also place all midpoint-filled root
vectors at each complex source in one norm-compact set.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Literal all-index squared-gap factorization and p-power sum on the unchanged W. -/
theorem SourceLemma12_11Data.original_filled_offsets_power_sum
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ χ ∈ V, ∀ n : ℤ, ∃ α : Coeff p, α n = 0 ∧
        (∀ m, displacedRoots (sourcePsiFillDeletedRoot n (s n χ)
          (sourceStandardRootMidpoint hp hp1 χ n)) m =
            sourceStandardRootMidpoint hp hp1 χ m+(sourcePeriodicGapDisplacement hp hp1 χ m)^2*α m) ∧
        Summable (fun m : ℤ => ‖α m‖^p.toReal) ∧
        (∑' m : ℤ, ‖α m‖^p.toReal) ≤ C := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  obtain ⟨V,hV,hψV,hVW,L,hL,hbound⟩ := H.previous.psi.locally_uniform_offsets ψ hψ
  refine ⟨V,hV,hψV,hVW,L^p.toReal,Real.rpow_pos_of_pos hL _,?_⟩
  intro χ hχ n
  obtain ⟨α,hαn,hfactor,hαnorm⟩ := hbound χ hχ n
  refine ⟨α,hαn,?_,(lp.memℓp α).summable hpr,?_⟩
  · intro m
    by_cases hmn : m = n
    · subst m
      rw [displacedRoots_sourcePsiFillDeletedRoot_same,hαn,mul_zero,add_zero]
    · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hmn]
      exact hfactor m hmn
  · rw [← lp.norm_rpow_eq_tsum hpr α]
    exact Real.rpow_le_rpow (norm_nonneg _) hαnorm hpr.le

/-- Collapsed complex gaps force the actual filled root to equal the moving midpoint. -/
theorem SourceLemma12_11Data.original_collapsed_root_eq_midpoint
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n m : ℤ) (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0) :
    displacedRoots (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)) m =
      sourceStandardRootMidpoint hp hp1 ψ m := by
  obtain ⟨V,_,hψV,_,C,_,hb⟩ := H.original_filled_offsets_power_sum ψ hψ
  obtain ⟨α,_,he,_,_⟩ := hb ψ hψV n
  simpa only [hgap,zero_pow (by decide : 2 ≠ 0),zero_mul,add_zero] using he m

/-- At every complex source, one compact set contains all midpoint-filled root vectors. -/
theorem SourceLemma12_11Data.original_filled_rootFamily_compact
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ K : Set (Coeff p), IsCompact K ∧ ∀ n : ℤ,
      sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n) ∈ K := by
  obtain ⟨V,_,hψV,_,L,hL,hb⟩ := H.previous.psi.locally_uniform_offsets ψ hψ
  let τ := sourcePeriodicMidpointDisplacement hp hp1 ψ
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ
  let C : ℝ := L*‖γ‖
  have hC : 0 ≤ C := mul_nonneg hL.le (norm_nonneg _)
  let b : Coeff p := Coeff.magnitude τ+(C:ℂ) • Coeff.magnitude γ
  have hbpoint (m : ℤ) : ‖b m‖ = ‖τ m‖+C*‖γ m‖ := by
    simp only [b,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,Coeff.magnitude_apply,
      smul_eq_mul,← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ ‖τ m‖+C*‖γ m‖)]
  let K : Set (Coeff p) := {a | ∀ m : ℤ, ‖a m‖ ≤ ‖b m‖}
  have hKclosed : IsClosed K := by
    simp only [K,ofPred_forall]
    exact isClosed_iInter (fun m => isClosed_le
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous.norm) continuous_const)
  refine ⟨K,Coeff.isCompact_of_isClosed_of_majorant hp b hKclosed (fun _ ha => ha),?_⟩
  intro n
  obtain ⟨α,hαn,hfactor,hαnorm⟩ := hb ψ hψV n
  let a := sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)
  have hfactor' (m : ℤ) : a m = τ m+(γ m)^2*α m := by
    have he : displacedRoots a m = sourceStandardRootMidpoint hp hp1 ψ m+(γ m)^2*α m := by
      by_cases hm : m = n
      · subst m
        simp only [a,displacedRoots_sourcePsiFillDeletedRoot_same,hαn,mul_zero,add_zero]
      · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hm]
        exact hfactor m hm
    simp only [displacedRoots,τ,sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] at he ⊢
    linear_combination he
  intro m
  change ‖a m‖ ≤ ‖b m‖
  rw [hfactor',hbpoint]
  have hα : ‖α m‖ ≤ L := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' α m).trans hαnorm
  have hγ : ‖γ m‖ ≤ ‖γ‖ := lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' γ m
  calc
    ‖τ m+(γ m)^2*α m‖ ≤ ‖τ m‖+‖γ m‖^2*‖α m‖ := by
      convert norm_add_le (τ m) ((γ m)^2*α m) using 1
      rw [_root_.norm_mul,_root_.norm_pow]
    _ ≤ ‖τ m‖+(‖γ m‖*‖γ‖)*L := by
      gcongr
      calc
        ‖γ m‖^2 = ‖γ m‖*‖γ m‖ := pow_two _
        _ ≤ ‖γ m‖*‖γ‖ := mul_le_mul_of_nonneg_left hγ (norm_nonneg _)
    _ = ‖τ m‖+C*‖γ m‖ := by dsimp [C]; ring

/-- Symmetric spectral analyticity and uniform tails give midpoint sequence continuity. -/
theorem SourceLemma12_11Data.original_midpoint_continuous
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ContinuousAt (sourcePeriodicMidpointDisplacement hp hp1) ψ := by
  apply Coeff.continuousAt_of_coordinatewise_of_uniform_tails
  · intro n
    have h := (H.previous.psi.previous.quotients.roots.roots.symmetric.midpoint n ψ
      (H.previous.subset hψ)).continuousAt
    convert h.sub (continuousAt_const (y := (Real.pi:ℂ)*n)) using 1
    · rfl
    · funext χ
      exact sourcePeriodicMidpointDisplacement_apply hp hp1 χ n
  · intro ε hε
    obtain ⟨N,_,V,ho,hψV,R,hR,hb⟩ :=
      exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 ψ hε
    exact ⟨Finset.Icc (-(N:ℤ)) (N:ℤ),V,ho,hψV,fun χ hχ => (hb χ hχ).2 N le_rfl⟩

/-- All deleted branches are equicontinuous at every complex source of the same W. -/
theorem SourceLemma12_11Data.original_branch_dist_bound
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ball ψ r ⊆ W ∧
      ∀ χ ∈ ball ψ r, ∀ n : ℤ, dist (s n χ) (s n ψ) ≤ L*dist χ ψ := by
  obtain ⟨A,hdom,hbranch⟩ := H.previous.atlas
  let B := A.toSourcePsiComplexRootAtlas
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hdom.symm ▸ hψ)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (isOpen_ball : IsOpen (B.sourceBall φ)) ψ hφ
  let T := (B.localBranch φ).rootRadius+
    ‖canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)‖+
    ‖sourcePeriodicGapDisplacement hp hp1 φ.val‖
  have hT : 0 ≤ T := by
    have hh := (B.localBranch φ).rootRadius_pos
    dsimp only [T]; positivity
  have hsub : ball ψ r ⊆ W := by
    rw [← hdom]
    exact hball.trans (subset_iUnion B.sourceBall φ)
  have hb (n : ℤ) (χ : CoeffPair p) (hχ : χ ∈ ball ψ r) : ‖s n χ‖ ≤ T := by
    rw [← hbranch,B.eq_local n φ (hball hχ)]
    exact (B.localBranch φ).norm_branch_le n χ (hball hχ)
  refine ⟨r,2*T/r,hr,by positivity,hsub,?_⟩
  intro χ hχ n
  have hmaps : MapsTo (s n) (ball ψ r) (closedBall (s n ψ) (2*T)) := by
    intro θ hθ
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb n θ hθ,hb n ψ (mem_ball_self hr)])
  exact Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((H.previous.analytic n).mono hsub).differentiableOn hmaps hχ

/-- One radius controls every midpoint-filled root graph at a complex base source. -/
theorem SourceLemma12_11Data.original_filled_graph_radius
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball ψ r ⊆ W ∧ ∀ χ ∈ ball ψ r, ∀ n : ℤ,
      dist (sourcePsiFillDeletedRoot n (s n χ) (sourceStandardRootMidpoint hp hp1 χ n),χ)
        (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ) < ε := by
  obtain ⟨R,L,hR,hL,hRW,hbranch⟩ := H.original_branch_dist_bound ψ hψ
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp
    ((H.original_midpoint_continuous ψ hψ).preimage_mem_nhds
      (ball_mem_nhds _ (by positivity : 0 < ε/4)))
  let r := min R (min η (ε/(4*(L+1))))
  have hr : 0 < r := lt_min hR (lt_min hη (by positivity))
  have hrR : r ≤ R := min_le_left _ _
  have hrη : r ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε/(4*(L+1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,(ball_subset_ball hrR).trans hRW,?_⟩
  intro χ hχ n
  have hχdist : dist χ ψ < ε/(4*(L+1)) := (mem_ball.mp hχ).trans_le hrε
  have hmidseq : ‖sourcePeriodicMidpointDisplacement hp hp1 χ-
      sourcePeriodicMidpointDisplacement hp hp1 ψ‖ < ε/4 := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hηball (ball_subset_ball hrη hχ)
  have hmid : ‖sourceStandardRootMidpoint hp hp1 χ n-sourceStandardRootMidpoint hp hp1 ψ n‖ < ε/4 := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 χ-sourcePeriodicMidpointDisplacement hp hp1 ψ) n).trans_lt hmidseq
    simpa only [lp.coeFn_sub,Pi.sub_apply,sourcePeriodicMidpointDisplacement_apply,
      sub_sub_sub_cancel_right] using h
  have heq : sourcePsiFillDeletedRoot n (s n χ) (sourceStandardRootMidpoint hp hp1 χ n)-
      sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n) =
      ((s n χ:Coeff p)-(s n ψ:Coeff p))+
        lp.single p n (sourceStandardRootMidpoint hp hp1 χ n-sourceStandardRootMidpoint hp hp1 ψ n) := by
    unfold sourcePsiFillDeletedRoot
    rw [add_sub_add_comm,← lp.single_sub]
    congr 2
    ring
  have hfilled : dist
      (sourcePsiFillDeletedRoot n (s n χ) (sourceStandardRootMidpoint hp hp1 χ n))
      (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)) ≤ L*dist χ ψ+ε/4 := by
    rw [dist_eq_norm,heq]
    exact (norm_add_le _ _).trans (add_le_add (by
      change ‖s n χ-s n ψ‖ ≤ L*dist χ ψ
      simpa only [dist_eq_norm] using hbranch χ (ball_subset_ball hrR hχ) n)
      (by simpa only [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))] using hmid.le))
  rw [Prod.dist_eq,max_lt_iff]
  have hsmall : (L+1)*dist χ ψ < ε/4 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4*(L+1))).mp hχdist
    nlinarith
  constructor <;> nlinarith [dist_nonneg (x := χ) (y := ψ),mul_nonneg hL (dist_nonneg (x := χ) (y := ψ))]

end NLS.ZakharovShabat
