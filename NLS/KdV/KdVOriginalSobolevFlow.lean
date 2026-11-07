import NLS.KdV.KdVOriginalSobolevModel
import NLS.Articles.KdVPseudomeasures.OriginalHillClassicalRoughSolution

/-! Global KdV in the article's exact original mean-zero H^m domains.
The imported genuine physical construction supplies classical approximants;
no frequency family, conserved invariant, or existence witness is assumed.
Uniqueness is for the explicitly stated universal classical-approximation
solution concept, not all spacetime distributional solutions. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.WeightedCoeff NLS.Articles.KdVPseudomeasures
namespace NLS.KdV

def kdvSobolevRoughEmbedding (m : ℕ) (q : KdVMeanZeroSobolev m) : HillRealMeanZeroSource :=
  hillIntegerSourceInclusion m (kdvOriginalSobolevHomeomorph m q)

theorem kdvSobolevRoughEmbedding_apply (m : ℕ) (q : KdVMeanZeroSobolev m) (k : ℤ) :
    (kdvSobolevRoughEmbedding m q).val.val.val k = q.val.val.val k := by
  rw [kdvSobolevRoughEmbedding,hillIntegerSourceInclusion_apply]
  exact kdvOriginalToSigned_apply m q k

theorem kdvSobolevRoughEmbedding_injective (m : ℕ) : Function.Injective (kdvSobolevRoughEmbedding m) :=
  (hillIntegerSourceInclusion_injective m).comp (kdvOriginalSobolevHomeomorph m).injective

def kdvSobolevFlow (m : ℕ) (q : KdVMeanZeroSobolev m) (t : ℝ) : KdVMeanZeroSobolev m :=
  (kdvOriginalSobolevHomeomorph m).symm
    (hillIntegerCanonicalKdVFlow m (kdvOriginalSobolevHomeomorph m q) t)

theorem kdvSobolevFlow_zero (m : ℕ) (q : KdVMeanZeroSobolev m) : kdvSobolevFlow m q 0 = q := by
  rw [kdvSobolevFlow,hillIntegerCanonicalKdVFlow_zero,Homeomorph.symm_apply_apply]

theorem kdvSobolevFlow_add (m : ℕ) (q : KdVMeanZeroSobolev m) (s t : ℝ) :
    kdvSobolevFlow m (kdvSobolevFlow m q s) t = kdvSobolevFlow m q (t+s) := by
  unfold kdvSobolevFlow
  rw [Homeomorph.apply_symm_apply,hillIntegerCanonicalKdVFlow_add]

theorem continuous_kdvSobolevFlow (m : ℕ) :
    Continuous (fun x : ℝ × KdVMeanZeroSobolev m => kdvSobolevFlow m x.2 x.1) := by
  let e := kdvOriginalSobolevHomeomorph m
  have hi : Continuous (fun x : ℝ × KdVMeanZeroSobolev m => (x.1,e x.2)) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  have h := e.symm.continuous.comp ((continuous_hillIntegerCanonicalKdVFlow m).comp hi)
  simpa only [kdvSobolevFlow,e,Function.comp_def] using! h

theorem continuous_kdvSobolevFlow_time (m : ℕ) (q : KdVMeanZeroSobolev m) :
    Continuous (kdvSobolevFlow m q) := by
  have hi : Continuous (fun t : ℝ => (t,q)) := continuous_id.prodMk continuous_const
  have h := (continuous_kdvSobolevFlow m).comp hi
  simpa only [Function.comp_def] using! h

/-- The original entire physical distribution of this strong H^m flow is
exactly the already constructed genuine physical rough KdV solution. -/
theorem kdvSobolevFlow_rough (m : ℕ) (q : KdVMeanZeroSobolev m) (t : ℝ) :
    kdvSobolevRoughEmbedding m (kdvSobolevFlow m q t) =
      hillRoughCanonicalKdVFlow (kdvSobolevRoughEmbedding m q) t := by
  unfold kdvSobolevRoughEmbedding kdvSobolevFlow
  rw [Homeomorph.apply_symm_apply,hillIntegerCanonicalKdVFlow_inclusion]

/-- The intended approximation formulation is explicit: every genuine
jointly smooth classical family with convergent initial data converges to
the solution at every time. Its nonvacuity is proved in the imported physical
construction, and continuity here is in the article's original H^m norm. -/
def IsSobolevKdVSolution (m : ℕ) (q : KdVMeanZeroSobolev m)
    (u : ℝ → KdVMeanZeroSobolev m) : Prop :=
  Continuous u ∧ HillRoughSolutionByClassicalApproximation (kdvSobolevRoughEmbedding m q)
    (fun t => kdvSobolevRoughEmbedding m (u t))

theorem kdvSobolevFlow_is_solution (m : ℕ) (q : KdVMeanZeroSobolev m) :
    IsSobolevKdVSolution m q (kdvSobolevFlow m q) := by
  refine ⟨continuous_kdvSobolevFlow_time m q,?_⟩
  have he : (fun t => kdvSobolevRoughEmbedding m (kdvSobolevFlow m q t)) =
      hillRoughCanonicalKdVFlow (kdvSobolevRoughEmbedding m q) := funext (kdvSobolevFlow_rough m q)
  rw [he]
  exact hillCanonicalFlow_is_roughSolutionByClassicalApproximation _

/-- Global existence and uniqueness for every original real mean-zero H^m
datum, with strong H^m time continuity and continuous dependence. -/
theorem existsUnique_sobolevKdVSolution (m : ℕ) (q : KdVMeanZeroSobolev m) :
    ∃! u : ℝ → KdVMeanZeroSobolev m, IsSobolevKdVSolution m q u := by
  refine ⟨kdvSobolevFlow m q,kdvSobolevFlow_is_solution m q,?_⟩
  intro u hu
  have he := hillRoughSolutionByClassicalApproximation_unique _ _ hu.2
  funext t
  apply kdvSobolevRoughEmbedding_injective m
  exact (congrFun he t).trans (kdvSobolevFlow_rough m q t).symm

/-- Equivalence with the nonvacuous intended classical-approximation
solution formulation, rather than an assumed invariant or coordinate ODE. -/
theorem isSobolevKdVSolution_iff_eq_flow (m : ℕ) (q : KdVMeanZeroSobolev m)
    (u : ℝ → KdVMeanZeroSobolev m) :
    IsSobolevKdVSolution m q u ↔ u = kdvSobolevFlow m q := by
  constructor
  · intro hu
    exact (existsUnique_sobolevKdVSolution m q).unique hu (kdvSobolevFlow_is_solution m q)
  · rintro rfl
    exact kdvSobolevFlow_is_solution m q

/-- Strong Sobolev persistence for an initially rough-typed weak solution:
H^m membership and continuity of its entire lift are conclusions. -/
theorem roughKdVSolution_has_unique_sobolev_lift (m : ℕ) (q : KdVMeanZeroSobolev m)
    (γ : ℝ → HillRealMeanZeroSource)
    (hγ : HillRoughSolutionByClassicalApproximation (kdvSobolevRoughEmbedding m q) γ) :
    ∃! u : ℝ → KdVMeanZeroSobolev m,
      Continuous u ∧ u 0 = q ∧ ∀ t, kdvSobolevRoughEmbedding m (u t) = γ t := by
  have he := hillRoughSolutionByClassicalApproximation_unique _ _ hγ
  refine ⟨kdvSobolevFlow m q,⟨(kdvSobolevFlow_is_solution m q).1,kdvSobolevFlow_zero m q,?_⟩,?_⟩
  · intro t
    exact (kdvSobolevFlow_rough m q t).trans (congrFun he t).symm
  · intro u hu
    funext t
    apply kdvSobolevRoughEmbedding_injective m
    exact (hu.2.2 t).trans ((congrFun he t).trans (kdvSobolevFlow_rough m q t).symm)

/-- The literal coefficient-preserving inclusion of the article domains. -/
def kdvSobolevLower (M j : ℕ) (hj : j ≤ M) (q : KdVMeanZeroSobolev M) : KdVMeanZeroSobolev j :=
  ⟨hillRealNativeIntegerLower M j hj q.val,hillRealNativeIntegerLower_mean_zero M j hj q.val q.property⟩

theorem kdvSobolevLower_rough (M j : ℕ) (hj : j ≤ M) (q : KdVMeanZeroSobolev M) :
    kdvSobolevRoughEmbedding j (kdvSobolevLower M j hj q) = kdvSobolevRoughEmbedding M q := by
  apply hillRealMeanZeroInclusion_injective
  apply Subtype.ext
  funext k
  change (kdvSobolevRoughEmbedding j (kdvSobolevLower M j hj q)).val.val.val k =
    (kdvSobolevRoughEmbedding M q).val.val.val k
  rw [kdvSobolevRoughEmbedding_apply,kdvSobolevRoughEmbedding_apply]
  exact hillNativeIntegerLower_apply M j hj q.val.val k

/-- Restrictions to different original Sobolev orders give the same flow,
not merely separate families of norm-compatible witnesses. -/
theorem kdvSobolevFlow_order_compatibility (M j : ℕ) (hj : j ≤ M)
    (q : KdVMeanZeroSobolev M) (t : ℝ) :
    kdvSobolevFlow j (kdvSobolevLower M j hj q) t = kdvSobolevLower M j hj (kdvSobolevFlow M q t) := by
  apply kdvSobolevRoughEmbedding_injective j
  rw [kdvSobolevFlow_rough,kdvSobolevLower_rough,kdvSobolevLower_rough,kdvSobolevFlow_rough]

end NLS.KdV
