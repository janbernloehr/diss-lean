import NLS.ZakharovShabat.SourcePsiGluedEquation
import NLS.ZakharovShabat.SourcePsiGapRootAnalyticExistence

/-!
# Uniform analytic equation tubes around the canonical psi solutions

Compactness of the full gap product supplies one joint radius for all
deleted indices. The glued equations have a common norm bound and
actual bounded root derivative inverses on these balls. Their values
at the real canonical roots vanish by real contour comparison.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any realization of the actual contour coordinates vanishes at a
gap solution, on every valid real-centered contour family. -/
theorem sourcePsiEquationRealization_zero_of_gapSolution
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a z : DeletedCoeff p n)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (hcoord : ∀ m, (z : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ (c m) (R m))
    (hsol : SourcePsiGapSolution hp hp1 n φ a) : z = 0 := by
  obtain ⟨hgap,c₀,R₀,hcenter₀,hgeom₀,hcoord₀,hzero₀⟩ := hsol
  apply Subtype.ext
  ext m
  calc
    (z : Coeff p) m = sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ (c m) (R m) := hcoord m
    _ = sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ (c₀ m) (R₀ m) :=
      sourcePsiEquationCoordinate_eq_of_realCentered_enclosingCircles hp hp1 n m (a : Coeff p) φ hφ
        (c m) (c₀ m) (R m) (R₀ m) (hfamily.1 m) (hcenter₀ m)
        (hfamily.2 m).1 (hgeom₀ m).1 (hfamily.2 m).2.1 (hgeom₀ m).2.1
        (hfamily.2 m).2.2.1 (hgeom₀ m).2.2
    _ = (sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ a φ : Coeff p) m := (hcoord₀ m).symm
    _ = ((0 : DeletedCoeff p n) : Coeff p) m := by rw [hzero₀]

/-- Quantitative data for the actual psi equations. The joint radius,
equation norm bound, and inverse norm bound are independent of the
deleted index. The root centers are the canonical real solutions. -/
structure SourcePsiUniformEquationTube
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) where
  equation : (n : ℤ) → DeletedCoeff p n × CoeffPair p → DeletedCoeff p n
  radius : ℝ
  normBound : ℝ
  inverseBound : ℝ
  radius_pos : 0 < radius
  normBound_nonneg : 0 ≤ normBound
  inverseBound_nonneg : 0 ≤ inverseBound
  analytic : ∀ n, AnalyticOnNhd ℂ (equation n)
    (ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*radius))
  norm_le : ∀ n, ∀ q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*radius),
    ‖equation n q‖ ≤ normBound
  zero : ∀ n, equation n (sourcePsiGapRoot hp hp1 n φ,φ.val) = 0
  contours : ∀ n, ∀ q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*radius),
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 q.2 c R ∧
      ∀ m, (equation n q : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m (q.1 : Coeff p) q.2 (c m) (R m)
  inverse : ∀ n, ∀ q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*radius),
    ∃ S : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
      (fderiv ℂ (fun b => equation n (b,q.2)) q.1).comp S = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
      S.comp (fderiv ℂ (fun b => equation n (b,q.2)) q.1) = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
      ‖S‖ ≤ inverseBound

theorem nonempty_sourcePsiUniformEquationTube
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) :
    Nonempty (SourcePsiUniformEquationTube hp hp1 φ) := by
  obtain ⟨U,hUopen,hUconv,hbase,V,hVopen,hprojection,F,hF,C,hC,hbound,M,hM,hdata⟩ :=
    exists_sourcePsi_gluedEquation_neighborhood hp hp1 φ.val φ.property
  let K : Set (Coeff p × CoeffPair p) := sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}
  have hK : IsCompact K := (isCompact_sourcePeriodicGapRootSet hp hp1 φ.val).prod
    (isCompact_singleton : IsCompact {φ.val})
  obtain ⟨ε,hε,htube⟩ := hK.exists_cthickening_subset_open hUopen hbase
  let r := ε/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hfour : 4*r = ε := by dsimp [r]; ring
  have hprojectSelf (n : ℤ) (b : DeletedCoeff p n) : Coeff.deleteCoordinateTo n (b : Coeff p) = b := by
    apply Subtype.ext
    exact (Coeff.deleteCoordinate_eq_self_iff n (b : Coeff p)).2 b.property
  have hball (n : ℤ) : ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*r) ⊆ V n := by
    intro q hq
    let a : Coeff p := sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ)
      (sourceStandardRootMidpoint hp hp1 φ.val n)
    have ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ.val :=
      sourcePsiGapRoot_filled_mem_periodicGapRootSet hp hp1 φ n
    have hdelete : Coeff.deleteCoordinateTo n a = sourcePsiGapRoot hp hp1 n φ :=
      deleteCoordinateTo_sourcePsiFillDeletedRoot n _ _
    let t : Coeff p × CoeffPair p :=
      (a + ((q.1-sourcePsiGapRoot hp hp1 n φ : DeletedCoeff p n) : Coeff p),q.2)
    have ht : t ∈ U := by
      apply htube
      apply mem_cthickening_of_dist_le t (a,φ.val) ε K ⟨ha,mem_singleton φ.val⟩
      have hd : dist t (a,φ.val) = dist q (sourcePsiGapRoot hp hp1 n φ,φ.val) := by
        simp only [dist_eq_norm]
        change max ‖a + ((q.1-sourcePsiGapRoot hp hp1 n φ : DeletedCoeff p n) : Coeff p) - a‖
          ‖q.2-φ.val‖ = max ‖q.1-sourcePsiGapRoot hp hp1 n φ‖ ‖q.2-φ.val‖
        rw [add_sub_cancel_left]
        rfl
      rw [hd]
      exact le_of_lt (by simpa only [mem_ball,hfour] using hq)
    have hproj : (Coeff.deleteCoordinateTo n t.1,t.2) = q := by
      apply Prod.ext
      · change Coeff.deleteCoordinateTo n (a + ((q.1-sourcePsiGapRoot hp hp1 n φ : DeletedCoeff p n) : Coeff p)) = q.1
        rw [map_add,hprojectSelf,hdelete,add_sub_cancel]
      · rfl
    rw [← hproj]
    exact hprojection t ht n
  refine ⟨{
    equation := F, radius := r, normBound := C, inverseBound := M,
    radius_pos := hr, normBound_nonneg := hC, inverseBound_nonneg := hM,
    analytic := fun n => (hF n).mono (hball n),
    norm_le := fun n q hq => hbound n q (hball n hq),
    zero := ?_,
    contours := fun n q hq => (hdata n q (hball n hq)).1,
    inverse := fun n q hq => (hdata n q (hball n hq)).2.2
  }⟩
  intro n
  obtain ⟨c,R,hfamily,hcoord⟩ :=
    (hdata n (sourcePsiGapRoot hp hp1 n φ,φ.val)
      (hball n (mem_ball_self (by positivity)))).1
  exact sourcePsiEquationRealization_zero_of_gapSolution hp hp1 n φ.val φ.property
    (sourcePsiGapRoot hp hp1 n φ) _ c R hfamily hcoord (sourcePsiGapRoot_solution hp hp1 n φ)

end NLS.ZakharovShabat
