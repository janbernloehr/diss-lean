import NLS.ZakharovShabat.SourcePsiJacobianSourceVariation

/-!
# One joint radius for all deleted psi Jacobian charts

The common escaping-index chart controls the tail. Bounded analytic
charts at each remaining index supply finitely many radii and constants.
Their minimum radius and maximum bound give joint analytic charts and
Jacobian Lipschitz estimates for every index on one neighborhood of a
fixed full root vector and real-type potential.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_local_sourcePsi_fullJacobian_jointLipschitz
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 φ c R ∧
      ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
        sourcePsiJointJacobianControl hp hp1 n c R a φ r L := by
  obtain ⟨U,hUopen,hbase,K,c,R,hcenter,hfree,hgeom,hiso,C,hC,hcoord,hbound,hreal,hdiff⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic hp hp1 φ hφ n a
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hUopen (a,φ) hbase
  let r := δ/4
  let L := 4*C/r^2
  have hr : 0 < r := by dsimp [r]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hfour : 4*r = δ := by dsimp [r]; ring
  have hsmall : r ≤ δ := by dsimp [r]; linarith
  have hinner : ball (a,φ) r ⊆ U := (ball_subset_ball hsmall).trans hball
  refine ⟨c,R,⟨hcenter,fun m => hgeom (a,φ) hbase m⟩,r,L,hr,hL,
    hdiff.mono hinner,(fun t ht m => hcoord t (hinner ht) m),?_,
    (fun t ht => ⟨hcenter,fun m => hgeom t (hinner ht) m⟩)⟩
  intro t ht u hu
  apply norm_sourcePsiFullRootJacobian_sub_le_of_joint_ball_bound hp hp1 n c R (a,φ) r C hr
    ?_ ?_ ht hu
  · rw [hfour]
    exact hdiff.mono hball
  · rw [hfour]
    exact fun t ht => hbound t (hball ht)

/-- The radius and Lipschitz constant do not depend on the deleted
index. Every contour family is valid at the real-type base potential;
all selected equations are actual analytic charts on the common ball. -/
theorem exists_allIndex_sourcePsi_fullJacobian_jointLipschitz
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℤ → ℤ → ℂ, ∃ R : ℤ → ℤ → ℝ,
      (∀ n : ℤ, sourcePsiRealCenteredContourFamily hp hp1 φ (c n) (R n)) ∧
      ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ n : ℤ,
        sourcePsiJointJacobianControl hp hp1 n (c n) (R n)
          (Coeff.deleteCoordinateTo n a) φ r L := by
  classical
  obtain ⟨ct,Rt,hfamilyt,rt,Lt,hrt,hLt,htail⟩ :=
    exists_common_sourcePsi_fullJacobian_jointLipschitz hp hp1 a φ hφ
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_comap.mp htail)
  have hhead (n : ℤ) := exists_local_sourcePsi_fullJacobian_jointLipschitz
    hp hp1 n (Coeff.deleteCoordinateTo n a) φ hφ
  choose ch Rh hfamilyh rh Lh hrh hLh hcharts using hhead
  let s : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ)
  have hs : s.Nonempty := ⟨0,by simp [s]⟩
  let r := min rt (s.inf' hs rh)
  let L := max Lt (∑ n ∈ s, Lh n)
  have hr : 0 < r := lt_min hrt ((Finset.lt_inf'_iff hs).2 (fun n _ => hrh n))
  have hL : 0 ≤ L := le_max_of_le_left hLt
  let c : ℤ → ℤ → ℂ := fun n => if K ≤ n.natAbs then ct else ch n
  let R : ℤ → ℤ → ℝ := fun n => if K ≤ n.natAbs then Rt else Rh n
  refine ⟨c,R,?_,r,L,hr,hL,?_⟩
  · intro n
    by_cases hn : K ≤ n.natAbs
    · simpa only [c,R,if_pos hn] using hfamilyt
    · simpa only [c,R,if_neg hn] using hfamilyh n
  · intro n
    by_cases hn : K ≤ n.natAbs
    · have hnt : sourcePsiJointJacobianControl hp hp1 n ct Rt
          (Coeff.deleteCoordinateTo n a) φ rt Lt := hK n.natAbs hn n rfl
      simpa only [c,R,if_pos hn] using sourcePsiJointJacobianControl.mono
        hp hp1 n ct Rt (Coeff.deleteCoordinateTo n a) φ rt r Lt L hnt
        (min_le_left _ _) (le_max_left _ _)
    · have hnabs : |n| ≤ (K:ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hn))
      have hns : n ∈ s := by simpa only [s,Finset.mem_Icc] using abs_le.mp hnabs
      have hrn : r ≤ rh n := (min_le_right _ _).trans (Finset.inf'_le rh hns)
      have hLn : Lh n ≤ L :=
        (Finset.single_le_sum (fun k _ => hLh k) hns).trans (le_max_right _ _)
      simpa only [c,R,if_neg hn] using sourcePsiJointJacobianControl.mono
        hp hp1 n (ch n) (Rh n) (Coeff.deleteCoordinateTo n a) φ (rh n) r (Lh n) L
          (hcharts n) hrn hLn

end NLS.ZakharovShabat
