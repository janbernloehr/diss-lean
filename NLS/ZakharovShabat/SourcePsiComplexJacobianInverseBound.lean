import NLS.ZakharovShabat.SourcePsiAllIndexJacobianCharts
import NLS.ZakharovShabat.SourcePsiJacobianGapInverseBound
import NLS.SequenceSpaces.NearbyInverse

/-!
# Uniform actual inverses near the real psi gap product

At every gap-root vector, joint holomorphic bounds give a radius
independent of the deleted index. The common real inverse bound and
the Neumann perturbation estimate prove existence of actual two-sided
inverses throughout those complex balls, with one norm bound shared by
all root centers and all indices. No complex invertibility is assumed.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All gap centers have joint complex chart balls whose radius is
independent of the deleted index and whose full inverses share one
bound independent of both the center and the index. -/
theorem exists_uniform_local_sourcePsi_complexJacobian_inverses
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
      ∃ c : ℤ → ℤ → ℂ, ∃ R : ℤ → ℤ → ℝ,
        (∀ n : ℤ, sourcePsiRealCenteredContourFamily hp hp1 φ (c n) (R n)) ∧
        ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧ ∀ n : ℤ,
          sourcePsiJointJacobianControl hp hp1 n (c n) (R n)
            (Coeff.deleteCoordinateTo n a.val) φ δ L ∧
          ∀ t ∈ ball (Coeff.deleteCoordinateTo n a.val,φ) δ,
            ∃ S : Coeff p →L[ℂ] Coeff p,
              (sourcePsiFullRootJacobian hp hp1 n (c n) (R n) t.1 t.2).comp S =
                ContinuousLinearMap.id ℂ (Coeff p) ∧
              S.comp (sourcePsiFullRootJacobian hp hp1 n (c n) (R n) t.1 t.2) =
                ContinuousLinearMap.id ℂ (Coeff p) ∧ ‖S‖ ≤ M := by
  obtain ⟨c₀,R₀,hfamily₀,rest⟩ :=
    exists_common_sourcePsi_fullJacobian_jointLipschitz hp hp1 (0 : Coeff p) φ hφ
  obtain ⟨M₀,hM₀,hbound⟩ :=
    exists_uniform_sourcePsiGapJacobianInverse_norm hp hp1 φ hφ c₀ R₀ hfamily₀
  refine ⟨2*M₀,by positivity,?_⟩
  intro a
  obtain ⟨c,R,hfamily,r,L,hr,hL,hcharts⟩ :=
    exists_allIndex_sourcePsi_fullJacobian_jointLipschitz hp hp1 a.val φ hφ
  let ε : ℝ := 1/(2*(M₀+1)*(L+1))
  let δ := min r ε
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hδ : 0 < δ := lt_min hr hε
  have hδr : δ ≤ r := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  refine ⟨c,R,hfamily,δ,L,hδ,hL,?_⟩
  intro n
  refine ⟨sourcePsiJointJacobianControl.mono hp hp1 n (c n) (R n)
    (Coeff.deleteCoordinateTo n a.val) φ r δ L L (hcharts n) hδr le_rfl,?_⟩
  intro t ht
  let T := sourcePsiFullRootJacobian hp hp1 n (c n) (R n) t.1 t.2
  let Q := sourcePsiFullRootJacobian hp hp1 n c₀ R₀ (Coeff.deleteCoordinateTo n a.val) φ
  let S₀ := sourcePsiGapJacobianInverse hp hp1 φ hφ c₀ R₀ hfamily₀ n a
  have hbaseeq : sourcePsiFullRootJacobian hp hp1 n (c n) (R n)
      (Coeff.deleteCoordinateTo n a.val) φ = Q :=
    sourcePsiFullRootJacobian_eq_of_realCentered_families hp hp1 φ hφ
      (c n) c₀ (R n) R₀ (hfamily n) hfamily₀ n (Coeff.deleteCoordinateTo n a.val)
  have hdiff : ‖Q-T‖ ≤ L*δ := by
    have hLip := (hcharts n).2.2.1 t ((ball_subset_ball hδr) ht)
      (Coeff.deleteCoordinateTo n a.val,φ) (mem_ball_self hr)
    rw [hbaseeq,norm_sub_rev] at hLip
    exact hLip.trans (mul_le_mul_of_nonneg_left
      (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ht)) hL)
  have hnear : ‖S₀‖*‖Q-T‖ ≤ (1/2:ℝ) := by
    calc
      _ ≤ M₀*(L*δ) := mul_le_mul (hbound n a) hdiff (norm_nonneg _) hM₀
      _ ≤ (M₀+1)*((L+1)*ε) := by gcongr <;> linarith
      _ = 1/2 := by
        dsimp [ε]
        have hneM : M₀+1 ≠ 0 := by positivity
        have hneL : L+1 ≠ 0 := by positivity
        field_simp [hneM,hneL]
  obtain ⟨S,hTS,hST,hS⟩ := NLS.exists_inverse_norm_le_two_mul_of_near T Q S₀
    (sourcePsiFullRootJacobian_comp_gapInverse hp hp1 φ hφ c₀ R₀ hfamily₀ n a)
    (sourcePsiGapJacobianInverse_comp_fullRootJacobian hp hp1 φ hφ c₀ R₀ hfamily₀ n a) hnear
  exact ⟨S,hTS,hST,hS.trans (mul_le_mul_of_nonneg_left (hbound n a) (by norm_num))⟩

end NLS.ZakharovShabat
