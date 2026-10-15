import NLS.ZakharovShabat.SourcePsiOriginalLimitCanonical
import NLS.ZakharovShabat.SourcePsiAllIndexJacobianCharts

/-!
# Continuity of Q* on the full original domain

A common joint analytic chart bounds changes in every full original
Jacobian by the joint root/source distance. Lower semicontinuity of the
operator norm passes this estimate to Q*. Thus Q* is locally Lipschitz
and continuous on the original domain at real-type sources, without
assuming that the roots lie in their spectral gaps.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coordinate deletion contracts the joint root/source distance. -/
theorem norm_sourcePsiDeletedPair_sub_le (n : ℤ) (t u : Coeff p × CoeffPair p) :
    ‖(Coeff.deleteCoordinateTo n t.1,t.2)-(Coeff.deleteCoordinateTo n u.1,u.2)‖ ≤ ‖t-u‖ := by
  have hd := (Coeff.deleteCoordinateTo (p := p) n).le_of_opNorm_le
    (Coeff.norm_deleteCoordinateTo_le_one n) (t.1-u.1)
  simp only [map_sub,one_mul] at hd
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub] using max_le_max hd (le_refl ‖t.2-u.2‖)

/-- Every original full Jacobian shares one local Lipschitz bound at real-type sources.
The right-hand side controls both the root and source variables. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_local_Lipschitz
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ n : ℤ,
      ∀ t ∈ ball (a,φ) r, t.2 ∈ W → IsRealType (CoeffPair.toMax p t.2) →
      ∀ u ∈ ball (a,φ) r, u.2 ∈ W → IsRealType (CoeffPair.toMax p u.2) →
        ‖sourcePsiOriginalFullRootJacobian hp hp1 n t.1 t.2 -
          sourcePsiOriginalFullRootJacobian hp hp1 n u.1 u.2‖ ≤ L*‖t-u‖ := by
  obtain ⟨c,R,_,r,L,hr,hL,hchart⟩ := exists_allIndex_sourcePsi_fullJacobian_jointLipschitz hp hp1 a φ hφ
  have hball (n : ℤ) (t : Coeff p × CoeffPair p) (ht : t ∈ ball (a,φ) r) :
      (Coeff.deleteCoordinateTo n t.1,t.2) ∈ ball (Coeff.deleteCoordinateTo n a,φ) r := by
    rw [mem_ball,dist_eq_norm] at ht ⊢
    exact (norm_sourcePsiDeletedPair_sub_le n t (a,φ)).trans_lt ht
  refine ⟨r,L,hr,hL,?_⟩
  intro n t ht htW htr u hu huW hur
  have ht' := hball n t ht
  have hu' := hball n u hu
  rw [H.originalFullRootJacobian_eq_selected t.2 htW htr (c n) (R n) ((hchart n).2.2.2.1 (Coeff.deleteCoordinateTo n t.1,t.2) ht'),
    H.originalFullRootJacobian_eq_selected u.2 huW hur (c n) (R n) ((hchart n).2.2.2.1 (Coeff.deleteCoordinateTo n u.1,u.2) hu')]
  exact ((hchart n).2.2.1 (Coeff.deleteCoordinateTo n t.1,t.2) ht' (Coeff.deleteCoordinateTo n u.1,u.2) hu').trans
    (mul_le_mul_of_nonneg_left (norm_sourcePsiDeletedPair_sub_le n t u) hL)

/-- The original placed-root domain with real-type sources and complex root coordinates. -/
def sourcePsiOriginalLimitDomain (W V : Set (CoeffPair p)) (D : ℤ → Set ℂ) :
    Set (Coeff p × CoeffPair p) :=
  {t | t.2 ∈ W ∧ t.2 ∈ V ∧ IsRealType (CoeffPair.toMax p t.2) ∧
    t.1 ∈ sourcePsiOriginalRootPlacement D}

/-- The same joint bound passes to the intrinsic Q* on the entire original domain. -/
theorem SourceLemma12_4Data.originalLimitOperator_local_Lipschitz
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (a : Coeff p) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ t ∈ ball (a,φ) r, t ∈ sourcePsiOriginalLimitDomain W V D →
      ∀ u ∈ ball (a,φ) r, u ∈ sourcePsiOriginalLimitDomain W V D →
        ‖sourcePsiOriginalLimitOperator hp hp1 t.1 t.2 -
          sourcePsiOriginalLimitOperator hp hp1 u.1 u.2‖ ≤ L*‖t-u‖ := by
  let l : Filter ℤ := Filter.comap Int.natAbs atTop
  let : NeBot l := (inferInstance : NeBot (atTop : Filter ℕ)).comap_of_surj Int.natAbs_surjective
  obtain ⟨r,L,hr,hL,hb⟩ := H.originalFullRootJacobian_local_Lipschitz a φ hφ
  refine ⟨r,L,hr,hL,?_⟩
  intro t ht htD u hu huD
  have htlim := H.originalLimitOperator_spec hD t.2 htD.1 htD.2.1 htD.2.2.1 t.1 htD.2.2.2
  have hulim := H.originalLimitOperator_spec hD u.2 huD.1 huD.2.1 huD.2.2.1 u.1 huD.2.2.2
  apply Coeff.opNorm_le_of_coordinatewise_limit l
    (fun n => sourcePsiOriginalFullRootJacobian hp hp1 n t.1 t.2 -
      sourcePsiOriginalFullRootJacobian hp hp1 n u.1 u.2)
    (sourcePsiOriginalLimitOperator hp hp1 t.1 t.2 - sourcePsiOriginalLimitOperator hp hp1 u.1 u.2)
    (L*‖t-u‖) (mul_nonneg hL (norm_nonneg _))
  · exact Filter.Eventually.of_forall (fun n => hb n t ht htD.1 htD.2.2.1 u hu huD.1 huD.2.2.1)
  · intro x m
    exact (htlim x m).sub (hulim x m)

/-- The original limit operator is continuous in the full root/source topology. -/
theorem SourceLemma12_4Data.originalLimitOperator_continuousOn
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    ContinuousOn (fun t : Coeff p × CoeffPair p => sourcePsiOriginalLimitOperator hp hp1 t.1 t.2)
      (sourcePsiOriginalLimitDomain W V D) := by
  intro t ht
  obtain ⟨r,L,hr,hL,hb⟩ := H.originalLimitOperator_local_Lipschitz hD t.1 t.2 ht.2.2.1
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min r (ε/(L+1)),lt_min hr (div_pos hε (by positivity)),?_⟩
  intro u hu hud
  have hur : u ∈ ball t r := hud.trans_le (min_le_left _ _)
  have hd : ‖u-t‖ < ε/(L+1) := by
    simpa only [dist_eq_norm] using hud.trans_le (min_le_right _ _)
  rw [dist_eq_norm]
  apply (hb u hur hu t (mem_ball_self hr) ht).trans_lt
  have hpos : 0 < L+1 := by positivity
  have hmul := (lt_div_iff₀ hpos).mp hd
  nlinarith [norm_nonneg (u-t)]

end NLS.ZakharovShabat
