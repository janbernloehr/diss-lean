import NLS.ZakharovShabat.SourcePsiAllIndexJacobianCharts

/-!
# SourcePsiCompactJointCharts

One radius and one joint analytic chart bound work at every center
of a compact root set and every signed deleted index.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Shrinking and recentering a chart preserves its actual equation,
geometry and joint Jacobian estimate. -/
theorem sourcePsiJointJacobianControl.recenter
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a b : DeletedCoeff p n) (φ : CoeffPair p) (r δ L B : ℝ)
    (h : sourcePsiJointJacobianControl hp hp1 n c R a φ r L)
    (hball : ball (b,φ) δ ⊆ ball (a,φ) r) (hL : L ≤ B) :
    sourcePsiJointJacobianControl hp hp1 n c R b φ δ B := by
  refine ⟨h.1.mono hball,(fun t ht m => h.2.1 t (hball ht) m),?_,
    (fun t ht => h.2.2.2.1 t (hball ht)),
    (fun t ht => (h.2.2.2.2 t (hball ht)).trans hL)⟩
  intro t ht u hu
  exact (h.2.2.1 t (hball ht) u (hball hu)).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- One positive radius and one joint Lipschitz bound work at every
center of any compact root set and every signed deleted index. -/
theorem exists_compact_sourcePsi_fullJacobian_jointLipschitz
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (K : Set (Coeff p)) (hK : IsCompact K) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ ∀ a ∈ K,
      ∃ c : ℤ → ℤ → ℂ, ∃ R : ℤ → ℤ → ℝ,
        (∀ n : ℤ, sourcePsiRealCenteredContourFamily hp hp1 φ (c n) (R n)) ∧
        ∀ n : ℤ, sourcePsiJointJacobianControl hp hp1 n (c n) (R n)
          (Coeff.deleteCoordinateTo n a) φ δ B := by
  classical
  have hlocal (a : Coeff p) := exists_allIndex_sourcePsi_fullJacobian_jointLipschitz hp hp1 a φ hφ
  choose c R hfamily r L hr hL hcharts using hlocal
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun a : Coeff p => ball a (r a/2))
    (fun _ => isOpen_ball) (fun a _ => mem_iUnion.mpr ⟨a,mem_ball_self (half_pos (hr a))⟩)
  by_cases hsnon : s.Nonempty
  · let δ := s.inf' hsnon (fun a => r a/2)
    let B := ∑ a ∈ s, L a
    have hδ : 0 < δ := (Finset.lt_inf'_iff hsnon).2 (fun a _ => half_pos (hr a))
    have hB : 0 ≤ B := Finset.sum_nonneg (fun a _ => hL a)
    refine ⟨δ,B,hδ,hB,?_⟩
    intro a ha
    obtain ⟨b,hbs,hab⟩ := mem_iUnion₂.mp (hs ha)
    have hδb : δ ≤ r b/2 := Finset.inf'_le _ hbs
    have hLb : L b ≤ B := Finset.single_le_sum (fun j _ => hL j) hbs
    refine ⟨c b,R b,hfamily b,?_⟩
    intro n
    apply sourcePsiJointJacobianControl.recenter hp hp1 n (c b n) (R b n)
      (Coeff.deleteCoordinateTo n b) (Coeff.deleteCoordinateTo n a) φ (r b) δ (L b) B (hcharts b n) ?_ hLb
    intro t ht
    have hproj : dist (Coeff.deleteCoordinateTo n a) (Coeff.deleteCoordinateTo n b) ≤ dist a b := by
      rw [dist_eq_norm,dist_eq_norm,← map_sub]
      simpa only [one_mul] using (Coeff.deleteCoordinateTo (p := p) n).le_of_opNorm_le
        (Coeff.norm_deleteCoordinateTo_le_one n) (a-b)
    have hab' : dist (Coeff.deleteCoordinateTo n a,φ) (Coeff.deleteCoordinateTo n b,φ) < r b/2 := by
      simpa only [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg)] using hproj.trans_lt (mem_ball.mp hab)
    have hdist := dist_triangle t (Coeff.deleteCoordinateTo n a,φ) (Coeff.deleteCoordinateTo n b,φ)
    rw [mem_ball] at ht ⊢
    linarith
  · refine ⟨1,0,by norm_num,le_rfl,?_⟩
    intro a ha
    obtain ⟨b,hbs,_⟩ := mem_iUnion₂.mp (hs ha)
    exact (hsnon ⟨b,hbs⟩).elim

end NLS.ZakharovShabat
