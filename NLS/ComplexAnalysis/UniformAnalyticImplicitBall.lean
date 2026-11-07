import NLS.ComplexAnalysis.UniformNormalizedAnalyticInverse
import NLS.ComplexAnalysis.BanachTriangularInverseBound

/-! A common analytic Banach implicit-function ball from a common
outer-domain norm bound and an ACTUAL bound for the partial inverse.
Both radii are selected before the equation, base data and inverse. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]

theorem exists_uniform_analytic_implicit_ball (R L M : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧ ρ < R ∧
      ∀ F : E × P → E, ∀ a : E, ∀ p : P,
        AnalyticOnNhd ℂ F (ball (a,p) R) →
        (∀ t ∈ ball (a,p) R, ‖F t‖ ≤ L) → F (a,p) = 0 →
        ∀ e : E ≃L[ℂ] E, e.toContinuousLinearMap =
          (fderiv ℂ F (a,p)).comp (ContinuousLinearMap.inl ℂ E P) →
          ‖e.symm.toContinuousLinearMap‖ ≤ M →
          ∃ s : P → E, AnalyticOnNhd ℂ s (ball p ε) ∧ s p = a ∧
            ∀ y ∈ ball p ε, (s y,y) ∈ ball (a,p) ρ ∧ F (s y,y) = 0 ∧
              ∀ u : E, (u,y) ∈ ball (a,p) ρ → F (u,y) = 0 → u = s y := by
  let C : ℝ := 4*L/R
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let B : ℝ := M*(1+C)+1
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨ρ,δ,hρ,hδ,hρR,hinv⟩ := exists_uniform_normalized_analytic_inverse_radii
    (E := E × P) (R/4) (B*(L+R)) (by positivity) (by positivity)
  let ε : ℝ := δ/(B+1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεδ : B*ε < δ := by
    have he : ε*(B+1) = δ := by dsimp only [ε]; field_simp
    nlinarith
  refine ⟨ρ,ε,hρ,hε,by linarith,?_⟩
  intro F a p hF hb hzero e he heM
  let A := fderiv ℂ F (a,p)
  let T := A.prod (ContinuousLinearMap.snd ℂ E P)
  let Q := banachTriangularInverseCLM A e
  have hA : ‖A‖ ≤ C := by
    have hd := norm_fderiv_le_of_ball_bound F (a,p) (a,p) (R/2) (R/2) L (half_pos hR)
      (by simpa only [add_halves] using hF.differentiableOn)
      (by simpa only [add_halves] using hb) (mem_ball_self (half_pos hR))
    apply hd.trans_eq
    dsimp only [C]
    field_simp
    ring
  have hQ : ‖Q‖ ≤ B := norm_banachTriangularInverseCLM_le A e M C hM hC heM hA
  have hTQ : T.comp Q = ContinuousLinearMap.id ℂ (E × P) := banachTriangular_derivative_comp_inverse A e he
  have hQT : Q.comp T = ContinuousLinearMap.id ℂ (E × P) := banachTriangular_inverse_comp_derivative A e he
  have hTQval (v : E × P) : T (Q v) = v := congrArg (fun J : (E × P) →L[ℂ] (E × P) => J v) hTQ
  let H : E × P → E × P := fun t => (F ((a,p)+t),t.2)
  let N : E × P → E × P := fun t => Q (H t)
  have hshift (t : E × P) (ht : t ∈ ball 0 R) : (a,p)+t ∈ ball (a,p) R := by
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using ht
  have hNa : AnalyticOnNhd ℂ N (ball 0 R) := by
    intro t ht
    exact (Q.analyticAt (H t)).comp
      (((hF _ (hshift t ht)).comp (f := fun s : E × P => (a,p)+s) (analyticAt_const.add analyticAt_id)).prod analyticAt_snd)
  have hNb (t : E × P) (ht : t ∈ ball 0 R) : ‖N t‖ ≤ B*(L+R) := by
    have htN : ‖t‖ < R := mem_ball_zero_iff.mp ht
    have hH : ‖H t‖ ≤ L+R := by
      change max ‖F ((a,p)+t)‖ ‖t.2‖ ≤ L+R
      exact max_le ((hb _ (hshift t ht)).trans (le_add_of_nonneg_right hR.le))
        ((norm_snd_le t).trans (htN.le.trans (le_add_of_nonneg_left hL)))
    exact (Q.le_of_opNorm_le hQ (H t)).trans (mul_le_mul_of_nonneg_left hH hB.le)
  have hNzero : N 0 = 0 := by
    change Q (F ((a,p)+(0:E × P)),(0:E × P).2) = 0
    rw [add_zero,hzero]
    exact Q.map_zero
  have hNder : fderiv ℂ N 0 = ContinuousLinearMap.id ℂ (E × P) := by
    have hFbase : HasFDerivAt F A ((a,p)+(0:E × P)) := by
      simpa only [add_zero] using (hF (a,p) (mem_ball_self hR)).differentiableAt.hasFDerivAt
    have hs : HasFDerivAt (fun t : E × P => (a,p)+t) (ContinuousLinearMap.id ℂ (E × P)) 0 :=
      (hasFDerivAt_id (0:E × P)).const_add (a,p)
    have hFt : HasFDerivAt (fun t : E × P => F ((a,p)+t)) A 0 := by
      simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hFbase.comp 0 hs
    have hHt : HasFDerivAt H T 0 := hFt.prodMk hasFDerivAt_snd
    have hNt := Q.hasFDerivAt.comp 0 hHt
    simpa only [N,Function.comp_def,hQT] using hNt.fderiv
  have hfour : 4*(R/4) = R := by ring
  obtain ⟨g,hg,hg0,hginv⟩ := hinv N (by rw [hfour]; exact hNa) (by rw [hfour]; exact hNb) hNzero hNder
  let target : P → E × P := fun y => Q (0,y-p)
  have htarget (y : P) (hy : y ∈ ball p ε) : target y ∈ ball 0 δ := by
    have hyN : ‖y-p‖ < ε := by simpa only [mem_ball,dist_eq_norm] using hy
    have ht : ‖target y‖ ≤ B*‖y-p‖ := by
      simpa only [target,Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg _)] using Q.le_of_opNorm_le hQ (0,y-p)
    rw [mem_ball_zero_iff]
    exact ht.trans_lt ((mul_lt_mul_of_pos_left hyN hB).trans hεδ)
  have hta (y : P) : AnalyticAt ℂ target y :=
    (Q.analyticAt (0,y-p)).comp (f := fun z : P => (0,z-p))
      (analyticAt_const.prod (analyticAt_id.sub analyticAt_const))
  let w : P → E × P := fun y => g (target y)
  let s : P → E := fun y => a+(w y).1
  have hs : AnalyticOnNhd ℂ s (ball p ε) := by
    intro y hy
    exact analyticAt_const.add (analyticAt_fst.comp ((hg _ (htarget y hy)).comp (hta y)))
  have hw0 : w p = 0 := by
    change g (Q (0,p-p)) = 0
    rw [sub_self]
    change g (Q 0) = 0
    rw [map_zero,hg0]
  refine ⟨s,hs,by change a+(w p).1 = a; rw [hw0]; simp,?_⟩
  intro y hy
  have hgt := hginv (target y) (htarget y hy)
  have hHw : H (w y) = (0,y-p) := by
    have hh := congrArg T hgt.2.1
    change T (Q (H (w y))) = T (Q (0,y-p)) at hh
    rwa [hTQval,hTQval] at hh
  have hpar : (w y).2 = y-p := congrArg Prod.snd hHw
  have hpair : (a,p)+w y = (s y,y) := by
    apply Prod.ext
    · rfl
    · change p+(w y).2 = y
      rw [hpar]
      abel
  have hgraph : (s y,y) ∈ ball (a,p) ρ := by
    rw [← hpair]
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hgt.1
  have hroot : F (s y,y) = 0 := by
    have hh := congrArg Prod.fst hHw
    change F ((a,p)+w y) = 0 at hh
    rwa [hpair] at hh
  refine ⟨hgraph,hroot,?_⟩
  intro u hu hFu
  let v : E × P := (u,y)-(a,p)
  have hv : v ∈ ball 0 ρ := by simpa only [v,mem_ball,dist_eq_norm,sub_zero] using hu
  have hvshift : (a,p)+v = (u,y) := by dsimp only [v]; abel
  have hNv : N v = target y := by
    change Q (F ((a,p)+v),v.2) = Q (0,y-p)
    rw [hvshift,hFu]
    rfl
  have hvg : v = w y := hgt.2.2 v hv hNv
  have hh := congrArg Prod.fst hvg
  change u-a = (w y).1 at hh
  change u = a+(w y).1
  rw [← hh]
  abel

end NLS.ComplexAnalysis
