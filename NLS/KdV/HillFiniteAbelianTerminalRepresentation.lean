import NLS.KdV.HillFiniteAbelianPhase

/-! # The actual finite phase as the exponential of full terminal integrals

The own bare Dirichlet phase cancels the regularization's linear term.
This identity uses any compatible real sheeted terminal lifts and retains
the original minus sign and the primitive's base point pi.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillFiniteAbelianPhase_eq_exp_terminal_primitives
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ)
    (hnF : n-1 ∈ F) (θ : ℕ → ℝ)
    (hgap : ∀ k ∈ F,hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) ≠ 0)
    (hpoint : ∀ k ∈ F,cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 (k+1))
      (hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1)) (θ k : ℂ) =
        (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega) : ℂ))
    (hsin : ∀ k ∈ F,sin (θ k : ℂ) = hillDirichletGapSine q.val q.property.1 q.property.2 (k+1) (by omega)) :
    hillFiniteAbelianPhase q n hn F =
      exp (I*∑ k ∈ F,hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n hn (k+1) (θ k : ℂ)) := by
  have hn1 : n-1+1 = n := by omega
  have hgn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0 := by
    simpa only [hn1] using hgap (n-1) hnF
  have hcn : cos (θ (n-1) : ℂ) = hillDirichletGapCosine q.val q.property.1 q.property.2 n hn := by
    apply (eq_div_iff (ofReal_ne_zero.mpr hgn)).mpr
    have hp : cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 n)
        (hillRealGapHalfLength q.val q.property.1 q.property.2 n) (θ (n-1) : ℂ) =
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) := by
      simpa only [hn1] using hpoint (n-1) hnF
    dsimp only [cosineGapPoint,hillDirichletGapCosine] at hp ⊢
    linear_combination hp
  have hsn : sin (θ (n-1) : ℂ) = hillDirichletGapSine q.val q.property.1 q.property.2 n hn := by
    simpa only [hn1] using hsin (n-1) hnF
  have hterms : hillFiniteRegularAbelianSum q n hn F =
      (∑ k ∈ F,hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n hn (k+1) (θ k : ℂ))-
        ((θ (n-1) : ℂ)-(Real.pi : ℂ)) := by
    unfold hillFiniteRegularAbelianSum
    have he : (∑ k ∈ F,hillDirichletRegularAbelianTerm q n hn (k+1) (by omega)) =
        ∑ k ∈ F,hillRegularAbelianPrimitive q.val q.property.1 q.property.2 n hn (k+1) (θ k : ℂ) :=
      Finset.sum_congr rfl (fun k hk => hillDirichletRegularAbelianTerm_eq_terminal q n hn (k+1)
        (by omega) (hgap k hk) (θ k) (hpoint k hk) (hsin k hk))
    rw [he]
    unfold hillRegularAbelianPrimitive
    rw [Finset.sum_sub_distrib]
    congr 1
    have htest (k : ℕ) : k+1 = n ↔ k = n-1 := by omega
    simp only [htest,ite_mul,one_mul,zero_mul]
    simp [hnF]
  rw [hillFiniteAbelianPhase,hillDirichletUnitPhase_eq_terminal q n hn _ hcn hsn,hterms,
    neg_mul,← exp_add]
  rw [show (θ (n-1) : ℂ)*I+I*((∑ k ∈ F,
      hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n hn (k+1) (θ k : ℂ))-
        ((θ (n-1) : ℂ)-(Real.pi : ℂ))) =
      I*(∑ k ∈ F,hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n hn (k+1) (θ k : ℂ))+
        (Real.pi : ℂ)*I by ring,exp_add,exp_pi_mul_I]
  ring

end NLS.KdV
