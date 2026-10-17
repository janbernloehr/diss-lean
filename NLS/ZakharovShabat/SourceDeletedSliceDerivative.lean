import NLS.ZakharovShabat.SourceDeleteResonance
import NLS.ZakharovShabat.SourceBirkhoffDeletedSlice

/-! # Derivative rows from complex deleted-slice zeros

If a pair of output coordinates vanishes when its signed source pair
is deleted, differentiating at a point fixed by deletion leaves exactly
two input modes. Their coefficients are the actual unit-direction
derivatives, including the reflected first source frequency.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A source with zero resonant pair is fixed by deletion. -/
theorem sourceDeleteResonance_eq_self (n : ℤ) (a : CoeffPair p)
    (h : a.fst (-n) = 0 ∧ a.snd n = 0) : sourceDeleteResonance n a = a := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext j
  · change Coeff.deleteCoordinate (-n) a.fst j = a.fst j
    by_cases hj : j = -n
    · subst j; simp [h.1]
    · exact Coeff.deleteCoordinate_apply_other (-n) j hj a.fst
  · change Coeff.deleteCoordinate n a.snd j = a.snd j
    by_cases hj : j = n
    · subst j; simp [h.2]
    · exact Coeff.deleteCoordinate_apply_other n j hj a.snd

/-- Deletion leaves exactly the two raw unit directions and their source amplitudes. -/
theorem sub_sourceDeleteResonance_eq_smul_single (n : ℤ) (a : CoeffPair p) :
    a-sourceDeleteResonance n a =
      a.fst (-n) • CoeffPair.inlCLM (lp.single p (-n) (1:ℂ))+
        a.snd n • CoeffPair.inrCLM (lp.single p n (1:ℂ)) := by
  have he : a-sourceDeleteResonance n a =
      CoeffPair.inlCLM (lp.single p (-n) (a.fst (-n)))+
        CoeffPair.inrCLM (lp.single p n (a.snd n)) := by
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext j <;> simp [sourceDeleteResonance,Coeff.deleteCoordinate] <;> rfl
  rw [he,← map_smul,← map_smul,← lp.single_smul,← lp.single_smul]
  simp only [smul_eq_mul,mul_one]

/-- A linear observation killed by deletion depends only on the two removed modes. -/
theorem linear_observation_of_deleted_kernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : CoeffPair p →L[ℂ] E) (n : ℤ) (hL : L.comp (sourceDeleteResonance n) = 0)
    (a : CoeffPair p) :
    L a = a.fst (-n) • L (CoeffPair.inlCLM (lp.single p (-n) (1:ℂ)))+
      a.snd n • L (CoeffPair.inrCLM (lp.single p n (1:ℂ))) := by
  have hzero : L (sourceDeleteResonance n a) = 0 := congrArg (fun M => M a) hL
  have he := congrArg L (sub_sourceDeleteResonance_eq_smul_single n a)
  simpa only [map_sub,hzero,sub_zero,map_add,map_smul] using he

private theorem fderiv_comp_projection_of_zero_germ
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : E → F) (P : E →L[ℂ] E) (a : E) (hP : P a = a) (hf : AnalyticAt ℂ f a)
    (hz : (fun b => f (P b)) =ᶠ[𝓝 a] fun _ => 0) :
    (fderiv ℂ f a).comp P = 0 := by
  have hfa : HasFDerivAt f (fderiv ℂ f a) (P a) := by
    rw [hP]
    exact hf.differentiableAt.hasFDerivAt
  have h := hfa.comp a P.hasFDerivAt
  exact (h.congr_of_eventuallyEq hz.symm).unique (hasFDerivAt_const (0:F) a)

/-- Differentiating actual deleted-slice zeros gives both exact two-mode derivative rows. -/
theorem fderiv_coordinate_rows_of_deleted_zero
    (F : CoeffPair p → Coeff p × Coeff p) (b : CoeffPair p) (n : ℤ)
    (hF : AnalyticAt ℂ F b) (hb : b.fst (-n) = 0 ∧ b.snd n = 0)
    (hz : ∀ᶠ y in 𝓝 b, (F (sourceDeleteResonance n y)).1 n = 0 ∧
      (F (sourceDeleteResonance n y)).2 n = 0)
    (a : CoeffPair p) :
    (fderiv ℂ F b a).1 n =
      a.fst (-n)*(fderiv ℂ F b (CoeffPair.inlCLM (lp.single p (-n) (1:ℂ)))).1 n+
      a.snd n*(fderiv ℂ F b (CoeffPair.inrCLM (lp.single p n (1:ℂ)))).1 n ∧
    (fderiv ℂ F b a).2 n =
      a.fst (-n)*(fderiv ℂ F b (CoeffPair.inlCLM (lp.single p (-n) (1:ℂ)))).2 n+
      a.snd n*(fderiv ℂ F b (CoeffPair.inrCLM (lp.single p n (1:ℂ)))).2 n := by
  let Q : (Coeff p × Coeff p) →L[ℂ] (ℂ × ℂ) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).prodMap (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n)
  let f := fun y => Q (F y)
  have hf : AnalyticAt ℂ f b := (Q.analyticAt _).comp hF
  have hzero : (fun y => f (sourceDeleteResonance n y)) =ᶠ[𝓝 b] fun _ => 0 := by
    filter_upwards [hz] with y hy
    exact Prod.ext hy.1 hy.2
  have hker := fderiv_comp_projection_of_zero_germ f (sourceDeleteResonance n) b
    (sourceDeleteResonance_eq_self n b hb) hf hzero
  have hd : fderiv ℂ f b = Q.comp (fderiv ℂ F b) :=
    (Q.hasFDerivAt.comp b hF.differentiableAt.hasFDerivAt).fderiv
  rw [hd] at hker
  have hr := linear_observation_of_deleted_kernel (Q.comp (fderiv ℂ F b)) n hker a
  exact ⟨congrArg Prod.fst hr,congrArg Prod.snd hr⟩

end NLS.ZakharovShabat
