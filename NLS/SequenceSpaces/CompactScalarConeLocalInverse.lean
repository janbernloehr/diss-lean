import NLS.SequenceSpaces.NonnegativeRealLocalInverse
import NLS.ComplexAnalysis.LinearCoordinatesLocalInverse

/-! Generic REAL analytic local inverses of an actual cone map whose
derivative is a compact perturbation of a nonzero scalar identity.
Compactness is required only at the ORIGINAL nonnegative parameters. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem isUnit_scalar_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℂ) (hc : c≠0) : IsUnit (c • ContinuousLinearMap.id ℂ E) := by
  let u : Units (E →L[ℂ] E) := {
    val := c • ContinuousLinearMap.id ℂ E
    inv := c⁻¹ • ContinuousLinearMap.id ℂ E
    val_inv := by
      apply ContinuousLinearMap.ext
      intro v
      change c • (c⁻¹ • v)=v
      rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
    inv_val := by
      apply ContinuousLinearMap.ext
      intro v
      change c⁻¹ • (c • v)=v
      rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
  }
  exact ⟨u,rfl⟩

theorem exists_open_dense_real_inverse_of_compact_scalar_derivative
    (U : Set (Coeff 1)) (F : Coeff 1 → Coeff 1)
    (_hU : IsOpen U) (hCU : nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (hreal : ∀ x∈nonnegativeLocus 1, F x∈realLocus 1)
    (c : ℂ) (hc : c≠0)
    (hcompact : ∀ x∈nonnegativeLocus 1,
      IsCompactOperator (fderiv ℂ F x-c • ContinuousLinearMap.id ℂ (Coeff 1)))
    (hzero : fderiv ℂ F 0=c • ContinuousLinearMap.id ℂ (Coeff 1)) :
    ∃ O : Set (nonnegativeLocus 1), IsOpen O ∧ Dense O ∧
      (⟨0,zero_mem_nonnegativeLocus 1⟩ : nonnegativeLocus 1)∈O ∧
      ∀ x∈O, IsUnit (fderiv ℂ F x.val) ∧
        AnalyticAt ℝ (realRestriction F) (reCLM 1 x.val) ∧
        NLS.ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ) (realRestriction F) (reCLM 1 x.val) := by
  let A := fun x : nonnegativeLocus 1 => fderiv ℂ F x.val
  have hA : HasLocalAnalyticExtensions A univ := by
    intro x _hx
    exact ⟨fderiv ℂ F,hF.fderiv _ (hCU x.property),Filter.Eventually.of_forall (fun _ => rfl)⟩
  have : PreconnectedSpace (nonnegativeLocus 1) :=
    Subtype.preconnectedSpace (convex_nonnegativeLocus 1).isPreconnected
  have hstart : IsUnit (A ⟨0,zero_mem_nonnegativeLocus 1⟩) := by
    change IsUnit (fderiv ℂ F 0)
    rw [hzero]
    exact isUnit_scalar_identity c hc
  obtain ⟨hopen,hdense⟩ := open_dense_isUnit_of_nonnegative_analytic_compact_shift (p := 1) (by norm_num)
    isOpen_univ isPreconnected_univ hA hc (fun x _hx => hcompact x.val x.property)
    ⟨⟨0,zero_mem_nonnegativeLocus 1⟩,mem_univ _,hstart⟩
  let O := {x : nonnegativeLocus 1 | x∈(univ : Set (nonnegativeLocus 1)) ∧ IsUnit (A x)}
  let a : NonnegativeAnalyticAtlas (fun x : nonnegativeLocus 1 => F x.val) univ := {
    extension := fun _x => F
    analyticAt := fun x _hx => hF x.val (hCU x.property)
    agreement := fun _x _hx => Filter.Eventually.of_forall (fun _y => rfl)
  }
  refine ⟨O,hopen,(fun x => hdense (mem_univ x)),⟨mem_univ _,hstart⟩,?_⟩
  intro x hx
  have hu : IsUnit (a.derivative x) := hx.2
  obtain ⟨G,hFa,hG,hGx,hl,hr,_hcone⟩ := exists_realRestriction_localInverse_of_nonnegative_atlas (by norm_num)
    a isOpen_univ (fun y _hy => hreal y.val y.property) (mem_univ x) hu
  have hcenter : realRestriction F (reCLM 1 x.val)=reCLM 1 (F x.val) := by
    change reCLM 1 (F (RealCoeff.complexCLM 1 (reCLM 1 x.val)))=reCLM 1 (F x.val)
    rw [RealCoeff.complexCLM_reCLM 1 x.val (fun n => (x.property n).1)]
  refine ⟨hx.2,hFa,?_⟩
  change ∃ G : RealCoeff 1 → RealCoeff 1, AnalyticAt ℝ G (realRestriction F (reCLM 1 x.val)) ∧
    G (realRestriction F (reCLM 1 x.val))=reCLM 1 x.val ∧
    (∀ᶠ y in 𝓝 (reCLM 1 x.val), G (realRestriction F y)=y) ∧
    ∀ᶠ z in 𝓝 (realRestriction F (reCLM 1 x.val)), realRestriction F (G z)=z
  rw [hcenter]
  exact ⟨G,hG,hGx,hl,hr⟩

end NLS.Coeff
