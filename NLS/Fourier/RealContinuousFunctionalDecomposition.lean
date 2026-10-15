import NLS.Fourier.PeriodicDistributionPhysicalOrderZero
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Algebra.Order.Module.PositiveLinearMap
/-! # Positive decomposition of real continuous functionals

A bounded real functional on continuous functions over a nonempty compact space
is the difference of two positive real functionals. A Hahn–Banach extension
on the doubled space gives the decomposition without assuming a Riesz theorem
for signed or complex functionals.
-/
noncomputable section
namespace NLS.Fourier
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem continuousFunctional_nonneg_of_norm_le_one (F : C(X,ℝ) →L[ℝ] ℝ)
    (hF : ‖F‖ ≤ F 1) (f : C(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ F f := by
  have hn : ‖‖f‖ • (1 : C(X,ℝ)) - f‖ ≤ ‖f‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    simp only [ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.one_apply,
      smul_eq_mul,mul_one,Real.norm_eq_abs,abs_le]
    have hp : 0 ≤ f x := hf x
    have hb : f x ≤ ‖f‖ := (le_abs_self _).trans (f.norm_coe_le_norm x)
    constructor <;> linarith [norm_nonneg f]
  have hb : F (‖f‖ • (1 : C(X,ℝ)) - f) ≤ F 1 * ‖f‖ := by
    calc
      _ ≤ ‖F (‖f‖ • (1 : C(X,ℝ)) - f)‖ := le_abs_self _
      _ ≤ ‖F‖ * ‖‖f‖ • (1 : C(X,ℝ)) - f‖ := F.le_opNorm _
      _ ≤ F 1 * ‖f‖ := mul_le_mul hF hn (norm_nonneg _) ((norm_nonneg F).trans hF)
  simp only [map_sub,map_smul,smul_eq_mul] at hb
  nlinarith


variable [Nonempty X]

def doubledTestLM : C(X,ℝ) × ℝ →ₗ[ℝ] C(X ⊕ X,ℝ) where
  toFun fc := ⟨Sum.elim (fun x => fc.1 x + fc.2) (fun x => -fc.1 x + fc.2),by fun_prop⟩
  map_add' a b := by ext x; cases x <;> dsimp <;> ring
  map_smul' c a := by ext x; cases x <;> dsimp <;> ring

omit [CompactSpace X] in
theorem doubledTestLM_injective : Function.Injective (doubledTestLM (X := X)) := by
  intro a b h
  have hp := congrArg (fun g : C(X ⊕ X,ℝ) => g (Sum.inl (Classical.arbitrary X))) h
  have hm := congrArg (fun g : C(X ⊕ X,ℝ) => g (Sum.inr (Classical.arbitrary X))) h
  change a.1 _ + a.2 = b.1 _ + b.2 at hp
  change -a.1 _ + a.2 = -b.1 _ + b.2 at hm
  have hc : a.2 = b.2 := by linarith
  apply Prod.ext _ hc
  ext x
  have hx := congrArg (fun g : C(X ⊕ X,ℝ) => g (Sum.inl x)) h
  change a.1 x + a.2 = b.1 x + b.2 at hx
  linarith

theorem norm_doubledTestLM_lower (f : C(X,ℝ)) (c : ℝ) :
    ‖f‖ + |c| ≤ ‖doubledTestLM (f,c)‖ := by
  let K := ‖doubledTestLM (f,c)‖
  have hp (x : X) : |f x| + |c| ≤ K := by
    have h1 := (doubledTestLM (f,c)).norm_coe_le_norm (Sum.inl x)
    have h2 := (doubledTestLM (f,c)).norm_coe_le_norm (Sum.inr x)
    change |f x + c| ≤ K at h1
    change |-f x + c| ≤ K at h2
    obtain ⟨h1a,h1b⟩ := abs_le.mp h1
    obtain ⟨h2a,h2b⟩ := abs_le.mp h2
    rcases le_total 0 (f x) with hx | hx <;> rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hx,abs_of_nonneg hc]; linarith
    · rw [abs_of_nonneg hx,abs_of_nonpos hc]; linarith
    · rw [abs_of_nonpos hx,abs_of_nonneg hc]; linarith
    · rw [abs_of_nonpos hx,abs_of_nonpos hc]; linarith
  have hK : 0 ≤ K - |c| := by
    have h := hp (Classical.arbitrary X)
    linarith [abs_nonneg (f (Classical.arbitrary X))]
  have hf : ‖f‖ ≤ K - |c| := by
    apply (ContinuousMap.norm_le _ hK).mpr
    intro x
    change |f x| ≤ K - |c|
    linarith [hp x]
  linarith

theorem exists_positive_decomposition (ell : C(X,ℝ) →L[ℝ] ℝ) :
    ∃ g h : C(X,ℝ) →ₚ[ℝ] ℝ, ∀ f, ell f = g f - h f := by
  let e := LinearEquiv.ofInjective (doubledTestLM (X := X)) doubledTestLM_injective
  let v : C(X,ℝ) × ℝ →ₗ[ℝ] ℝ := {
    toFun := fun a => ell a.1 + ‖ell‖ * a.2
    map_add' := by intro a b; simp only [Prod.fst_add,Prod.snd_add,map_add]; ring
    map_smul' := by intro c a; simp only [Prod.smul_fst,Prod.smul_snd,map_smul,smul_eq_mul,RingHom.id_apply]; ring }
  let b := v.comp e.symm.toLinearMap
  have hb (y : LinearMap.range (doubledTestLM (X := X))) : ‖b y‖ ≤ ‖ell‖ * ‖y‖ := by
    let a := e.symm y
    have hJ : doubledTestLM a = y.val := LinearEquiv.ofInjective_symm_apply doubledTestLM y
    calc
      ‖b y‖ = |ell a.1 + ‖ell‖ * a.2| := rfl
      _ ≤ |ell a.1| + |‖ell‖ * a.2| := abs_add_le _ _
      _ ≤ ‖ell‖ * ‖a.1‖ + ‖ell‖ * |a.2| := by
        rw [abs_mul,abs_of_nonneg (norm_nonneg ell)]
        exact add_le_add (ell.le_opNorm _) le_rfl
      _ = ‖ell‖ * (‖a.1‖ + |a.2|) := by ring
      _ ≤ ‖ell‖ * ‖y‖ := by
        have hj := norm_doubledTestLM_lower a.1 a.2
        change ‖a.1‖ + |a.2| ≤ ‖doubledTestLM a‖ at hj
        rw [hJ] at hj
        exact mul_le_mul_of_nonneg_left hj (norm_nonneg ell)
  let B := b.mkContinuous ‖ell‖ hb
  obtain ⟨F,hF,hnorm⟩ := exists_extension_norm_eq (LinearMap.range (doubledTestLM (X := X))) B
  have hext (a : C(X,ℝ) × ℝ) : F (doubledTestLM a) = v a := by
    have h := hF (e a)
    change F (doubledTestLM a) = v (e.symm (e a)) at h
    simpa only [e.symm_apply_apply] using h
  have hn : ‖F‖ ≤ ‖ell‖ := by
    rw [hnorm]
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg ell) _
  have hunit : F 1 = ‖ell‖ := by
    have h := hext (0,1)
    have he : doubledTestLM (0,1) = (1 : C(X ⊕ X,ℝ)) := by ext x; cases x <;> simp [doubledTestLM]
    rw [he] at h
    simpa [v] using h
  have hpos := continuousFunctional_nonneg_of_norm_le_one F (hn.trans_eq hunit.symm)
  let left : C(X,ℝ) →ₗ[ℝ] C(X ⊕ X,ℝ) := {
    toFun := fun f => ⟨Sum.elim f (fun _ => 0),by fun_prop⟩
    map_add' := by intro f g; ext x; cases x <;> simp
    map_smul' := by intro c f; ext x; cases x <;> simp }
  let right : C(X,ℝ) →ₗ[ℝ] C(X ⊕ X,ℝ) := {
    toFun := fun f => ⟨Sum.elim (fun _ => 0) f,by fun_prop⟩
    map_add' := by intro f g; ext x; cases x <;> simp
    map_smul' := by intro c f; ext x; cases x <;> simp }
  let g : C(X,ℝ) →ₚ[ℝ] ℝ := {
    toLinearMap := F.toLinearMap.comp left
    monotone' := by
      intro f g hfg
      change F (left f) ≤ F (left g)
      apply sub_nonneg.mp
      rw [← map_sub]
      apply hpos
      intro x
      cases x with
      | inl x => exact sub_nonneg.mpr (hfg x)
      | inr x => simp [left] }
  let h : C(X,ℝ) →ₚ[ℝ] ℝ := {
    toLinearMap := F.toLinearMap.comp right
    monotone' := by
      intro f g hfg
      change F (right f) ≤ F (right g)
      apply sub_nonneg.mp
      rw [← map_sub]
      apply hpos
      intro x
      cases x with
      | inl x => simp [right]
      | inr x => exact sub_nonneg.mpr (hfg x) }
  refine ⟨g,h,fun f => ?_⟩
  have he : doubledTestLM (f,0) = left f - right f := by ext x; cases x <;> simp [doubledTestLM,left,right]
  have hf := hext (f,0)
  rw [he,map_sub] at hf
  change ell f = F (left f) - F (right f)
  simpa [v] using hf.symm

end NLS.Fourier
