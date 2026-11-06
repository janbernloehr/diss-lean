import NLS.SequenceSpaces.SignChange
import NLS.SequenceSpaces.CompactHolderDerivative

/-! # One constant sign selection transports analytic packets exactly

Signs are chosen before every source point and weighted index. Their
bounded complex linear isometry transports both actual values and the
compact derivative remainder, without a new choice at each source.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- A coordinatewise alternative on a common domain gives ONE infinite
sign selection on that WHOLE domain, not signs depending on the source. -/
theorem exists_constant_signChange_of_eqOn_or_neg
    {X : Type*} (U : Set X) (F G : X → Coeff 2)
    (he : ∀ n : ℤ, (∀ q∈U, F q n=G q n) ∨ (∀ q∈U, F q n= -G q n)) :
    ∃ e : ℤ → Bool, ∀ q∈U, F q=signChange e (G q) := by
  classical
  have hchoice (n : ℤ) : ∃ b : Bool, ∀ q∈U, F q n=if b then -G q n else G q n := by
    rcases he n with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose e he using hchoice
  refine ⟨e,?_⟩
  intro q hq
  ext n
  rw [signChange_apply]
  exact he n q hq

/-- The exact derivative of a fixed sign change is the SAME sign change
of the derivative, on every native domain. -/
theorem fderiv_signChange_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : ℤ → Bool) (G : E → Coeff 2) (q : E) (hG : DifferentiableAt ℂ G q) :
    fderiv ℂ (fun p => signChange e (G p)) q=(signChange e).comp (fderiv ℂ G q) :=
  ((signChange e).hasFDerivAt.comp q hG.hasFDerivAt).fderiv

/-- The fixed signs preserve the actual full-symbol compact derivative
formula. The principal operator is transported EXACTLY, including phases. -/
theorem isCompactOperator_fderiv_signChange_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : ℤ → Bool) (G : E → Coeff 2) (q : E) (hG : DifferentiableAt ℂ G q)
    (A : E →L[ℂ] Coeff 2) (hc : IsCompactOperator (fderiv ℂ G q-A)) :
    IsCompactOperator (fderiv ℂ (fun p => signChange e (G p)) q-(signChange e).comp A) := by
  rw [fderiv_signChange_comp e G q hG]
  have he : (signChange e).comp (fderiv ℂ G q)-(signChange e).comp A=
      (signChange e).comp (fderiv ℂ G q-A) := by
    apply ContinuousLinearMap.ext
    intro v
    change signChange e (fderiv ℂ G q v)-signChange e (A v)=signChange e (fderiv ℂ G q v-A v)
    exact ((signChange e).map_sub _ _).symm
  rw [he]
  exact hc.clm_comp (signChange e)

/-- Weighted packet coefficients transport through the SAME fixed signs. -/
theorem signChange_weighted_packet
    {X : Type*} (e : ℤ → Bool) (F G : X → Coeff 2) (w : ℤ → ℂ)
    (q : X) (he : ∀ n : ℤ, F q n=w n*G q n) (n : ℤ) :
    signChange e (F q) n=w n*signChange e (G q) n := by
  rw [signChange_apply,signChange_apply,he n]
  cases e n <;> simp

/-- ONE fixed sign selection transports every weighted native analytic
packet and its exact compact principal derivative to a GIVEN weak map. -/
theorem exists_constant_sign_weighted_packet_germ
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (L : E →L[ℂ] P) (U : Set P) (hU : IsOpen U)
    (e : ℤ → Bool) (Z G : P → Coeff 2)
    (he : ∀ p∈U, Z p=signChange e (G p))
    (V : Set E) (hV : IsOpen V) (q : E) (hqV : q∈V) (hqU : L q∈U)
    (w : ℤ → ℂ) (M : ℝ) (F : E → Coeff 2)
    (hFa : AnalyticOnNhd ℂ F V) (hFb : ∀ p∈V, ‖F p‖≤M)
    (hcoeff : ∀ p∈V, ∀ n : ℤ, F p n=w n*G (L p) n)
    (A : E → E →L[ℂ] Coeff 2)
    (hcompact : ∀ p∈V, IsCompactOperator (fderiv ℂ F p-A p)) :
    ∃ W : Set E, IsOpen W ∧ q∈W ∧ W⊆V ∧
      ∃ H : E → Coeff 2, AnalyticOnNhd ℂ H W ∧ ∀ p∈W,
        L p∈U ∧ ‖H p‖≤M ∧ (∀ n : ℤ, H p n=w n*Z (L p) n) ∧
        IsCompactOperator (fderiv ℂ H p-(signChange e).comp (A p)) := by
  let W := V∩L ⁻¹' U
  let H := fun p => signChange e (F p)
  refine ⟨W,hV.inter (hU.preimage L.continuous),⟨hqV,hqU⟩,inter_subset_left,H,?_,?_⟩
  · intro p hp
    exact ((signChange e).analyticAt _).comp (hFa p hp.1)
  · intro p hp
    refine ⟨hp.2,?_,?_,?_⟩
    · simpa only [H,norm_signChange] using hFb p hp.1
    · intro n
      change signChange e (F p) n=w n*Z (L p) n
      rw [he (L p) hp.2]
      exact signChange_weighted_packet e F (fun p => G (L p)) w p (hcoeff p hp.1) n
    · exact isCompactOperator_fderiv_signChange_sub e F p (hFa p hp.1).differentiableAt
        (A p) (hcompact p hp.1)

end NLS.Coeff
