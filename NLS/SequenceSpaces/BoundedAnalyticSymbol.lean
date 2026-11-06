import NLS.SequenceSpaces.BoundedCoordinateAnalytic
import NLS.SequenceSpaces.FunctionOrZero
import NLS.SequenceSpaces.CompactHolderDerivative

/-! # Exact bounded analytic symbols and compact principal derivatives

A uniformly bounded scalar family realizes an actual native ell-infinity
analytic map. Bounded reciprocal symbols give literal multiplier inverses.
An actual sequence packet with a compact principal derivative retains
that principal after multiplication by its full analytic symbol.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- Native realization of an arbitrary signed scalar symbol family. -/
def boundedSymbolRealization {E : Type*} (f : E → ℤ → ℂ) (x : E) : Coeff ⊤ :=
  ofFunctionOrZero ⊤ (f x)

/-- A common bound before all signed indices proves genuine native
analyticity and excludes the total constructor fallback on the domain. -/
theorem analytic_boundedSymbolRealization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (hU : IsOpen U) (f : E → ℤ → ℂ)
    (C : ℝ) (hC : 0≤C) (ha : ∀ n : ℤ, AnalyticOnNhd ℂ (fun x => f x n) U)
    (hb : ∀ x∈U, ∀ n : ℤ, ‖f x n‖≤C) :
    AnalyticOnNhd ℂ (boundedSymbolRealization f) U ∧
      ∀ x∈U, ‖boundedSymbolRealization f x‖≤C ∧ ∀ n : ℤ, boundedSymbolRealization f x n=f x n := by
  have hm (x : E) (hx : x∈U) : Memℓp (f x) ⊤ :=
    memℓp_infty ⟨C,by rintro _ ⟨n,rfl⟩;exact hb x hx n⟩
  have he (x : E) (hx : x∈U) (n : ℤ) : boundedSymbolRealization f x n=f x n :=
    ofFunctionOrZero_apply_of_mem ⊤ _ (hm x hx) n
  have hn (x : E) (hx : x∈U) : ‖boundedSymbolRealization f x‖≤C := by
    apply lp.norm_le_of_forall_le hC
    intro n
    rw [he x hx n]
    exact hb x hx n
  refine ⟨analyticOnNhd_of_bounded_coordinatewise _ hU (fun n x hx => ?_) C hn,
    fun x hx => ⟨hn x hx,he x hx⟩⟩
  apply (ha n x hx).congr
  filter_upwards [hU.mem_nhds hx] with y hy
  exact (he y hy n).symm

/-- Two ACTUAL bounded reciprocal symbols give an exact multiplier
isomorphism on every Banach coefficient space, including infinity. -/
def multiplierEquivOfInverse {p : ℝ≥0∞} [Fact (1≤p)]
    (m n : Coeff ⊤) (hmn : ∀ j : ℤ, m j*n j=1) : Coeff p ≃L[ℂ] Coeff p where
  toLinearEquiv := {
    toFun := multiplierCLM m
    invFun := multiplierCLM n
    left_inv := by
      intro a
      ext j
      change n j*(m j*a j)=a j
      rw [←mul_assoc,mul_comm (n j),hmn j,one_mul]
    right_inv := by
      intro a
      ext j
      change m j*(n j*a j)=a j
      rw [←mul_assoc,hmn j,one_mul]
    map_add' := (multiplierCLM m).map_add
    map_smul' := (multiplierCLM m).map_smul }
  continuous_toFun := (multiplierCLM m).continuous
  continuous_invFun := (multiplierCLM n).continuous

/-- The ACTUAL full analytic symbol multiplies the given compact
principal derivative. Symbol differentiation remains compact. -/
theorem isCompactOperator_fderiv_symbol_packet_sub_principal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : E → Coeff ⊤) (F : E → Coeff 2) (q : E)
    (hσ : DifferentiableAt ℂ σ q) (hF : DifferentiableAt ℂ F q)
    (Q : E →L[ℂ] Coeff 2) (hQ : IsCompactOperator (fderiv ℂ F q-Q)) :
    IsCompactOperator (fderiv ℂ (fun x => holderProduct (q := 2) (σ x) (F x)) q-
      (holderProduct (q := 2) (σ q)).comp Q) := by
  let M := holderProduct (p := ⊤) (r := 2) (q := 2) (σ q)
  have he : fderiv ℂ (fun x => holderProduct (q := 2) (σ x) (F x)) q-M.comp Q=
      (fderiv ℂ (fun x => holderProduct (q := 2) (σ x) (F x)) q-M.comp (fderiv ℂ F q))+
        M.comp (fderiv ℂ F q-Q) := by
    apply ContinuousLinearMap.ext
    intro h
    change (fderiv ℂ (fun x => holderProduct (q := 2) (σ x) (F x)) q) h-M (Q h)=
      ((fderiv ℂ (fun x => holderProduct (q := 2) (σ x) (F x)) q) h-M (fderiv ℂ F q h))+
        M (fderiv ℂ F q h-Q h)
    rw [map_sub]
    abel
  rw [he]
  exact (isCompactOperator_fderiv_holderProduct_packet_sub (by norm_num) σ F q hσ hF).add
    (hQ.clm_comp M)

end NLS.Coeff
