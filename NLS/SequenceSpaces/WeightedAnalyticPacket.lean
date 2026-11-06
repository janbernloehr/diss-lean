import NLS.SequenceSpaces.HolderEmbedding
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Bounded analytic symbols preserve actual weighted sequence packets

An exact weighted coefficient realization is multiplied by a native
ell-infinity symbol. The resulting analytic Hilbert map retains the
literal product coefficients on an explicit open pullback domain.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

/-- A bounded analytic native symbol preserves an exact weighted packet,
with one norm bound and open neighborhood before all signed indices. -/
theorem exists_analytic_weighted_symbol_packet
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (L : E →L[ℂ] P) (U : Set P) (hU : IsOpen U)
    (σ : P → Coeff ⊤) (hσ : AnalyticOnNhd ℂ σ U)
    (K : ℝ) (hK : 0≤K) (hσbound : ∀ p∈U, ‖σ p‖≤K)
    (V : Set E) (hV : IsOpen V) (q : E) (hqV : q∈V) (hqU : L q∈U)
    (F : E → Coeff 2) (hF : AnalyticOnNhd ℂ F V)
    (M : ℝ) (hM : 0≤M) (hFbound : ∀ p∈V, ‖F p‖≤M)
    (R : P → Coeff 2) (w : ℤ → ℂ)
    (he : ∀ p∈V, ∀ n : ℤ, F p n=w n*R (L p) n) :
    ∃ W : Set E, IsOpen W ∧ q∈W ∧ W⊆V ∧
      ∃ C : ℝ, ∃ G : E → Coeff 2, 0≤C ∧ AnalyticOnNhd ℂ G W ∧
        ∀ p∈W, L p∈U ∧ ‖G p‖≤C ∧ ∀ n : ℤ,
          G p n=w n*(holderProduct (q := 2) (σ (L p)) (R (L p))) n := by
  let W := V∩L ⁻¹' U
  let G := fun p => holderProduct (q := 2) (σ (L p)) (F p)
  refine ⟨W,hV.inter (hU.preimage L.continuous),⟨hqV,hqU⟩,inter_subset_left,
    K*M,G,mul_nonneg hK hM,?_,?_⟩
  · intro p hp
    exact ((holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
      ((hσ (L p) hp.2).comp (L.analyticAt p)) (hF p hp.1)
  · intro p hp
    refine ⟨hp.2,?_,?_⟩
    · exact (norm_holderProduct_le _ _).trans
        (mul_le_mul (hσbound (L p) hp.2) (hFbound p hp.1) (norm_nonneg _) hK)
    · intro n
      change σ (L p) n*F p n=w n*(σ (L p) n*R (L p) n)
      rw [he p hp.1 n]
      ring

end NLS.Coeff
