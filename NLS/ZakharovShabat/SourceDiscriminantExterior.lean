import NLS.ZakharovShabat.LocallyUniformDiscriminantAsymptotics

/-!
# Common source neighborhoods for the discriminant exterior estimates

The full exterior contains cosine zeros. There the trace estimate is
additive, normalized by exp(abs(Im z)); the sine derivative quotient is
valid on the whole exterior. A cosine quotient additionally requires an
explicit lower bound for its denominator.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One original open convex neighborhood and positive threshold serve all three bounds. -/
theorem exists_uniform_sourceDiscriminant_exterior (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 < R ∧ ∀ ψ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
        (∀ n : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*n‖) →
        ‖canonicalDiscriminant hp (periodOnePotential ψ) z-2*cos z‖ ≤ ε*Real.exp |z.im| ∧
        ‖deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z+2*sin z‖ ≤ ε*Real.exp |z.im| ∧
        ‖deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/(-2*sin z)-1‖ ≤ ε := by
  have hr : 0 < Real.pi/4 := by positivity
  obtain ⟨A,hAo,hAc,hAφ,hA0,a,ha⟩ := exists_uniform_discriminant_error_exp hp hp1 (periodOnePotential φ) hr le_rfl hε
  obtain ⟨B,hBo,hBc,hBφ,hB0,b,hb⟩ := exists_uniform_discriminant_derivative_error_exp hp hp1 (periodOnePotential φ) hr le_rfl hε
  obtain ⟨C,hCo,hCc,hCφ,hC0,c,hc⟩ := exists_uniform_discriminant_derivative_div_free hp hp1 (periodOnePotential φ) hr le_rfl hε
  let V := (A ∩ B) ∩ C
  let R := max 1 (max (max a b) c)
  have hRa : a ≤ R := (le_max_left a b).trans ((le_max_left (max a b) c).trans (le_max_right _ _))
  have hRb : b ≤ R := (le_max_right a b).trans ((le_max_left (max a b) c).trans (le_max_right _ _))
  have hRc : c ≤ R := (le_max_right (max a b) c).trans (le_max_right _ _)
  refine ⟨periodOnePotential ⁻¹' V,((hAo.inter hBo).inter hCo).preimage (periodOnePotential (p := p)).continuous,
    ((hAc.inter hBc).inter hCc).linear_preimage ((periodOnePotential (p := p)).restrictScalars ℝ).toLinearMap,
    ⟨⟨hAφ,hBφ⟩,hCφ⟩,?_,R,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  · simpa only [mem_preimage,map_zero] using (show (0 : PairSpace p) ∈ V from ⟨⟨hA0,hB0⟩,hC0⟩)
  · intro ψ hψ z hz hsep
    exact ⟨ha _ hψ.1.1 (periodOnePotential_mem ψ) z (hRa.trans hz) hsep,
      hb _ hψ.1.2 (periodOnePotential_mem ψ) z (hRb.trans hz) hsep,
      hc _ hψ.2 (periodOnePotential_mem ψ) z (hRc.trans hz) hsep⟩

/-- The cosine quotient is uniformly controlled where its denominator has a relative lower bound. -/
theorem exists_uniform_sourceDiscriminant_cosine_quotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 < R ∧ ∀ ψ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
        (∀ n : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*n‖) →
        c*Real.exp |z.im| ≤ ‖2*cos z‖ →
        ‖canonicalDiscriminant hp (periodOnePotential ψ) z/(2*cos z)-1‖ ≤ ε := by
  obtain ⟨U,ho,hconv,hφ,h0,R,hR,h⟩ := exists_uniform_sourceDiscriminant_exterior hp hp1 φ (mul_pos hε hc)
  refine ⟨U,ho,hconv,hφ,h0,R,hR,?_⟩
  intro ψ hψ z hz hsep hcos
  have hn : 0 < ‖2*cos z‖ := (mul_pos hc (Real.exp_pos _)).trans_le hcos
  have he : canonicalDiscriminant hp (periodOnePotential ψ) z/(2*cos z)-1 =
      (canonicalDiscriminant hp (periodOnePotential ψ) z-2*cos z)/(2*cos z) := by
    rw [sub_div,div_self (norm_pos_iff.mp hn)]
  rw [he,norm_div]
  apply (div_le_iff₀ hn).mpr
  have hbound := (h ψ hψ z hz hsep).1
  have hden := mul_le_mul_of_nonneg_left hcos hε.le
  nlinarith

end NLS.ZakharovShabat
