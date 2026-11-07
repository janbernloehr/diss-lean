import NLS.SequenceSpaces.WeightedReciprocalColumnMajorants

/-! The actual negative Sobolev reciprocal column at EVERY order
-1<alpha<0 has decay of every strictly smaller positive order. Two
conjugate exponent pairs prove summability before all column indices. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem reciprocal_holder_pair (θ : ℝ) (hθ : 0<θ) (hθ1 : θ<1) :
    let p := ENNReal.ofReal θ⁻¹
    let q := ENNReal.ofReal (1-θ)⁻¹
    1≤p ∧ 1≤q ∧ 0<p.toReal ∧ 0<q.toReal ∧ p.toReal.HolderConjugate q.toReal := by
  intro p q
  have hd : 0<1-θ := sub_pos.mpr hθ1
  have hp : p.toReal=θ⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.mpr hθ.le)
  have hq : q.toReal=(1-θ)⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.mpr hd.le)
  refine ⟨?_,?_,by rw [hp];positivity,by rw [hq];positivity,?_⟩
  · change 1≤ENNReal.ofReal θ⁻¹
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((one_le_inv₀ hθ).mpr hθ1.le)
  · change 1≤ENNReal.ofReal (1-θ)⁻¹
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((one_le_inv₀ hd).mpr (by linarith))
  · rw [hp,hq]
    exact Real.HolderConjugate.inv_one_sub_inv hθ hθ1

theorem exists_negative_weight_reciprocal_column_bound
    (A σ : ℝ) (hA1 : A<1) (hσ : 0<σ) (hσA : σ<A) :
    ∃ C : ℝ, 0≤C ∧ ∀ k : ℤ,
      Summable (fun n : ℤ => Weight.sobolev (-A) n*‖puncturedLattice 2 (by norm_num) (n-k)‖) ∧
      Weight.sobolev σ k*(∑' n : ℤ, Weight.sobolev (-A) n*‖puncturedLattice 2 (by norm_num) (n-k)‖)≤C := by
  let θ₁ := (A-σ)/2
  let θ₂ := (A+σ)/2
  have hθ₁ : 0<θ₁ := by dsimp only [θ₁];linarith
  have hθ₁1 : θ₁<1 := by dsimp only [θ₁];linarith
  have hθ₂ : 0<θ₂ := by dsimp only [θ₂];linarith
  have hθ₂1 : θ₂<1 := by dsimp only [θ₂];linarith
  let p₁ := ENNReal.ofReal θ₁⁻¹
  let q₁ := ENNReal.ofReal (1-θ₁)⁻¹
  let p₂ := ENNReal.ofReal θ₂⁻¹
  let q₂ := ENNReal.ofReal (1-θ₂)⁻¹
  obtain ⟨hp₁,hq₁,hp₁0,hq₁0,hpq₁⟩ := reciprocal_holder_pair θ₁ hθ₁ hθ₁1
  obtain ⟨hp₂,hq₂,hp₂0,hq₂0,hpq₂⟩ := reciprocal_holder_pair θ₂ hθ₂ hθ₂1
  let : Fact (1≤p₁) := ⟨hp₁⟩
  let : Fact (1≤q₁) := ⟨hq₁⟩
  let : Fact (1≤p₂) := ⟨hp₂⟩
  let : Fact (1≤q₂) := ⟨hq₂⟩
  have hp₁r : p₁.toReal=θ₁⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.mpr hθ₁.le)
  have hp₂r : p₂.toReal=θ₂⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.mpr hθ₂.le)
  have hq₂r : q₂.toReal=(1-θ₂)⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.mpr (sub_nonneg.mpr hθ₂1.le))
  have hd₁ : 1<(A-σ)*p₁.toReal := by
    rw [hp₁r,←div_eq_mul_inv]
    apply (lt_div_iff₀ hθ₁).mpr
    dsimp only [θ₁]
    linarith
  have hd₂ : 1<A*p₂.toReal := by
    rw [hp₂r,←div_eq_mul_inv]
    apply (lt_div_iff₀ hθ₂).mpr
    dsimp only [θ₂]
    linarith
  have hd₃ : 1<(1-σ)*q₂.toReal := by
    rw [hq₂r,←div_eq_mul_inv]
    apply (lt_div_iff₀ (sub_pos.mpr hθ₂1)).mpr
    dsimp only [θ₂]
    linarith
  have hq₁gt : 1<q₁ := by
    apply (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ENNReal.ofReal_ne_top)).mp
    simpa only [ENNReal.toReal_one] using hpq₁.symm.lt
  let a₁ : Coeff p₁ := ⟨fun n => (Weight.sobolev (-(A-σ)) n : ℂ),Weight.memlp_negative_sobolev hp₁0 (A-σ) hd₁⟩
  let b₁ : Coeff q₁ := puncturedLattice q₁ hq₁gt
  let a₂ : Coeff p₂ := ⟨fun n => (Weight.sobolev (-A) n : ℂ),Weight.memlp_negative_sobolev hp₂0 A hd₂⟩
  let b₂ : Coeff q₂ := ⟨fun n => (Weight.sobolev σ n : ℂ)*puncturedLattice 2 (by norm_num) n,
    memlp_weighted_puncturedLattice hq₂0 σ hd₃⟩
  apply weighted_reciprocal_columns_of_holder_rows A σ hσ.le hpq₁ hpq₂ a₁ b₁ a₂ b₂
  · intro n
    change ‖(Weight.sobolev (-(A-σ)) n : ℂ)‖=_
    rw [Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev (-(A-σ))).positive n).le]
    rw [show -(A-σ)=σ+(-A) by ring,Weight.sobolev_add]
  · intro n
    simp only [b₁,puncturedLattice_apply]
  · intro n
    exact Complex.norm_of_nonneg ((Weight.sobolev (-A)).positive n).le
  · intro n
    change ‖(Weight.sobolev σ n : ℂ)*puncturedLattice 2 (by norm_num) n‖=_
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev σ).positive n).le]

end NLS.Coeff
