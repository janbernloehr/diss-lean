import NLS.ZakharovShabat.ParitySpectralFamilies

/-!
# Uniform removal of the odd boundary factor

On compact spectral sets and bounded displacement families, the extra pair
at `2M+1` tends uniformly to one. Its inverse does too, and it is eventually
nonzero everywhere in the family. This permits intrinsic odd approximants.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS

/-- Uniform convergence to one permits inversion and gives simultaneous eventual nonvanishing. -/
theorem ComplexAnalysis.uniform_inverse_of_tendsto_one {X : Type*} (F : ℕ → X → ℂ) (S : Set X)
    (h : TendstoUniformlyOn F (fun _ => 1) atTop S) :
    TendstoUniformlyOn (fun N x => (F N x)⁻¹) (fun _ => 1) atTop S ∧
      ∀ᶠ N : ℕ in atTop, ∀ x ∈ S, F N x ≠ 0 := by
  constructor
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hc : ContinuousAt (fun z : ℂ => z⁻¹) 1 := continuousAt_inv₀ one_ne_zero
    obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp hc ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp h δ hδ] with N hN x hx
    have he := hb (by simpa only [dist_comm] using hN x hx)
    simpa only [inv_one, dist_comm] using he
  · filter_upwards [Metric.tendstoUniformlyOn_iff.mp h 1 (by norm_num)] with N hN x hx
    intro hz
    have he := hN x hx
    rw [hz] at he
    norm_num at he

namespace ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The odd boundary factor tends to one uniformly over every bounded displacement family and spectral compact set. -/
theorem tendstoUniformlyOn_oddBoundary_family {X : Type*}
    (ξ η : X → ℤ → ℂ) (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (hη : ∀ x, Memℓp (fun n => η x n-(Real.pi : ℂ)*n) p)
    (R : ℝ) (hbξ : ∀ x, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x, ‖(⟨_,hη x⟩ : Coeff p)‖ ≤ R) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × X) =>
      spectralPairFactor (ξ t.2) (η t.2) t.1 (2*(M : ℤ)+1)) (fun _ => 1) atTop (K ×ˢ Set.univ) := by
  obtain ⟨A,hA,hAb⟩ := hK.isBounded.exists_pos_norm_le
  let n (M : ℕ) : ℤ := 2*(M : ℤ)+1
  have hiNat : Tendsto (fun M : ℕ => ((Real.pi : ℂ)*M)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_inv_rev, zero_mul] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).mul_const (Real.pi : ℂ)⁻¹
  have ht : Tendsto (fun M : ℕ => 2*M+1) atTop atTop :=
    tendsto_atTop_mono (fun M => by dsimp; omega) tendsto_id
  have hi : Tendsto (fun M => ((Real.pi : ℂ)*n M)⁻¹) atTop (𝓝 0) := by
    simpa only [n, Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, Int.cast_natCast] using hiNat.comp ht
  have hD : Tendsto (fun M => (R+A)*‖((Real.pi : ℂ)*n M)⁻¹‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hi.norm.const_mul (R+A)
  let G (α : X → ℤ → ℂ) (M : ℕ) (t : ℂ × X) :=
    1+(α t.2 (n M)-(Real.pi : ℂ)*n M-t.1)*((Real.pi : ℂ)*n M)⁻¹
  have hsingle (α : X → ℤ → ℂ) (hα : ∀ x, Memℓp (fun n => α x n-(Real.pi : ℂ)*n) p)
      (hbα : ∀ x, ‖(⟨_,hα x⟩ : Coeff p)‖ ≤ R) :
      TendstoUniformlyOn (G α) (fun _ => 1) atTop (K ×ˢ Set.univ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hD.eventually_lt_const hε] with M hM t ht
    have hn := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (⟨_,hα t.2⟩ : Coeff p) (n M)).trans (hbα t.2)
    have he : ‖α t.2 (n M)-(Real.pi : ℂ)*n M-t.1‖ ≤ R+A :=
      (norm_sub_le _ _).trans (add_le_add hn (hAb t.1 ht.1))
    have hb : dist (1 : ℂ) (G α M t) ≤ (R+A)*‖((Real.pi : ℂ)*n M)⁻¹‖ := by
      rw [dist_eq_norm]
      change ‖1-(1+_)‖ ≤ _
      rw [show (1 : ℂ)-(1+(α t.2 (n M)-(Real.pi : ℂ)*n M-t.1)*((Real.pi : ℂ)*n M)⁻¹) =
        -((α t.2 (n M)-(Real.pi : ℂ)*n M-t.1)*((Real.pi : ℂ)*n M)⁻¹) by ring,
        norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_right he (norm_nonneg _)
    exact hb.trans_lt hM
  have hh := ComplexAnalysis.tendstoUniformlyOn_mul_bounded _ _ _ _ (K ×ˢ Set.univ) 1 1
    (by norm_num) (by norm_num) (hsingle ξ hξ hbξ) (hsingle η hη hbη)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
  simp only [mul_one] at hh
  apply hh.congr
  exact Filter.Eventually.of_forall (fun M t _ => by
    have hn : n M ≠ 0 := by dsimp [n]; omega
    have hnC : ((n M : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hpC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    change G ξ M t * G η M t = spectralPairFactor (ξ t.2) (η t.2) t.1 (n M)
    dsimp only [G]
    rw [spectralPairFactor, if_neg hn]
    field_simp
    ring)

end ZakharovShabat
end NLS
