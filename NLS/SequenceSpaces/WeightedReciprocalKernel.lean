import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.TameSpectralConvolution
import NLS.SequenceSpaces.YoungInequality

/-! Actual reciprocal kernels with fractional Sobolev weights. The
additive weight splitting retains the two distinct Holder rows needed
at every negative action order strictly above the weak endpoint. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

theorem Weight.sobolev_sum_bound (σ : ℝ) (hσ : 0≤σ) (n k : ℤ) :
    Weight.sobolev σ k≤(2 : ℝ)^σ*(Weight.sobolev σ n+Weight.sobolev σ (k-n)) := by
  have h := SpectralWeight.sobolev_add_le σ hσ n (k-n)
  have he : n+(k-n)=k := by omega
  simpa only [SpectralWeight.sobolev_apply,he] using h

theorem Weight.memlp_negative_sobolev {p : ℝ≥0∞} (hp : 0<p.toReal) (d : ℝ)
    (hd : 1<d*p.toReal) : Memℓp (fun n : ℤ => (Weight.sobolev (-d) n : ℂ)) p := by
  have he : (fun n : ℤ => (Weight.sobolev (-d) n : ℂ))=
      (fun n : ℤ => (Weight.sobolev d n : ℂ)⁻¹) := by
    funext n
    simp only [Weight.sobolev_apply,Real.rpow_neg (by positivity : (0 : ℝ)≤1+|(n : ℝ)|),Complex.ofReal_inv]
  rw [he]
  exact Weight.inverse_sobolev_memlp hp hd

namespace Coeff

theorem norm_puncturedLattice_neg (n : ℤ) :
    ‖puncturedLattice 2 (by norm_num) (-n)‖=‖puncturedLattice 2 (by norm_num) n‖ := by
  by_cases hn : n=0
  · simp [hn]
  · simp only [puncturedLattice_apply,neg_ne_zero.mpr hn,hn,if_false,Int.cast_neg,inv_neg,norm_neg]

theorem weighted_puncturedLattice_bound (σ : ℝ) (n : ℤ) :
    Weight.sobolev σ n*‖puncturedLattice 2 (by norm_num) n‖≤2/Weight.sobolev (1-σ) n := by
  apply (le_div_iff₀ ((Weight.sobolev (1-σ)).positive n)).mpr
  have hw : Weight.sobolev σ n*Weight.sobolev (1-σ) n=1+|(n : ℝ)| := by
    rw [←Weight.sobolev_add]
    norm_num [Weight.sobolev_apply]
  rw [mul_right_comm,hw,puncturedLattice_apply]
  by_cases hn : n=0
  · simp [hn]
  · rw [if_neg hn,norm_inv,Complex.norm_intCast]
    have h1 : (1 : ℝ)≤|(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    rw [←div_eq_mul_inv]
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < |(n : ℝ)|)).mpr
    nlinarith

theorem memlp_weighted_puncturedLattice {p : ℝ≥0∞} (hp : 0<p.toReal) (σ : ℝ)
    (hσ : 1<(1-σ)*p.toReal) :
    Memℓp (fun n : ℤ => (Weight.sobolev σ n : ℂ)*puncturedLattice 2 (by norm_num) n) p := by
  apply ((Weight.inverse_sobolev_memlp hp hσ).norm.const_mul (2 : ℝ)).mono
  intro n
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev σ).positive n).le]
  simpa only [norm_inv,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev (1-σ)).positive n).le,
    div_eq_mul_inv] using weighted_puncturedLattice_bound σ n

theorem holder_absolute_row {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p.toReal.HolderConjugate q.toReal) (a : Coeff p) (b : Coeff q) (k : ℤ) :
    Summable (fun n : ℤ => ‖a n‖*‖b (k-n)‖) ∧
      (∑' n : ℤ, ‖a n‖*‖b (k-n)‖)≤‖a‖*‖b‖ := by
  have h := lp.tsum_mul_le_mul_norm hpq a (reindex (Equiv.subLeft k) b)
  simpa only [reindex_apply,norm_reindex,Equiv.subLeft_apply] using h

end Coeff
end NLS
