import NLS.MKdV.MiuraSquaredEndpointMultiplicity

/-! # Exact fixed-index Miura gap identification on real H¹

The Hill labels are independently constructed from its physical L²
operator. The NLS labels retain their original signed indices.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.KdV
open scoped ComplexConjugate
namespace NLS.MKdV

theorem miuraHillLabels_ground (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    miuraHillLabels a ha 0 = (miuraNLSRight a 0).re^2 := by
  rw [miuraHillLabels_eq_squaredNLS,miuraSquaredNLS,miuraPositiveFrequency_zero]

theorem miuraHillLabels_left (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    miuraHillLabels a ha (2*n-1) = (miuraNLSLeft a n).re^2 := by
  rw [miuraHillLabels_eq_squaredNLS,miuraSquaredNLS,miuraPositiveFrequency_left a n hn]

theorem miuraHillLabels_right (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    miuraHillLabels a ha (2*n) = (miuraNLSRight a n).re^2 := by
  rw [miuraHillLabels_eq_squaredNLS,miuraSquaredNLS,miuraPositiveFrequency_right a n hn]

theorem miuraHillLabels_ground_complex (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    (miuraHillLabels a ha 0 : ℂ) = (miuraNLSRight a 0)^2 ∧
    (miuraHillLabels a ha 0 : ℂ) = (miuraNLSLeft a 0)^2 := by
  have hR : ((miuraNLSRight a 0).re : ℂ) = miuraNLSRight a 0 := by
    apply Complex.ext <;> simp only [ofReal_re,ofReal_im,(miuraNLSEndpoints_real a ha 0).2]
  have h1 : (miuraHillLabels a ha 0 : ℂ) = (miuraNLSRight a 0)^2 := by
    rw [miuraHillLabels_ground,ofReal_pow,hR]
  refine ⟨h1,?_⟩
  rw [(miuraNLSEndpoints_reflection a 0).1,neg_zero,neg_sq]
  exact h1

theorem miuraHillLabels_endpoints_complex (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    (miuraHillLabels a ha (2*n-1) : ℂ) = (miuraNLSLeft a n)^2 ∧
    (miuraHillLabels a ha (2*n) : ℂ) = (miuraNLSRight a n)^2 := by
  have him := miuraNLSEndpoints_real a ha n
  have hL : ((miuraNLSLeft a n).re : ℂ) = miuraNLSLeft a n := by
    apply Complex.ext <;> simp only [ofReal_re,ofReal_im,him.1]
  have hR : ((miuraNLSRight a n).re : ℂ) = miuraNLSRight a n := by
    apply Complex.ext <;> simp only [ofReal_re,ofReal_im,him.2]
  constructor
  · rw [miuraHillLabels_left a ha n hn,ofReal_pow,hL]
  · rw [miuraHillLabels_right a ha n hn,ofReal_pow,hR]

theorem miuraHillGap_collapsed_iff (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    miuraHillLabels a ha (2*n-1) = miuraHillLabels a ha (2*n) ↔
      miuraNLSLeft a n = miuraNLSRight a n := by
  rw [miuraHillLabels_left a ha n hn,miuraHillLabels_right a ha n hn]
  have hL := (miuraNLSLeft_pos a ha (show (0 : ℤ) < n by omega)).le
  have hR := hL.trans (miuraNLSEndpoints_within a n)
  rw [sq_eq_sq₀ hL hR]
  constructor
  · intro he
    apply Complex.ext
    · exact he
    · rw [(miuraNLSEndpoints_real a ha n).1,(miuraNLSEndpoints_real a ha n).2]
  · exact congrArg Complex.re

theorem miuraHillGap_square_image (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    (fun x : ℝ => x^2) '' Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re =
      Icc (miuraHillLabels a ha (2*n-1)) (miuraHillLabels a ha (2*n)) := by
  rw [miuraHillLabels_left a ha n hn,miuraHillLabels_right a ha n hn]
  have hL := (miuraNLSLeft_pos a ha (show (0 : ℤ) < n by omega)).le
  have hR := hL.trans (miuraNLSEndpoints_within a n)
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(sq_le_sq₀ hL (hL.trans hx.1)).mpr hx.1,
      (sq_le_sq₀ (hL.trans hx.1) hR).mpr hx.2⟩
  · intro hy
    have hy0 : 0 ≤ y := (sq_nonneg _).trans hy.1
    refine ⟨Real.sqrt y,⟨?_,?_⟩,Real.sq_sqrt hy0⟩
    · exact (sq_le_sq₀ hL (Real.sqrt_nonneg y)).mp ((Real.sq_sqrt hy0).symm ▸ hy.1)
    · exact (sq_le_sq₀ (Real.sqrt_nonneg y) hR).mp ((Real.sq_sqrt hy0).symm ▸ hy.2)

end NLS.MKdV
