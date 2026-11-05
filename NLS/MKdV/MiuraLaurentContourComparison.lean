import NLS.MKdV.MiuraHillPrimitiveEndpoint
import NLS.ZakharovShabat.SourceLaurentActionContour
import NLS.ComplexAnalysis.PiecewiseSquareContour

/-! # The actual Hill/mKdV Laurent action contours under squaring

At every integer level the physical energy integral transforms with its
literal Jacobian 2*z. The normalization is exactly 2*J_(n,k)=I_(n,2k-2).
The actual mKdV action is k=1 and therefore uses the NLS level zero.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraRightFrequencyDomain (a : ScalarDomain 2) : Set ℂ :=
  {z | 0 < z.re ∧ z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sobolevSourceInclusion (a,a))}

def miuraHillActionContour (a : ScalarDomain 2) (k : ℤ) (energyLoop : PiecewiseC1Loop) : ℂ :=
  -(4*(Real.pi : ℂ))⁻¹ * energyLoop.integral (fun μ => μ^(k-2)*canonicalMiuraHillPrimitive a μ)

theorem miuraSquaredContour_inside (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (miuraRightFrequencyDomain a)) : Γ.square.Inside (miuraHillGapComplement a ha) :=
  Γ.inside_square hΓ (fun z hz => (miuraHillGapComplement_sq_iff a ha z hz.1).mpr hz.2)

theorem miuraHill_laurent_contour_square (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (k : ℤ) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (miuraRightFrequencyDomain a)) :
    Γ.square.integral (fun μ => μ^(k-2)*canonicalMiuraHillPrimitive a μ) =
      2*Γ.integral (fun z => z^(2*k-3)*sourceAbelianPrimitive (by simp) (by norm_num)
        (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property z) := by
  rw [Γ.integral_square]
  calc
    _ = Γ.integral (fun z => 2*(z^(2*k-3)*sourceAbelianPrimitive (by simp) (by norm_num)
        (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property z)) := by
      apply Γ.integral_congr hΓ
      intro z hz
      dsimp only
      rw [(canonicalMiuraHillSheets_eq_NLS a ha z hz.1 hz.2).2]
      have hn : z ≠ 0 := by intro he; simpa [he] using hz.1
      have hp : (z^2)^(k-2) = z^(2*(k-2)) := by rw [zpow_mul]; rfl
      rw [hp]
      have hex : (1 : ℤ)+2*(k-2) = 2*k-3 := by ring
      have hpow : z*z^(2*(k-2)) = z^(2*k-3) := by
        calc
          _ = z^(1 : ℤ)*z^(2*(k-2)) := by rw [zpow_one]
          _ = z^((1 : ℤ)+2*(k-2)) := (zpow_add₀ hn _ _).symm
          _ = _ := congrArg (fun j : ℤ => z^j) hex
      calc
        _ = 2*(z*z^(2*(k-2)))*sourceAbelianPrimitive (by simp) (by norm_num)
          (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property z := by ring
        _ = _ := by rw [hpow]; ring
    _ = _ := Γ.integral_const_mul 2 _

/-- Lemma 7's exact integer-level normalization for the actual squared
contour and the independently constructed physical Hill primitive. -/
theorem two_mul_miuraHillActionContour (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (k : ℤ) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (miuraRightFrequencyDomain a)) :
    2*miuraHillActionContour a k Γ.square =
      sourceLaurentActionContour (by simp) (by norm_num) (realDiagonalH1Source a ha) (2*k-2) Γ := by
  rw [miuraHillActionContour,miuraHill_laurent_contour_square a ha k Γ hΓ,sourceLaurentActionContour]
  have hex : 2*k-2-1 = 2*k-3 := by ring
  rw [hex]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- The mKdV action uses the inverse-energy weight and the NLS level zero. -/
theorem two_mul_miuraHillActionContour_one (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (miuraRightFrequencyDomain a)) :
    2*miuraHillActionContour a 1 Γ.square =
      sourceLaurentActionContour (by simp) (by norm_num) (realDiagonalH1Source a ha) 0 Γ := by
  simpa only [mul_one,sub_self] using two_mul_miuraHillActionContour a ha 1 Γ hΓ

end NLS.MKdV
