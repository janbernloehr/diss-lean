import NLS.ZakharovShabat.SourceFullAbelianCauchySquare
import NLS.ZakharovShabat.SourcePsiLemma12_11

/-! # The moments of Section 20 on specified circles

These are raw positively oriented contour integrals, with no `1/(2*pi)`
factor. The primitive is normalized at the integration gap, while the
numerator index is independent. At order zero the existing normalized
psi periods give exactly `2*pi` times the Kronecker delta.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integrand `F_k^m*psi_n/canonicalRoot`, with independent numerator
roots and source parameters before selecting the normalized psi branch. -/
def sourceAbelianMomentIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n k : ℤ) (m : ℕ) (t : ℂ × (Coeff p × CoeffPair p)) : ℂ :=
  (sourceFullAbelianPrimitive hp hp1 W k (t.1,t.2.2))^m*
    sourcePsiContourIntegrandJoint hp hp1 n t

/-- The raw moment on a specified circle enclosing the selected gap. -/
def sourceAbelianMomentCircle (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n k : ℤ) (m : ℕ) (a : Coeff p) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  ∮ z in C(c,R), sourceAbelianMomentIntegrand hp hp1 W n k m (z,(a,ψ))

/-- Order zero is exactly the raw psi period, regardless of the
primitive domain and normalization index. -/
theorem sourceAbelianMomentCircle_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) :
    sourceAbelianMomentCircle hp hp1 W n k 0 a ψ c R =
      (2*Real.pi:ℂ)*sourcePsiContour hp hp1 n a ψ c R := by
  have hπ : (2*Real.pi:ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  simp only [sourceAbelianMomentCircle,sourceAbelianMomentIntegrand,pow_zero,one_mul,
    sourcePsiContour,← mul_assoc,mul_inv_cancel₀ hπ,one_mul]

/-- Lemma 20.1(i) for the actual normalized psi branch on its isolating
circle family. The factor is `2*pi`, without an extra imaginary unit. -/
theorem SourcePsiNormalizedComplexExtension.exists_momentCircle_zero_periods
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s) (W : Set (CoeffPair p))
    (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ n k : ℤ, sourceAbelianMomentCircle hp hp1 W n k 0 (s n ψ : Coeff p) ψ (c k) (R k) =
        (2*Real.pi:ℂ)*(if k = n then 1 else 0) := by
  obtain ⟨c,R,hfamily,hperiod⟩ := hs.contour_orthogonality ψ hψ
  refine ⟨c,R,hfamily,?_⟩
  intro n k
  rw [sourceAbelianMomentCircle_zero,hperiod n k]

end NLS.ZakharovShabat
