import NLS.ZakharovShabat.SourceAngularEtaRemainder
import NLS.ZakharovShabat.SourceStandardRootFirstMoment

/-!
# A logarithmic spectral coordinate for the eta model

The coordinate `z - midpoint - standardRoot z` is nonzero off the
periodic gap, including when that gap is collapsed. Its logarithmic
derivative is `i` times the eta model differential. Consequently
exponentiating model integrals can reduce them to endpoint data.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The branch of the Joukowski coordinate matching the canonical
standard root's normalization at infinity. -/
def sourceAngularEtaModelCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  z-sourceStandardRootMidpoint hp hp1 ψ n-sourceStandardRoot hp hp1 ψ n z

theorem sourceAngularEtaModelCoordinate_analyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    AnalyticAt ℂ (sourceAngularEtaModelCoordinate hp hp1 n ψ) z := by
  exact (analyticAt_id.sub analyticAt_const).sub
    (sourceStandardRoot_analyticAt hp hp1 ψ n z hz)

/-- Nonvanishing uses the endpoint polynomial for an open gap and
the exact linear root for a collapsed gap. -/
theorem sourceAngularEtaModelCoordinate_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    sourceAngularEtaModelCoordinate hp hp1 n ψ z ≠ 0 := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let w := sourceStandardRoot hp hp1 ψ n z
  have hτ : τ = (a+b)/2 := rfl
  intro hzero
  change z-τ-w = 0 at hzero
  have hw : w = z-τ := by linear_combination -hzero
  have hsq : w^2 = (a-z)*(b-z) := sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z hz
  rw [hw,hτ] at hsq
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 := by
    change b-a = 0
    apply sq_eq_zero_iff.mp
    linear_combination 4*hsq
  have hlinear : w = τ-z := sourceStandardRoot_of_zeroGap hp hp1 ψ n z hgap
  have hmid : z = τ := by linear_combination (hzero+hlinear)/2
  exact hz (hmid ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)

/-- Multiplication by `i` turns the model into a negative reciprocal
root, the logarithmic derivative of the spectral coordinate. -/
theorem I_mul_sourceAngularEtaModelIntegrand
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (z : ℂ) :
    Complex.I*sourceAngularEtaModelIntegrand hp hp1 n ψ z =
      -(sourceStandardRoot hp hp1 ψ n z)⁻¹ := by
  simp only [sourceAngularEtaModelIntegrand,div_eq_mul_inv,← mul_assoc,I_mul_I,neg_one_mul]

/-- The coordinate solves the scalar logarithmic differential
equation everywhere off the selected periodic gap. -/
theorem hasDerivAt_sourceAngularEtaModelCoordinate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    HasDerivAt (sourceAngularEtaModelCoordinate hp hp1 n ψ)
      ((Complex.I*sourceAngularEtaModelIntegrand hp hp1 n ψ z)*
        sourceAngularEtaModelCoordinate hp hp1 n ψ z) z := by
  have hroot : HasDerivAt (sourceStandardRoot hp hp1 ψ n)
      ((z-sourceStandardRootMidpoint hp hp1 ψ n)/sourceStandardRoot hp hp1 ψ n z) z := by
    rw [← deriv_sourceStandardRoot_off_segment hp hp1 ψ n z hz]
    exact (sourceStandardRoot_analyticAt hp hp1 ψ n z hz).differentiableAt.hasDerivAt
  have h := ((hasDerivAt_id z).sub_const (sourceStandardRootMidpoint hp hp1 ψ n)).sub hroot
  change HasDerivAt (sourceAngularEtaModelCoordinate hp hp1 n ψ)
    (1-(z-sourceStandardRootMidpoint hp hp1 ψ n)/sourceStandardRoot hp hp1 ψ n z) z at h
  rw [I_mul_sourceAngularEtaModelIntegrand]
  convert h using 1
  unfold sourceAngularEtaModelCoordinate
  field_simp [sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hz]
  ring

/-- The canonical standard root is continuous at both endpoints of
an open complex gap. Its principal square-root argument is zero there. -/
theorem sourceStandardRoot_continuousAt_openGap_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (z : ℂ) (hz : z ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    ContinuousAt (sourceStandardRoot hp hp1 ψ n) z := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  have hτ : τ = (a+b)/2 := rfl
  have hmem : z = a ∨ z = b := by simpa only [mem_insert_iff,mem_singleton_iff] using hz
  have hne : τ-z ≠ 0 := by
    intro he
    rcases hmem with rfl | rfl
    · apply hgap
      change a = b
      rw [hτ] at he
      linear_combination -2*he
    · apply hgap
      change a = b
      rw [hτ] at he
      linear_combination 2*he
  let rad : ℂ → ℂ := fun u => 1-(b-a)^2/(4*(τ-u)^2)
  have hrad0 : rad z = 0 := by
    dsimp [rad]
    field_simp [hne]
    rcases hmem with rfl | rfl <;> rw [hτ] <;> ring
  have hrad : ContinuousAt rad z := by
    exact continuousAt_const.sub (continuousAt_const.div
      (continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).pow 2))
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hne)))
  have hsqrt : ContinuousAt Complex.sqrt (rad z) := Complex.continuousAt_sqrt
    (Or.inl (by rw [hrad0]; simp))
  change ContinuousAt (fun u => (τ-u)*Complex.sqrt (rad u)) z
  exact (continuousAt_const.sub continuousAt_id).mul (hsqrt.comp hrad)

/-- Nonzero logarithmic coordinate at either endpoint of an open gap. -/
theorem sourceAngularEtaModelCoordinate_ne_zero_openGap_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (z : ℂ) (hz : z ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    sourceAngularEtaModelCoordinate hp hp1 n ψ z ≠ 0 := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  have hτ : τ = (a+b)/2 := rfl
  have hmem : z = a ∨ z = b := by simpa only [mem_insert_iff,mem_singleton_iff] using hz
  have hne : z ≠ τ := by
    intro he
    rcases hmem with rfl | rfl
    · apply hgap
      change a = b
      rw [hτ] at he
      linear_combination 2*he
    · apply hgap
      change a = b
      rw [hτ] at he
      linear_combination -2*he
  have hroot0 : sourceStandardRoot hp hp1 ψ n z = 0 := by
    apply sq_eq_zero_iff.mp
    rw [sourceStandardRoot_sq_of_ne_midpoint hp hp1 ψ n z hne]
    change (a-z)*(b-z) = 0
    rcases hmem with rfl | rfl <;> simp
  unfold sourceAngularEtaModelCoordinate
  rw [hroot0,sub_zero]
  exact sub_ne_zero.mpr hne

theorem sourceAngularEtaModelCoordinate_continuousAt_openGap_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (z : ℂ) (hz : z ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    ContinuousAt (sourceAngularEtaModelCoordinate hp hp1 n ψ) z :=
  (continuousAt_id.sub continuousAt_const).sub
    (sourceStandardRoot_continuousAt_openGap_endpoint hp hp1 n ψ hgap z hz)

end NLS.ZakharovShabat
