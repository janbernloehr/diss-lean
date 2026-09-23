import NLS.ZakharovShabat.SourcePeriodicPowerSums
import NLS.ZakharovShabat.CanonicalPeriodicDisplacementBounds

/-!
# Locally uniform source midpoint asymptotics

The canonical midpoint displacement is the average of the two canonical
endpoint displacement sequences. Their common local norm and tail bounds
therefore give the midpoint's full ℓp asymptotic, uniformly on a source
neighborhood.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical source midpoint displacement as an actual ℓp sequence. -/
def sourcePeriodicMidpointDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff p :=
  (1/2 : ℂ) •
    (canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) +
      canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))

@[simp] theorem sourcePeriodicMidpointDisplacement_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    sourcePeriodicMidpointDisplacement hp hp1 ψ n =
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n -
        (Real.pi : ℂ)*n := by
  simp only [sourcePeriodicMidpointDisplacement, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lp.coeFn_add, Pi.add_apply, canonicalPeriodicLeftDisplacement_apply,
    canonicalPeriodicRightDisplacement_apply, canonicalPeriodicMidpoint]
  ring

/-- Near any source coefficient pair, the midpoint displacement has a
uniform ℓp norm bound and uniformly small ℓp tails. -/
theorem exists_uniform_small_sourcePeriodicMidpointDisplacement
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ V,
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R ∧
        ∀ M : ℕ, N ≤ M →
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ -
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M)
              (sourcePeriodicMidpointDisplacement hp hp1 ψ)‖ ≤ ε := by
  obtain ⟨N, hN, U, hUopen, _, hφU, _, R, hR, hdata⟩ :=
    exists_uniform_small_canonicalPeriodicDisplacements hp hp1
      (periodOnePotential φ) hε
  let V : Set (CoeffPair p) := periodOnePotential ⁻¹' U
  refine ⟨N, hN, V, hUopen.preimage (periodOnePotential (p := p)).continuous,
    hφU, R, hR, ?_⟩
  intro ψ hψ
  let a := canonicalPeriodicLeftDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let b := canonicalPeriodicRightDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  obtain ⟨ha, hb, htail⟩ := hdata (periodOnePotential ψ) hψ (periodOnePotential_mem ψ)
  have hbound : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R := by
    change ‖(1/2 : ℂ) • (a+b)‖ ≤ R
    rw [norm_smul]
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    have hsum := norm_add_le a b
    nlinarith
  refine ⟨hbound, ?_⟩
  intro M hM
  let s := Finset.Icc (-(M : ℤ)) M
  have heq : sourcePeriodicMidpointDisplacement hp hp1 ψ -
      Coeff.truncate s (sourcePeriodicMidpointDisplacement hp hp1 ψ) =
        (1/2 : ℂ) • ((a-Coeff.truncate s a)+(b-Coeff.truncate s b)) := by
    simp only [sourcePeriodicMidpointDisplacement, Coeff.truncate_smul,
      Coeff.truncate_add]
    module
  rw [heq, norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have hsum := norm_add_le (a-Coeff.truncate s a) (b-Coeff.truncate s b)
  obtain ⟨hta, htb⟩ := htail M hM
  dsimp only [a, b, s] at hta htb ⊢
  nlinarith

end NLS.ZakharovShabat
