import NLS.ZakharovShabat.SourcePeriodicMidpointAsymptotics
import NLS.ZakharovShabat.PeriodicGapSummability

/-!
# Source periodic gap summability

The canonical gap is the difference of the two endpoint displacement
sequences. Its square has half the summability exponent because the
`p/2` power of the squared modulus equals the `p` power of the gap
modulus, also when `p/2 < 1`.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical periodic gap as an actual source ℓp sequence. -/
def sourcePeriodicGapDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff p :=
  canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) -
    canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)

@[simp] theorem sourcePeriodicGapDisplacement_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    sourcePeriodicGapDisplacement hp hp1 ψ n =
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  simp only [sourcePeriodicGapDisplacement, lp.coeFn_sub, Pi.sub_apply,
    canonicalPeriodicLeftDisplacement_apply, canonicalPeriodicRightDisplacement_apply,
    canonicalPeriodicGap]
  ring

/-- The canonical source squared-gap sequence belongs to ℓ^(p/2)
for every finite p greater than one. -/
theorem memℓp_sourcePeriodicSquaredGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    Memℓp (fun n : ℤ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2)
      (p/2) := by
  let g := sourcePeriodicGapDisplacement hp hp1 ψ
  have hpPos : 0 < p.toReal := by
    exact ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hreal : (p/2).toReal = p.toReal/2 := by
    rw [ENNReal.toReal_div]
    norm_num
  have hqPos : 0 < (p/2).toReal := by
    rw [hreal]
    positivity
  apply (memℓp_gen_iff hqPos).2
  have hsum := (lp.memℓp g).summable hpPos
  convert hsum using 1
  funext n
  rw [hreal]
  simpa only [g, sourcePeriodicGapDisplacement_apply] using
    (norm_sq_rpow_half (g n) p.toReal)

end NLS.ZakharovShabat
