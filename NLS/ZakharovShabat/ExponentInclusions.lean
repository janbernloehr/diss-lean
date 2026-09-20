import NLS.SequenceSpaces.ExponentEmbedding
import NLS.ZakharovShabat.PeriodicParity

/-!
# Changing the sequence exponent of potentials and domain vectors

The canonical contractive inclusions keep every raw Fourier coefficient.
They commute with the original domain inclusion and preserve both parities.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The coefficient-preserving inclusion of potential pairs into a larger exponent. -/
def pairExponentInclusion (h : p ≤ q) : PairSpace p →L[ℂ] PairSpace q :=
  (Coeff.exponentInclusion h).prodMap (Coeff.exponentInclusion h)

@[simp] theorem pairExponentInclusion_apply (h : p ≤ q) (φ : PairSpace p) :
    pairExponentInclusion h φ = (Coeff.exponentInclusion h φ.1, Coeff.exponentInclusion h φ.2) := rfl

/-- The corresponding inclusion on the original one-derivative domain. -/
def domainExponentInclusion (h : p ≤ q) : Domain p →L[ℂ] Domain q :=
  (WeightedCoeff.exponentInclusion (Weight.sobolev 1) h).prodMap
    (WeightedCoeff.exponentInclusion (Weight.sobolev 1) h)

@[simp] theorem domainExponentInclusion_apply (h : p ≤ q) (a : Domain p) :
    domainExponentInclusion h a =
      (WeightedCoeff.exponentInclusion (Weight.sobolev 1) h a.1,
       WeightedCoeff.exponentInclusion (Weight.sobolev 1) h a.2) := rfl

theorem pairExponentInclusion_injective (h : p ≤ q) : Function.Injective (pairExponentInclusion h) := by
  intro a b hab
  exact Prod.ext (Coeff.exponentInclusion_injective h (congrArg Prod.fst hab))
    (Coeff.exponentInclusion_injective h (congrArg Prod.snd hab))

theorem domainExponentInclusion_injective (h : p ≤ q) : Function.Injective (domainExponentInclusion h) := by
  intro a b hab
  exact Prod.ext (WeightedCoeff.exponentInclusion_injective _ h (congrArg Prod.fst hab))
    (WeightedCoeff.exponentInclusion_injective _ h (congrArg Prod.snd hab))

theorem norm_pairExponentInclusion_le (h : p ≤ q) (φ : PairSpace p) :
    ‖pairExponentInclusion h φ‖ ≤ ‖φ‖ :=
  max_le_max (Coeff.norm_exponentInclusion_le h φ.1) (Coeff.norm_exponentInclusion_le h φ.2)

theorem norm_domainExponentInclusion_le (h : p ≤ q) (a : Domain p) :
    ‖domainExponentInclusion h a‖ ≤ ‖a‖ :=
  max_le_max (WeightedCoeff.norm_exponentInclusion_le _ h a.1)
    (WeightedCoeff.norm_exponentInclusion_le _ h a.2)

@[simp] theorem domainInclusion_domainExponentInclusion (h : p ≤ q) (a : Domain p) :
    domainInclusion (domainExponentInclusion h a) = pairExponentInclusion h (domainInclusion a) := by
  apply Prod.ext <;> ext n <;> simp

@[simp] theorem pairExponentInclusion_trans [Fact (1 ≤ r)] (hpq : p ≤ q) (hqr : q ≤ r)
    (φ : PairSpace p) : pairExponentInclusion hqr (pairExponentInclusion hpq φ) =
      pairExponentInclusion (hpq.trans hqr) φ := by
  simp only [pairExponentInclusion_apply, Coeff.exponentInclusion_trans]

@[simp] theorem domainExponentInclusion_trans [Fact (1 ≤ r)] (hpq : p ≤ q) (hqr : q ≤ r)
    (a : Domain p) : domainExponentInclusion hqr (domainExponentInclusion hpq a) =
      domainExponentInclusion (hpq.trans hqr) a := by
  simp only [domainExponentInclusion_apply, WeightedCoeff.exponentInclusion_trans]

/-- Changing the exponent neither introduces nor removes Fourier parity membership. -/
@[simp] theorem pairExponentInclusion_mem_parity_iff (h : p ≤ q) (φ : PairSpace p) (k : ℤ) :
    pairExponentInclusion h φ ∈ pairParitySubspace k ↔ φ ∈ pairParitySubspace k := by
  simp only [mem_pairParitySubspace, Coeff.mem_paritySubspace, pairExponentInclusion_apply,
    Coeff.exponentInclusion_apply]

@[simp] theorem domainExponentInclusion_mem_parity_iff (h : p ≤ q) (a : Domain p) (k : ℤ) :
    domainExponentInclusion h a ∈ domainParitySubspace k ↔ a ∈ domainParitySubspace k := by
  rw [mem_domainParitySubspace, domainInclusion_domainExponentInclusion,
    pairExponentInclusion_mem_parity_iff, mem_domainParitySubspace]

end NLS.ZakharovShabat
