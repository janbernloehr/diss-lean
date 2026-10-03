import NLS.SequenceSpaces.ConvolutionSandwichCoefficientContinuity
import NLS.ZakharovShabat.DoubleResolventEstimates
import NLS.ZakharovShabat.PeriodOneEmbedding

/-! # Double-resolvent continuity under bounded coefficient limits

The two free resolvent factors regularize potential variation enough to
upgrade coefficientwise convergence to operator-norm convergence, even with
summable output. No strong convergence of the potentials is assumed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- Assemble the off-diagonal scalar operators into the raw pair operator. -/
def offDiagonalPairOperatorCLM :
    ((Coeff p →L[ℂ] Coeff 1) × (Coeff p →L[ℂ] Coeff 1)) →L[ℂ]
      (PairSpace p →L[ℂ] PairSpace 1) :=
  (ContinuousLinearMap.prodL ℂ).toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL ℂ (PairSpace p) (Coeff p) (Coeff 1)).flip
      (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))).prodMap
      ((ContinuousLinearMap.compL ℂ (PairSpace p) (Coeff p) (Coeff 1)).flip
        (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))))

@[simp] theorem offDiagonalPairOperatorCLM_apply
    (T : (Coeff p →L[ℂ] Coeff 1) × (Coeff p →L[ℂ] Coeff 1)) (u : PairSpace p) :
    offDiagonalPairOperatorCLM T u = (T.1 u.2, T.2 u.1) := rfl

/-- The existing double free resolvent is exactly the assembled pair of sandwiches. -/
theorem doubleResolvent_eq_offDiagonal_sandwich (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) :
    doubleResolvent hp φ z hz = offDiagonalPairOperatorCLM
      (Coeff.convolutionSandwich (firstFreeInverseSymbol hp z hz) φ.1 (conjugateInverseSymbol p hp z hz),
       Coeff.convolutionSandwich (conjugateInverseSymbol p hp z hz) φ.2 (firstFreeInverseSymbol hp z hz)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact doubleResolvent_apply_eq_sandwich hp φ z hz u

/-- Bounded coefficientwise limits give operator-norm convergence of
`R₀ Φ R₀ : FLᵖ → FL¹`, at every fixed parameter off the free lattice. -/
theorem tendsto_doubleResolvent_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → PairSpace p) (ψ : PairSpace p)
    (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (z : ℂ) (hz : z ∉ freeLattice) :
    Tendsto (fun k => doubleResolvent hp (φ k) z hz) l (𝓝 (doubleResolvent hp ψ z hz)) := by
  have hq : p.conjExponent ≠ ⊤ :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1 |>.ne
  have hb₁ : Bornology.IsBounded (range (fun k => (φ k).1)) := by
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (norm_fst_le (φ k)).trans (hM _ ⟨k, rfl⟩)
  have hb₂ : Bornology.IsBounded (range (fun k => (φ k).2)) := by
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (norm_snd_le (φ k)).trans (hM _ ⟨k, rfl⟩)
  have h₁ := Coeff.tendsto_convolutionSandwich_of_bounded_coefficientwise hq
    (firstFreeInverseSymbol hp z hz) (conjugateInverseSymbol p hp z hz)
    (fun k => (φ k).1) ψ.1 hb₁ ht₁
  have h₂ := Coeff.tendsto_convolutionSandwich_of_bounded_coefficientwise hq
    (conjugateInverseSymbol p hp z hz) (firstFreeInverseSymbol hp z hz)
    (fun k => (φ k).2) ψ.2 hb₂ ht₂
  simp_rw [doubleResolvent_eq_offDiagonal_sandwich]
  exact offDiagonalPairOperatorCLM.continuous.continuousAt.tendsto.comp (h₁.prodMk_nhds h₂)

/-- Period doubling preserves coefficientwise convergence, including the zero odd modes. -/
theorem tendsto_periodDouble_coefficientwise {α : Type*} {l : Filter α}
    (a : α → Coeff p) (b : Coeff p)
    (ht : ∀ n : ℤ, Tendsto (fun k => a k n) l (𝓝 (b n))) :
    ∀ n : ℤ, Tendsto (fun k => Coeff.periodDouble (a k) n) l (𝓝 (Coeff.periodDouble b n)) := by
  intro n
  rcases Int.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simpa only [← two_mul, Coeff.periodDouble_even] using ht j
  · simpa only [← two_mul, Coeff.periodDouble_odd] using (tendsto_const_nhds (x := (0 : ℂ)) :
      Tendsto (fun _ : α => (0 : ℂ)) l (𝓝 0))

/-- The double-resolvent continuity theorem in the dissertation's actual
period-one source coordinates, with no real-type restriction. -/
theorem tendsto_sourceDoubleResolvent_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p)
    (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (z : ℂ) (hz : z ∉ freeLattice) :
    Tendsto (fun k => doubleResolvent hp (periodOnePotential (φ k)) z hz) l
      (𝓝 (doubleResolvent hp (periodOnePotential ψ) z hz)) := by
  have hb' : Bornology.IsBounded (range (fun k => periodOnePotential (φ k))) := by
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (norm_periodOnePotential_le (φ k)).trans (hM _ ⟨k, rfl⟩)
  exact tendsto_doubleResolvent_of_bounded_coefficientwise hp hp1 (fun k => periodOnePotential (φ k)) (periodOnePotential ψ) hb'
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂) z hz

end NLS.ZakharovShabat
