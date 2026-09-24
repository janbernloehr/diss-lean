import NLS.ZakharovShabat.SourceCriticalGapQuotientContinuity
import NLS.ZakharovShabat.SourceCriticalMidpointGapSquaredTail
import NLS.ZakharovShabat.CompleteParityDisplacementBounds

/-!
# The source-local form of Lemma 10.10

The distant critical-point quotient has a uniformly bounded `ℓp` tail.
Continuity of each of the finitely many remaining coefficients supplies
a common central bound near a real-type source. Finite replacement then
gives one bound for the full quotient, whose squared-gap identity holds
at every signed index, including collapsed complex gaps.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual critical squared-gap quotient, as an `ℓp` sequence. -/
def sourceCriticalGapQuotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff p :=
  ⟨canonicalCriticalGapQuotient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ),
    memℓp_canonicalCriticalGapQuotient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ)⟩

@[simp] theorem sourceCriticalGapQuotient_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) :
    sourceCriticalGapQuotient hp hp1 ψ n =
      canonicalCriticalGapQuotient hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n := rfl

/-- Near each real-type source, the actual quotient has one local
`ℓp` norm bound and gives the exact squared-gap critical offset at
all indices. -/
theorem exists_local_uniform_sourceCriticalGapQuotient
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V,
        ‖sourceCriticalGapQuotient hp hp1 ψ‖ ≤ K ∧
          ∀ n : ℤ,
            canonicalCriticalPoints hp hp1
                (periodOnePotential ψ) (periodOnePotential_mem ψ) n -
              canonicalPeriodicMidpoint hp hp1
                (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
              (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
                sourceCriticalGapQuotient hp hp1 ψ n := by
  obtain ⟨N,_,U,hUopen,_,hφU,_,K,hK,htail⟩ :=
    exists_uniform_critical_midpoint_gap_sq_lp hp hp1 (periodOnePotential φ)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨V₀,hV₀open,hφV₀,B,hB,hcentral⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient_finiteBlock hp hp1 φ hφ s
  obtain ⟨W,hWopen,_,hreal,hexact⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  let V : Set (CoeffPair p) :=
    (periodOnePotential ⁻¹' U) ∩ V₀ ∩ W
  have hVopen : IsOpen V :=
    ((hUopen.preimage (periodOnePotential (p := p)).continuous).inter hV₀open).inter hWopen
  have hφV : φ ∈ V := ⟨⟨hφU,hφV₀⟩,hreal hφ⟩
  refine ⟨V,hVopen,hφV,s.card*B+K,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨hψU,hψV₀⟩ := hψ.1
  obtain ⟨a,ha,hatail⟩ := htail (periodOnePotential ψ) hψU (periodOnePotential_mem ψ)
  have hnorm : ‖sourceCriticalGapQuotient hp hp1 ψ‖ ≤ s.card*B+K := by
    apply (NLS.Coeff.norm_le_of_eq_outside_finset
      (sourceCriticalGapQuotient hp hp1 ψ) a s B
      (fun n hn => hcentral ψ hψV₀ n hn) (fun n hn => ?_)).trans
        (add_le_add le_rfl ha)
    exact (hatail n (by simp only [s, Finset.mem_Icc] at hn; omega)).1.symm
  refine ⟨hnorm,?_⟩
  intro n
  simpa only [sourceCriticalGapQuotient_apply] using (hexact ψ hψ.2 n).2

end NLS.ZakharovShabat
