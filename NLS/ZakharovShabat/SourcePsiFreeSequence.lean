import NLS.ZakharovShabat.SourcePsiCollapsedGapCircle
import NLS.SequenceSpaces.FiniteModification

/-!
# The free-source psi contour as a deleted-coordinate sequence

The quotient estimate from Lemma 10.8 controls all sufficiently
distant free centers. At the finitely many remaining centers we use
the actual quotient error as the majorant. Finite modification
preserves `ℓᵖ`, so the collapsed-gap residue estimate makes the full
psi contour equation a deleted-coordinate sequence at zero source.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every root-displacement sequence has one `ℓᵖ` majorant for the
single-root quotient error at *all* free lattice centers. -/
theorem exists_sourcePsiQuotient_freeCenter_lpMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) :
    ∃ B : Coeff p, ∀ m : ℤ,
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (((Real.pi : ℂ)*m),(a,(0 : CoeffPair p)))-1‖ ≤ ‖B m‖ := by
  obtain ⟨N,ε,hε,V,_,hzero,K,hNK,hmajor⟩ :=
    exists_local_sourcePsiQuotient_lpDiscMajorant hp hp1
      (0 : CoeffPair p) (by simp)
  obtain ⟨B,hB⟩ := hmajor 0 hzero a
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let b : ℤ → ℂ := fun m =>
    if m ∈ s then
      sourceSingleRootQuotientJointProduct hp hp1 m
        (((Real.pi : ℂ)*m),(a,(0 : CoeffPair p)))-1
    else B m
  have hbmem : Memℓp b p := by
    apply NLS.memℓp_of_eq_outside_finset (lp.memℓp B) s
    intro m hm
    simp [b,hm]
  let Bglobal : Coeff p := ⟨b,hbmem⟩
  refine ⟨Bglobal,?_⟩
  intro m
  by_cases hm : m ∈ s
  · simp [Bglobal,b,hm]
  · have hmK : K ≤ m.natAbs := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    have hN : ¬m.natAbs ≤ N := by omega
    have hzdisc : (Real.pi : ℂ)*m ∈
        sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N ε m := by
      have hcenter : (Real.pi : ℂ)*m ∈ refinedResonantDisk m := by
        exact mem_ball_self (by positivity)
      simpa only [sourceIsolatingDisc,if_neg hN] using hcenter
    have htail := hB m hmK ((Real.pi : ℂ)*m) hzdisc
    simpa [Bglobal,b,hm] using htail

/-- At the free source, the complete psi equation for every deleted
root-displacement input is an `ℓᵖ` sequence. -/
theorem memℓp_sourcePsiEquation_freeCircle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : DeletedCoeff p n)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4) :
    Memℓp (fun m : ℤ =>
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
        (0 : CoeffPair p) ((Real.pi : ℂ)*m) R) p := by
  obtain ⟨B,hB⟩ := exists_sourcePsiQuotient_freeCenter_lpMajorant
    hp hp1 (a : Coeff p)
  exact memℓp_sourcePsiEquationCoordinate_freeCircle hp hp1 n a B R
    hR hRquarter (fun m _ => hB m)

/-- The full free-source contour equation takes values in the
omitted-coordinate Banach space, for arbitrary deleted root inputs. -/
theorem exists_deletedCoeff_sourcePsiEquation_freeCircle_unconditional
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : DeletedCoeff p n)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4) :
    ∃ F : DeletedCoeff p n, ∀ m : ℤ,
      (F : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
          (0 : CoeffPair p) ((Real.pi : ℂ)*m) R := by
  obtain ⟨B,hB⟩ := exists_sourcePsiQuotient_freeCenter_lpMajorant
    hp hp1 (a : Coeff p)
  exact exists_deletedCoeff_sourcePsiEquation_freeCircle hp hp1 n a B R
    hR hRquarter (fun m _ => hB m)

/-- The actual sequence-valued psi equation at zero source. The
selected contours all have the same fixed free-centered radius. -/
def sourcePsiFreeEquationSequence
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4) :
    DeletedCoeff p n → DeletedCoeff p n := fun a =>
  ⟨⟨fun m => sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
      (0 : CoeffPair p) ((Real.pi : ℂ)*m) R,
    memℓp_sourcePsiEquation_freeCircle hp hp1 n a R hR hRquarter⟩,
   by
     change sourcePsiEquationCoordinate hp hp1 n n (a : Coeff p)
       (0 : CoeffPair p) ((Real.pi : ℂ)*n) R = 0
     simp [sourcePsiEquationCoordinate]⟩

@[simp] theorem sourcePsiFreeEquationSequence_apply
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4)
    (a : DeletedCoeff p n) :
    ((sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter a :
      DeletedCoeff p n) : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
        (0 : CoeffPair p) ((Real.pi : ℂ)*m) R := rfl

/-- The zero deleted root sequence solves the sequence-valued free
psi equation. -/
theorem sourcePsiFreeEquationSequence_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4) :
    sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter 0 = 0 := by
  have hRπ : R < Real.pi := by nlinarith [Real.pi_pos]
  ext m
  change sourcePsiEquationCoordinate hp hp1 n m (0 : Coeff p)
    (0 : CoeffPair p) ((Real.pi : ℂ)*m) R = 0
  exact sourcePsiEquationCoordinate_zero hp hp1 m n R hR hRπ

end NLS.ZakharovShabat
