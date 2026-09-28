import NLS.ZakharovShabat.SourcePsiLocalJacobianBijectivity
import NLS.ZakharovShabat.SourcePsiLocalJacobianInjectivity
import NLS.ZakharovShabat.SourceIsolatingContourGeometry
import NLS.SequenceSpaces.CoefficientDecay

/-!
# The open root-placement domain for the psi equation

The dissertation's deleted-root domain requires each retained root to
lie in its assigned isolating neighborhood; its omitted coordinate can
be filled separately. The source construction uses central discs and
fixed quarter-π tail discs. Although this is an infinite intersection
of coordinate conditions, it is open in `ℓᵖ`:
tail coordinates of a fixed sequence are uniformly small, while an
`ℓᵖ` perturbation controls every coordinate.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Retained-root placement for a chosen source isolating-disc family. -/
def sourcePsiRootPlacementSet
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ) :
    Set (DeletedCoeff p n) :=
  {a | ∀ j : ℤ, j ≠ n →
    displacedRoots (a : Coeff p) j ∈ sourceIsolatingDisc hp hp1 φ N ε j}

/-- For finite exponent, placing every retained root in its assigned
isolating disc defines an open subset of the deleted `ℓᵖ` space. -/
theorem isOpen_sourcePsiRootPlacementSet
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ) :
    IsOpen (sourcePsiRootPlacementSet hp hp1 φ N ε n) := by
  apply Metric.isOpen_iff.mpr
  intro a ha
  obtain ⟨M,hM⟩ := NLS.Coeff.exists_cutoff_norm_apply_lt hp
    (a : Coeff p) (by positivity : 0 < Real.pi / 8)
  let K := max (N+1) M
  let H : Set (DeletedCoeff p n) :=
    {b | ∀ j ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), j ≠ n →
      displacedRoots (b : Coeff p) j ∈
        sourceIsolatingDisc hp hp1 φ N ε j}
  have hcoordOpen (j : ℤ) :
      IsOpen {b : DeletedCoeff p n |
        j ≠ n → displacedRoots (b : Coeff p) j ∈
          sourceIsolatingDisc hp hp1 φ N ε j} := by
    by_cases hjn : j = n
    · simp [hjn]
    · have hc : Continuous (fun b : DeletedCoeff p n =>
          displacedRoots (b : Coeff p) j) := by
        change Continuous (fun b : DeletedCoeff p n =>
          (Real.pi : ℂ) * j + (b : Coeff p) j)
        exact continuous_const.add
          ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p j).continuous.comp
            continuous_subtype_val)
      simpa [hjn, Set.preimage] using
        (isOpen_sourceIsolatingDisc hp hp1 φ N ε j).preimage hc
  have hHopen : IsOpen H := by
    have heq : H = ⋂ j ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        {b : DeletedCoeff p n |
          j ≠ n → displacedRoots (b : Coeff p) j ∈
            sourceIsolatingDisc hp hp1 φ N ε j} := by
      ext b
      simp [H]
    rw [heq]
    exact isOpen_biInter_finset (fun j _ => hcoordOpen j)
  have haH : a ∈ H := by
    intro j _ hjn
    exact ha j hjn
  obtain ⟨δ,hδ,hδball⟩ := Metric.isOpen_iff.mp hHopen a haH
  refine ⟨min δ (Real.pi/8), by positivity,?_⟩
  intro b hb j hjn
  by_cases hj : j.natAbs ≤ K
  · have hbH : b ∈ H :=
      hδball (ball_subset_ball (min_le_left _ _) hb)
    have hjFin : j ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    exact hbH j hjFin hjn
  · have htailN : ¬ j.natAbs ≤ N := by
      dsimp [K] at hj
      omega
    have htailM : M ≤ j.natAbs := by
      dsimp [K] at hj
      omega
    have haSmall : ‖(a : Coeff p) j‖ < Real.pi/8 := hM j htailM
    have hab : ‖b-a‖ < Real.pi/8 := by
      have hdist : ‖b-a‖ < min δ (Real.pi/8) := by
        simpa only [mem_ball, dist_eq_norm] using hb
      exact lt_of_lt_of_le hdist (min_le_right _ _)
    have hcoord : ‖(b : Coeff p) j-(a : Coeff p) j‖ ≤ ‖b-a‖ := by
      have h := lp.norm_apply_le_norm
        (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
          ((b-a : DeletedCoeff p n) : Coeff p) j
      rw [← Submodule.coe_norm] at h
      simpa only [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply] using h
    have hbSmall : ‖(b : Coeff p) j‖ < Real.pi/4 := by
      have htri : ‖(b : Coeff p) j‖ ≤
          ‖(b : Coeff p) j-(a : Coeff p) j‖ + ‖(a : Coeff p) j‖ := by
        calc
          ‖(b : Coeff p) j‖ =
              ‖((b : Coeff p) j-(a : Coeff p) j)+(a : Coeff p) j‖ := by
                congr 1
                ring
          _ ≤ _ := norm_add_le _ _
      linarith
    simp only [sourceIsolatingDisc, if_neg htailN,
      refinedResonantDisk, mem_ball]
    simpa [displacedRoots, dist_eq_norm] using hbSmall

/-- The retained-root condition in the joint source/root parameter
space; the source parameter does not change its assigned discs. -/
def sourcePsiRootPlacementDomain
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ) :
    Set (DeletedCoeff p n × CoeffPair p) :=
  {t | t.1 ∈ sourcePsiRootPlacementSet hp hp1 φ N ε n}

theorem isOpen_sourcePsiRootPlacementDomain
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ) :
    IsOpen (sourcePsiRootPlacementDomain hp hp1 φ N ε n) := by
  exact (isOpen_sourcePsiRootPlacementSet hp hp1 φ N ε n).preimage
    continuous_fst

/-- On the open retained-root domain, the selected Jacobian is
injective at real source and root data. The omitted root is filled
inside its assigned disc during the interpolation proof. -/
theorem exists_local_sourcePsi_selectedJacobian_injective_on_rootPlacement
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        IsOpen (U ∩ sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n) ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U ∩ sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          Function.Injective
            (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,hinj⟩ :=
    exists_local_sourcePsi_selectedJacobian_injective hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,
    hUopen.inter (isOpen_sourcePsiRootPlacementDomain
      hp hp1 φ Niso εiso n),?_⟩
  intro a ψ hmem hreal hroots
  exact hinj a ψ hmem.1 hreal hroots hmem.2

/-- On the open retained-root domain, the selected Jacobian is
bijective at real source and root data. No placement condition is
imposed on the artificial zero-filled omitted coordinate. -/
theorem exists_local_sourcePsi_selectedJacobian_bijective_on_rootPlacement
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        IsOpen (U ∩ sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n) ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U ∩ sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          Function.Bijective
            (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,_,_,_,_,_,hbij⟩ :=
    exists_local_sourcePsi_selectedJacobian_bijective hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,
    hUopen.inter (isOpen_sourcePsiRootPlacementDomain
      hp hp1 φ Niso εiso n),?_⟩
  intro a ψ hmem hreal hroots
  exact hbij a ψ hmem.1 hreal hroots hmem.2

end NLS.ZakharovShabat
