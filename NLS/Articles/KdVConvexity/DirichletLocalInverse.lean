import NLS.Articles.KdVConvexity.DirichletLinearizationInverse
import NLS.ComplexAnalysis.AnalyticEquivDerivativeInverse

/-! # A local analytic inverse for the actual Hilbert Dirichlet data

Both components extend analytically to a common complex neighborhood of
all real H^-1 potentials. Their actual free derivative gives an analytic
inverse on open neighborhoods of zero in the mean-zero phase space and
the product of the two Hilbert sequence spaces.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- Actual globally extended energy and norming data, with exact root,
real recovery, normalization and free derivative identities. -/
structure DirichletHilbertCoordinates where
  domain : Set PeriodOneHminusOne
  energy : PeriodOneHminusOne → Coeff 2
  norming : PeriodOneHminusOne → Coeff 2
  isOpen_domain : IsOpen domain
  real_mem : {q | IsRealPeriodOneHminusOne q} ⊆ domain
  analytic_energy : AnalyticOnNhd ℂ energy domain
  analytic_norming : AnalyticOnNhd ℂ norming domain
  root : ∀ p ∈ domain, ∀ n : ℕ+, hillHminusDirichlet p
    ((freeHillValue (n : ℕ) : ℂ)+(1+(n : ℕ) : ℂ)*energy p (actionIndexEquiv.symm n)) = 0
  energy_recovery : ∀ p (hp : IsRealPeriodOneHminusOne p) (n : ℕ+),
    energy p (actionIndexEquiv.symm n) =
      ((hillHminusDirichletEnergy p hp n : ℂ)-(freeHillValue (n : ℕ) : ℂ))/(1+(n : ℕ) : ℂ)
  norming_recovery : ∀ p (hp : IsRealPeriodOneHminusOne p) (n : ℕ+),
    norming p (actionIndexEquiv.symm n) = (hillHminusDirichletLogNorming p hp n : ℂ)
  energy_zero : energy 0 = 0
  norming_zero : norming 0 = 0
  energy_derivative : HasFDerivAt energy freeNormalizedDirichletLinearization 0
  norming_derivative : HasFDerivAt norming freeDirichletLogNormingLinearization 0

theorem exists_DirichletHilbertCoordinates : Nonempty DirichletHilbertCoordinates := by
  obtain ⟨U,E,hU,hrealE,hE,hroot,hrecE,hzeroE,hdE⟩ :=
    exists_global_analytic_normalized_Dirichlet_energies_with_free_linearization
  obtain ⟨V,K,hV,hrealK,hK,hrecK,hzeroK,hdK⟩ :=
    exists_global_analytic_Dirichlet_log_norming_with_free_linearization
  exact ⟨{
    domain := U ∩ V
    energy := E
    norming := K
    isOpen_domain := hU.inter hV
    real_mem := fun _ hp => ⟨hrealE hp,hrealK hp⟩
    analytic_energy := hE.mono inter_subset_left
    analytic_norming := hK.mono inter_subset_right
    root := fun p hp => hroot p hp.1
    energy_recovery := hrecE
    norming_recovery := hrecK
    energy_zero := hzeroE
    norming_zero := hzeroK
    energy_derivative := hdE
    norming_derivative := hdK }⟩

def DirichletHilbertCoordinates.meanZeroDomain (C : DirichletHilbertCoordinates) :
    Set PeriodOneMeanZeroHminusOne := periodOneMeanZeroInclusion ⁻¹' C.domain

def DirichletHilbertCoordinates.paired (C : DirichletHilbertCoordinates)
    (q : PeriodOneMeanZeroHminusOne) : Coeff 2 × Coeff 2 := (C.energy q.val,C.norming q.val)

theorem DirichletHilbertCoordinates.isOpen_meanZeroDomain (C : DirichletHilbertCoordinates) :
    IsOpen C.meanZeroDomain := C.isOpen_domain.preimage periodOneMeanZeroInclusion.continuous

theorem DirichletHilbertCoordinates.zero_mem (C : DirichletHilbertCoordinates) :
    (0 : PeriodOneMeanZeroHminusOne) ∈ C.meanZeroDomain := by
  apply C.real_mem
  intro k
  simp

theorem DirichletHilbertCoordinates.analytic_paired (C : DirichletHilbertCoordinates) :
    AnalyticOnNhd ℂ C.paired C.meanZeroDomain := by
  intro q hq
  exact ((C.analytic_energy q.val hq).comp (periodOneMeanZeroInclusion.analyticAt q)).prod
    ((C.analytic_norming q.val hq).comp (periodOneMeanZeroInclusion.analyticAt q))

@[simp] theorem DirichletHilbertCoordinates.paired_zero (C : DirichletHilbertCoordinates) :
    C.paired 0 = 0 := by
  change (C.energy 0,C.norming 0) = (0,0)
  rw [C.energy_zero,C.norming_zero]

theorem DirichletHilbertCoordinates.paired_hasFDerivAt_zero (C : DirichletHilbertCoordinates) :
    HasFDerivAt C.paired freeDirichletFourierEquiv.toContinuousLinearMap 0 := by
  have hd := (C.energy_derivative.prodMk C.norming_derivative).comp
    (0 : PeriodOneMeanZeroHminusOne) periodOneMeanZeroInclusion.hasFDerivAt
  exact hd

/-- The actual two-sequence spectral map is an analytic diffeomorphism on
open neighborhoods of zero, retaining the original global recovery data. -/
theorem DirichletHilbertCoordinates.exists_local_analytic_inverse (C : DirichletHilbertCoordinates) :
    ∃ V : Set PeriodOneMeanZeroHminusOne, ∃ W : Set (Coeff 2 × Coeff 2),
      IsOpen V ∧ IsOpen W ∧ 0 ∈ V ∧ 0 ∈ W ∧ V ⊆ C.meanZeroDomain ∧
      C.paired '' V = W ∧ Set.BijOn C.paired V W ∧
      ∃ G : (Coeff 2 × Coeff 2) → PeriodOneMeanZeroHminusOne,
        G 0 = 0 ∧ AnalyticOnNhd ℂ C.paired V ∧ AnalyticOnNhd ℂ G W ∧
        (∀ q ∈ V, G (C.paired q) = q) ∧
        (∀ z ∈ W, G z ∈ V ∧ C.paired (G z) = z) := by
  obtain ⟨V,W,hV,hW,h0V,h0W,hsub,himage,hbij,G,hF,hG,hleft,hright⟩ :=
    NLS.ComplexAnalysis.exists_analytic_inverse_open_sets_of_equiv_derivative
      C.isOpen_meanZeroDomain C.analytic_paired C.zero_mem freeDirichletFourierEquiv
      C.paired_hasFDerivAt_zero
  have hG0 := hleft 0 h0V
  rw [C.paired_zero] at hG0 h0W
  exact ⟨V,W,hV,hW,h0V,h0W,hsub,himage,hbij,G,hG0,hF,hG,hleft,hright⟩

theorem exists_actual_Dirichlet_local_analytic_inverse :
    ∃ C : DirichletHilbertCoordinates,
      ∃ P : OpenPartialHomeomorph PeriodOneMeanZeroHminusOne (Coeff 2 × Coeff 2),
        (P : PeriodOneMeanZeroHminusOne → Coeff 2 × Coeff 2) = C.paired ∧
        0 ∈ P.source ∧ P.source ⊆ C.meanZeroDomain ∧
        AnalyticOnNhd ℂ C.paired P.source ∧ AnalyticOnNhd ℂ P.symm P.target := by
  obtain ⟨C⟩ := exists_DirichletHilbertCoordinates
  exact ⟨C,NLS.ComplexAnalysis.exists_analytic_openPartialHomeomorph_of_equiv_derivative
    C.isOpen_meanZeroDomain C.analytic_paired C.zero_mem freeDirichletFourierEquiv
    C.paired_hasFDerivAt_zero⟩

end NLS.Articles.KdVConvexity
