import NLS.ZakharovShabat.SourceDirichletFinitePrescription
import NLS.ZakharovShabat.SourceHilbertIsospectralConnected
import Mathlib.Topology.Homeomorph.Lemmas

/-! # The actual Hilbert isospectral set in Dirichlet sheet coordinates

Finite terminal prescriptions and compactness realize arbitrary admissible
terminal data, including infinitely many open gaps. The actual continuous
terminal map is bijective and hence a homeomorphism onto the product of
its original algebraic sheets. Those sheets retain the endpoint joining
of their two signs in the inherited complex-coordinate topology.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceDirichletSheetParametrization_factTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- Every collection of admissible terminals is realized by an actual
isospectral Hilbert source, without a finite-gap assumption. -/
theorem exists_isospectral_source_with_terminals
    (φ : realTypeSourceSubmodule 2) (z : ℤ → ℂ × ℂ)
    (hz : ∀ n, z n ∈ sourceDirichletSpectralSheet (by simp) (by norm_num) n φ.val) :
    ∃ ψ : realTypeSourceSubmodule 2,
      ψ ∈ sourceIsospectralSet (by simp) φ ∧
      sourceDirichletTerminalData (by simp) (by norm_num) ψ = z := by
  let C : ℤ → Set (realTypeSourceSubmodule 2) := fun n =>
    {ψ | sourceDirichletTerminalData (by simp) (by norm_num) ψ n = z n}
  have hC (n : ℤ) : IsClosed (C n) :=
    isClosed_eq ((continuous_apply n).comp (continuous_sourceDirichletTerminalData (by simp) (by norm_num))) continuous_const
  have hf (s : Finset ℤ) : (sourceIsospectralSet (by simp) φ ∩ ⋂ n ∈ s, C n).Nonempty := by
    obtain ⟨ψ,hψ,hdata,_⟩ := exists_isospectral_source_with_finite_terminals φ z hz s
    refine ⟨ψ,hψ,?_⟩
    exact mem_iInter.mpr (fun n => mem_iInter.mpr (fun hn => hdata n hn))
  obtain ⟨ψ,hψ,hdata⟩ := (sourceHilbertIsospectralSet_compact_connected φ).1.inter_iInter_nonempty C hC hf
  exact ⟨ψ,hψ,funext (fun n => mem_iInter.mp hdata n)⟩

/-- The actual terminal data, with each coordinate valued in its original fixed sheet. -/
def sourceHilbertDirichletSheetMap (φ : realTypeSourceSubmodule 2)
    (ψ : sourceIsospectralSet (by simp) φ) (n : ℤ) :
    sourceDirichletSpectralSheet (by simp) (by norm_num) n φ.val :=
  ⟨sourceDirichletTerminalData (by simp) (by norm_num) ψ.val n,
    sourceDirichletTerminalData_mem_sheet_of_isospectral (by simp) (by norm_num) φ ψ.val ψ.property n⟩

/-- Continuity holds for the actual terminal map and the inherited sheet topology. -/
theorem continuous_sourceHilbertDirichletSheetMap (φ : realTypeSourceSubmodule 2) :
    Continuous (sourceHilbertDirichletSheetMap φ) := by
  apply continuous_pi
  intro n
  apply Continuous.subtype_mk
  exact (((continuous_apply n).comp (continuous_sourceDirichletTerminalData (by simp) (by norm_num))).comp
    continuous_subtype_val)

/-- The actual terminal map is bijective onto the full product of original sheets. -/
theorem bijective_sourceHilbertDirichletSheetMap (φ : realTypeSourceSubmodule 2) :
    Function.Bijective (sourceHilbertDirichletSheetMap φ) := by
  constructor
  · intro ψ χ he
    apply Subtype.ext
    apply sourceDirichletTerminalData_injOn_isospectralSet (by simp) (by norm_num) φ ψ.property χ.property
    funext n
    exact congrArg Subtype.val (congrFun he n)
  · intro z
    obtain ⟨ψ,hψ,he⟩ := exists_isospectral_source_with_terminals φ (fun n => (z n).val) (fun n => (z n).property)
    refine ⟨⟨ψ,hψ⟩,?_⟩
    funext n
    exact Subtype.ext (congrFun he n)

/-- The actual isospectral Hilbert set is homeomorphic through its Dirichlet
terminal data to the product of its original algebraic spectral sheets. -/
def sourceHilbertDirichletSheetHomeomorph (φ : realTypeSourceSubmodule 2) :
    sourceIsospectralSet (by simp) φ ≃ₜ
      ((n : ℤ) → sourceDirichletSpectralSheet (by simp) (by norm_num) n φ.val) := by
  letI : CompactSpace (sourceIsospectralSet (by simp) φ) :=
    isCompact_iff_compactSpace.mp (sourceHilbertIsospectralSet_compact_connected φ).1
  exact (Equiv.ofBijective (sourceHilbertDirichletSheetMap φ)
    (bijective_sourceHilbertDirichletSheetMap φ)).toHomeomorphOfContinuousClosed
      (continuous_sourceHilbertDirichletSheetMap φ) (continuous_sourceHilbertDirichletSheetMap φ).isClosedMap

end NLS.ZakharovShabat
