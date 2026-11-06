import NLS.KdV.HillHminusOneDirichletGapLabels
import NLS.KdV.HillDirichletAnalyticLabels
import NLS.KdV.HillUnitRealSourceUnembed
import Mathlib.Topology.Connected.Clopen

/-! # Intrinsic rough and physical L2 Dirichlet labels agree

The original physical convention stores unit-period potentials at the even
Fourier indices. Sampling those indices gives their literal H^-1 inclusion.
The two actual characteristics agree at every complex energy. Continuity and
local uniqueness of the physical Dirichlet root then identify every labelled
energy along the real segment from zero, including collapsed gaps and means.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

/-- The literal unit-period H^-1 source of an original real physical potential. -/
def hillPhysicalHminusEmbedding (p : RealPeriodOneHillPotential) : PeriodOneRealHminusOne :=
  ⟨periodOneL2Inclusion (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)),
    fun j => by
      simp only [periodOneL2Inclusion_apply,hillUnitSample_apply,
        show 2*(-j) = -(2*j) by ring]
      exact p.property.2 (2*j)⟩

@[simp] theorem hillPhysicalHminusEmbedding_apply (p : RealPeriodOneHillPotential) (j : ℤ) :
    (hillPhysicalHminusEmbedding p).val.val j = SpectralWeight.one.toCoeff p.val (2*j) := by
  simp only [hillPhysicalHminusEmbedding,periodOneL2Inclusion_apply,hillUnitSample_apply]

theorem continuous_hillPhysicalHminusEmbedding : Continuous hillPhysicalHminusEmbedding := by
  apply Continuous.subtype_mk
  exact periodOneL2Inclusion.continuous.comp
    ((Fourier.paritySample (p := 2) 0).continuous.comp
      (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val))

/-- Equality uses the original derivative-one IVP, at all complex energies. -/
theorem hillHminusDirichlet_eq_physical (p : RealPeriodOneHillPotential) (E : ℂ) :
    hillHminusDirichlet (hillPhysicalHminusEmbedding p).val E =
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff p.val) E := by
  change hillHminusDirichlet (periodOneL2Inclusion _) E = _
  rw [hillHminusDirichlet_eq_hillL2,hillPeriodDouble_unitSample _ p.property.1]
  exact hillL2Dirichlet_eq_characteristic _ _

/-- No restriction on the source norm, mean, index, or open-gap locus is needed. -/
theorem hillHminusDirichletEnergy_eq_physical (p : RealPeriodOneHillPotential) (n : ℕ+) :
    hillHminusDirichletEnergy (hillPhysicalHminusEmbedding p).val
        (hillPhysicalHminusEmbedding p).property n =
      hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property := by
  let line (t : ℝ) : RealPeriodOneHillPotential :=
    ⟨(t : ℂ) • p.val,by
      constructor
      · rw [map_smul]
        exact (Coeff.paritySubspace 0).smul_mem _ p.property.1
      · rw [map_smul]
        exact p.property.2.smul_real t⟩
  have hline : Continuous line := by
    apply Continuous.subtype_mk
    exact Complex.continuous_ofReal.smul continuous_const
  let A (t : ℝ) := hillHminusDirichletEnergy (hillPhysicalHminusEmbedding (line t)).val
    (hillPhysicalHminusEmbedding (line t)).property n
  let B (t : ℝ) := hillDirichletEnergy (line t).val (line t).property.1
    (line t).property.2 (n : ℕ) n.property
  have hA : Continuous A := (continuous_hillHminusDirichletEnergy n).comp
    (continuous_hillPhysicalHminusEmbedding.comp hline)
  have hB : Continuous B := (continuous_hillDirichletEnergy (n : ℕ) n.property).comp hline
  have hclosed : IsClosed {t | A t = B t} := isClosed_eq hA hB
  have hopen : IsOpen {t | A t = B t} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hroot : ∀ᶠ s in 𝓝 t,
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (line s).val) (A s) = 0 := by
      apply Filter.Eventually.of_forall
      intro s
      rw [← hillHminusDirichlet_eq_physical]
      exact hillHminusDirichletEnergy_zero _ _ n
    have he := eventually_hillDirichletEnergy_eq_branch_family
      (fun s => (line s).val) (continuous_subtype_val.comp hline)
      (fun s => (line s).property.1) (fun s => (line s).property.2)
      (n : ℕ) n.property t (fun s => (A s : ℂ))
      (Complex.continuous_ofReal.comp hA).continuousAt (by exact_mod_cast ht) hroot
    filter_upwards [he] with s hs
    exact Complex.ofReal_injective hs.symm
  have h0 : A 0 = B 0 := by
    let z : PeriodOneRealHminusOne := ⟨0,by intro j; simp⟩
    have he : hillPhysicalHminusEmbedding (line 0) = z := by
      apply Subtype.ext
      simp [hillPhysicalHminusEmbedding,line,z]
    have ha0 : A 0 = freeHillValue (n : ℕ) := by
      exact (congrArg (fun q : PeriodOneRealHminusOne =>
        hillHminusDirichletEnergy q.val q.property n) he).trans
          (hillHminusDirichletEnergy_zero_potential z.property n)
    have hb0 : B 0 = freeHillValue (n : ℕ) := by
      simp only [B,line,ofReal_zero,zero_smul]
      exact hillDirichletEnergy_zero_potential _ _ _ _
    exact ha0.trans hb0.symm
  have hall := (IsClopen.eq_univ ⟨hclosed,hopen⟩ ⟨0,h0⟩)
  have h1 : A 1 = B 1 := by
    have : (1 : ℝ) ∈ {t | A t = B t} := by rw [hall]; exact mem_univ _
    exact this
  simpa only [A,B,line,ofReal_one,one_smul] using h1

end NLS.KdV
