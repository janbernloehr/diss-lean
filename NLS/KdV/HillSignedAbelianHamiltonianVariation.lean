import NLS.KdV.HillRealActionHamiltonians
import NLS.KdV.HillActionCoordinateBrackets
import NLS.ComplexAnalysis.RealLineConjugateDerivative
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! # Physical negative-mode action-coordinate variation

Actual real affine source curves determine conjugate source derivatives
in real physical directions. This gives the negative-mode action law from
the positive coordinate and the proved real Hamiltonian vector. Genuine
complex differentiable negative-coordinate matching germs are constructed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Physical real-source conjugate agreement determines conjugate complex
source derivatives in every real period-one direction. -/
theorem fderiv_conjugate_of_eventuallyEq_realPotentials_real_direction
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (F G : Coeff 2 → ℂ) (hF : DifferentiableAt ℂ F (SpectralWeight.one.toCoeff q))
    (hG : DifferentiableAt ℂ G (SpectralWeight.one.toCoeff q))
    (he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      F (SpectralWeight.one.toCoeff p.val)=conj (G (SpectralWeight.one.toCoeff p.val)))
    (v : Coeff 2) (hv : v∈Coeff.paritySubspace 0) (hvr : IsRealHillPotential v) :
    (fderiv ℂ F (SpectralWeight.one.toCoeff q)) v=conj ((fderiv ℂ G (SpectralWeight.one.toCoeff q)) v) := by
  let lift := (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm
  have hcoeff (c : Coeff 2) : SpectralWeight.one.toCoeff (lift c)=c := by
    ext k
    rw [SpectralWeight.toCoeff_apply]
    change c k/(1:ℂ)=c k
    exact div_one _
  have hprop (t : ℝ) :
      SpectralWeight.one.toCoeff (q+(t:ℂ) • lift v)∈Coeff.paritySubspace 0 ∧
        IsRealHillPotential (SpectralWeight.one.toCoeff (q+(t:ℂ) • lift v)) := by
    rw [map_add,map_smul,hcoeff]
    constructor
    · exact (Coeff.paritySubspace 0).add_mem hq ((Coeff.paritySubspace 0).smul_mem _ hv)
    · intro k
      simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,map_add,map_mul,conj_ofReal,hr k,hvr k]
  let line : ℝ → RealPeriodOneHillPotential := fun t => ⟨q+(t:ℂ) • lift v,hprop t⟩
  have hc : Continuous line := by
    apply Continuous.subtype_mk
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hline0 : line 0=(⟨q,hq,hr⟩ : RealPeriodOneHillPotential) := by
    apply Subtype.ext
    simp [line]
  have ht : Tendsto line (𝓝 0) (𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) := by
    rw [← hline0]
    exact hc.tendsto 0
  apply fderiv_conjugate_of_real_line_eventuallyEq F G _ v hF hG
  filter_upwards [ht.eventually he] with t hp
  simpa only [line,map_add,map_smul,hcoeff] using hp

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The actual negative coordinate has a genuine complex differentiable
local matching extension, through every closed selected gap as well. -/
theorem exists_hillNegativeAbelianCoordinate_differentiable_extension (n : ℕ) (hn : 1≤n) :
    ∃ H : Coeff 2 → ℂ, DifferentiableAt ℂ H (SpectralWeight.one.toCoeff q) ∧
      H (SpectralWeight.one.toCoeff q)=conj (hillDirichletAbelianCoordinate q hq hr n hn) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        H (SpectralWeight.one.toCoeff p.val)=conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) := by
  obtain ⟨Z,hZ,_hZ0,_hclosed,hZmatch⟩ :=
    exists_hillDirichletAbelianCoordinate_analytic_extension q hq hr h0q h0r n hn
  let H : Coeff 2 → ℂ := fun p => conj (Z (star (Coeff.reflection p)))
  have hreal (p : RealPeriodOneHillPotential) :
      star (SpectralWeight.one.toCoeff p.val)=Coeff.reflection (SpectralWeight.one.toCoeff p.val) := by
    ext k
    change conj ((SpectralWeight.one.toCoeff p.val) k)=(SpectralWeight.one.toCoeff p.val) (-k)
    exact (p.property.2 k).symm
  have hs := hZ.differentiableAt.star_star
  rw [hreal (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)] at hs
  have hR : DifferentiableAt ℂ (fun p : Coeff 2 => Coeff.reflection p) (SpectralWeight.one.toCoeff q) :=
    Coeff.reflection.toContinuousLinearEquiv.differentiableAt
  have hH : DifferentiableAt ℂ H (SpectralWeight.one.toCoeff q) := by
    simpa only [H,Function.comp_def,Complex.star_def] using hs.comp (SpectralWeight.one.toCoeff q) hR
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      H (SpectralWeight.one.toCoeff p.val)=conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) := by
    filter_upwards [hZmatch] with p hp
    have he : star (Coeff.reflection (SpectralWeight.one.toCoeff p.val))=SpectralWeight.one.toCoeff p.val := by
      ext k
      change conj ((SpectralWeight.one.toCoeff p.val) (-k))=(SpectralWeight.one.toCoeff p.val) k
      rw [p.property.2 k,conj_conj]
    dsimp only [H]
    rw [he,hp]
  exact ⟨H,hH,hmatch.self_of_nhds,hmatch⟩

/-- Negative physical coordinates have the opposite infinitesimal action
phase, independently of their matching differentiable complex extension. -/
theorem fderiv_hillNegativeAbelianCoordinate_extension_tracePeriodDirection
    (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn)) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q)) (hillL2TracePeriodDirection q hq hr m)=
      -I*(if m=n then 1 else 0)*conj (hillDirichletAbelianCoordinate q hq hr n hn) := by
  obtain ⟨Z,hZ,_hZ0,_hclosed,hZmatch⟩ :=
    exists_hillDirichletAbelianCoordinate_analytic_extension q hq hr h0q h0r n hn
  have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=conj (Z (SpectralWeight.one.toCoeff p.val)) := by
    filter_upwards [hmatch,hZmatch] with p hp hpZ
    rw [hp,hpZ]
  rw [fderiv_conjugate_of_eventuallyEq_realPotentials_real_direction q hq hr C Z hC hZ.differentiableAt he _
    (hillL2TracePeriodDirection_mem_parity q hq hr m hm) (hillL2TracePeriodDirection_isReal q hq hr m hm),
    fderiv_hillDirichletAbelianCoordinate_extension_tracePeriodDirection q hq hr h0q h0r n m hn hm Z hZ.differentiableAt hZmatch]
  by_cases hmn : m=n <;> simp [hmn,map_mul,conj_I]

/-- The same negative-mode law holds for every actual physical action
Hamiltonian vector, by its proved weak uniqueness. -/
theorem fderiv_hillNegativeAbelianCoordinate_action_hamiltonian
    (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (C B : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hB : DifferentiableAt ℂ B (SpectralWeight.one.toCoeff q))
    (hCmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn))
    (hBmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      B (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 m 0:ℂ))
    (v : Coeff 2) (hv : IsHillHamiltonianDirection (SpectralWeight.one.toCoeff q) B v) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q)) v=
      -I*(if m=n then 1 else 0)*conj (hillDirichletAbelianCoordinate q hq hr n hn) := by
  rw [hv.unique (hillL2TracePeriodDirection_is_action_hamiltonian q hq hr m hm B hB hBmatch)]
  exact fderiv_hillNegativeAbelianCoordinate_extension_tracePeriodDirection q hq hr h0q h0r n m hn hm C hC hCmatch

end NLS.KdV
