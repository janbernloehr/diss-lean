import NLS.KdV.HillDirichletGapExistence
import NLS.KdV.HillDirichletGapUniqueness

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

def hillDirichletEnergy
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) : ℝ :=
  (exists_hillL2Dirichlet_zero_in_gap q hq hr n hn).choose

theorem hillDirichletEnergy_mem_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    hillDirichletEnergy q hq hr n hn ∈
      Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) :=
  (exists_hillL2Dirichlet_zero_in_gap q hq hr n hn).choose_spec.1

theorem hillDirichletEnergy_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)=0 :=
  (exists_hillL2Dirichlet_zero_in_gap q hq hr n hn).choose_spec.2

theorem hillDirichletEnergy_eq_of_zero_in_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) (x : ℝ)
    (hx : x∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
    (hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) x=0) :
    hillDirichletEnergy q hq hr n hn=x :=
  hillL2Dirichlet_zero_unique_in_gap q hq hr n hn _ x
    (hillDirichletEnergy_mem_gap q hq hr n hn) hx (hillDirichletEnergy_zero q hq hr n hn) hz

end NLS.KdV
