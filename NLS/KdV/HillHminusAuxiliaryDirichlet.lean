import NLS.KdV.HminusOneMiuraDirichlet
import NLS.KdV.MiuraL2DirichletAuxiliary

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

/-- Literal auxiliary-to-scalar characteristic normalization at every
complex energy, source and frequency, including zero. -/
theorem auxiliaryDirichlet_eq_mul_hillHminusDirichlet
    (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ)
    (hi : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c)) :
    auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u) z=z*hillHminusDirichlet q (z^2-c) := by
  rw [hillHminusDirichlet_eq_miura_of_shifted_image q u c (z^2-c) hi,
    sub_add_cancel,auxiliaryDirichlet_eq_mul_quasiHillL2Dirichlet]

end NLS.KdV
