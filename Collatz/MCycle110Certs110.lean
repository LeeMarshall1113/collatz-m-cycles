import Collatz.MCycle110Certs109

/-!
# Certificates of the listed shapes of `data110`, chunks 436..439
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_436 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_436 = true := by
  decide +kernel

theorem certs110_437 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_437 = true := by
  decide +kernel

theorem certs110_438 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_438 = true := by
  decide +kernel

theorem certs110_439 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_439 = true := by
  decide +kernel

end Collatz
