import Collatz.MCycle110Certs88

/-!
# Certificates of the listed shapes of `data110`, chunks 352..355
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_352 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_352 = true := by
  decide +kernel

theorem certs110_353 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_353 = true := by
  decide +kernel

theorem certs110_354 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_354 = true := by
  decide +kernel

theorem certs110_355 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_355 = true := by
  decide +kernel

end Collatz
