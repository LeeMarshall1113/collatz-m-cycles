import Collatz.MCycle110Certs80

/-!
# Certificates of the listed shapes of `data110`, chunks 320..323
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_320 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_320 = true := by
  decide +kernel

theorem certs110_321 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_321 = true := by
  decide +kernel

theorem certs110_322 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_322 = true := by
  decide +kernel

theorem certs110_323 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_323 = true := by
  decide +kernel

end Collatz
