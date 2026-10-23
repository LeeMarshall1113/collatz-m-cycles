import Collatz.MCycle110Certs74

/-!
# Certificates of the listed shapes of `data110`, chunks 296..299
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_296 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_296 = true := by
  decide +kernel

theorem certs110_297 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_297 = true := by
  decide +kernel

theorem certs110_298 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_298 = true := by
  decide +kernel

theorem certs110_299 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_299 = true := by
  decide +kernel

end Collatz
