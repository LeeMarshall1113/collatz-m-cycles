import Collatz.MCycle110Certs83

/-!
# Certificates of the listed shapes of `data110`, chunks 332..335
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_332 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_332 = true := by
  decide +kernel

theorem certs110_333 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_333 = true := by
  decide +kernel

theorem certs110_334 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_334 = true := by
  decide +kernel

theorem certs110_335 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_335 = true := by
  decide +kernel

end Collatz
