import Collatz.MCycle110Certs44

/-!
# Certificates of the listed shapes of `data110`, chunks 176..179
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_176 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_176 = true := by
  decide +kernel

theorem certs110_177 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_177 = true := by
  decide +kernel

theorem certs110_178 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_178 = true := by
  decide +kernel

theorem certs110_179 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_179 = true := by
  decide +kernel

end Collatz
