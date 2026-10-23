import Collatz.MCycle110Certs48

/-!
# Certificates of the listed shapes of `data110`, chunks 192..195
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_192 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_192 = true := by
  decide +kernel

theorem certs110_193 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_193 = true := by
  decide +kernel

theorem certs110_194 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_194 = true := by
  decide +kernel

theorem certs110_195 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_195 = true := by
  decide +kernel

end Collatz
