import Collatz.MCycle110Certs51

/-!
# Certificates of the listed shapes of `data110`, chunks 204..207
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_204 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_204 = true := by
  decide +kernel

theorem certs110_205 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_205 = true := by
  decide +kernel

theorem certs110_206 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_206 = true := by
  decide +kernel

theorem certs110_207 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_207 = true := by
  decide +kernel

end Collatz
