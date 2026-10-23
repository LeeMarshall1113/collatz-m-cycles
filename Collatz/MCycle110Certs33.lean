import Collatz.MCycle110Certs32

/-!
# Certificates of the listed shapes of `data110`, chunks 128..131
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_128 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_128 = true := by
  decide +kernel

theorem certs110_129 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_129 = true := by
  decide +kernel

theorem certs110_130 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_130 = true := by
  decide +kernel

theorem certs110_131 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_131 = true := by
  decide +kernel

end Collatz
