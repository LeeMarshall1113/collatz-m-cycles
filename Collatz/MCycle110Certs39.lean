import Collatz.MCycle110Certs38

/-!
# Certificates of the listed shapes of `data110`, chunks 152..155
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_152 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_152 = true := by
  decide +kernel

theorem certs110_153 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_153 = true := by
  decide +kernel

theorem certs110_154 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_154 = true := by
  decide +kernel

theorem certs110_155 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_155 = true := by
  decide +kernel

end Collatz
