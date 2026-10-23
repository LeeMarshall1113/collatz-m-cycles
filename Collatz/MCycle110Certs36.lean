import Collatz.MCycle110Certs35

/-!
# Certificates of the listed shapes of `data110`, chunks 140..143
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_140 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_140 = true := by
  decide +kernel

theorem certs110_141 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_141 = true := by
  decide +kernel

theorem certs110_142 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_142 = true := by
  decide +kernel

theorem certs110_143 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_143 = true := by
  decide +kernel

end Collatz
