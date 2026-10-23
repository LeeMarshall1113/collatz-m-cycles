import Collatz.MCycle110Certs41

/-!
# Certificates of the listed shapes of `data110`, chunks 164..167
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_164 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_164 = true := by
  decide +kernel

theorem certs110_165 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_165 = true := by
  decide +kernel

theorem certs110_166 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_166 = true := by
  decide +kernel

theorem certs110_167 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_167 = true := by
  decide +kernel

end Collatz
