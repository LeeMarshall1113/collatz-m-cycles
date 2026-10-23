import Collatz.MCycle110Certs46

/-!
# Certificates of the listed shapes of `data110`, chunks 184..187
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_184 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_184 = true := by
  decide +kernel

theorem certs110_185 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_185 = true := by
  decide +kernel

theorem certs110_186 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_186 = true := by
  decide +kernel

theorem certs110_187 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_187 = true := by
  decide +kernel

end Collatz
