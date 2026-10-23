import Collatz.MCycle110Certs45

/-!
# Certificates of the listed shapes of `data110`, chunks 180..183
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_180 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_180 = true := by
  decide +kernel

theorem certs110_181 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_181 = true := by
  decide +kernel

theorem certs110_182 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_182 = true := by
  decide +kernel

theorem certs110_183 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_183 = true := by
  decide +kernel

end Collatz
