import Collatz.MCycle110Certs54

/-!
# Certificates of the listed shapes of `data110`, chunks 216..219
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_216 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_216 = true := by
  decide +kernel

theorem certs110_217 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_217 = true := by
  decide +kernel

theorem certs110_218 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_218 = true := by
  decide +kernel

theorem certs110_219 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_219 = true := by
  decide +kernel

end Collatz
