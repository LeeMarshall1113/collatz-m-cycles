import Collatz.MCycle110Certs67

/-!
# Certificates of the listed shapes of `data110`, chunks 268..271
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_268 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_268 = true := by
  decide +kernel

theorem certs110_269 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_269 = true := by
  decide +kernel

theorem certs110_270 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_270 = true := by
  decide +kernel

theorem certs110_271 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_271 = true := by
  decide +kernel

end Collatz
